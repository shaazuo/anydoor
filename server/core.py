#!/usr/bin/env python3
"""任意门 —— 每个站点一个独立端口 / 独立子域名 / 一个应用条目

设计前提（已在 fnOS 上验证）：
  * 飞牛给每个应用入口分配独立子域名（<appname>-web.<用户域>），也就是独立源
  * 因此站点看到的就是自己的根路径 /，**不需要任何路径改写**
  * 桌面拼地址时：公网优先用 app_service.full_url，内网用 host:端口
所以这里只需要：一个常驻服务 + N 个透明转发器 + N 个空壳应用条目。
"""
import http.server
import json
import os
import re
import socket
import socketserver
import ssl
import struct
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import zlib

VAR = os.environ.get("TRIM_PKGVAR") or os.path.join(os.path.dirname(os.path.abspath(__file__)), "var")
STATE = os.path.join(VAR, "sites.json")
PKGDIR = os.path.join(VAR, "packages")
WORKDIR = os.path.join(VAR, "build")
ADMIN_PORT = int(os.environ.get("ANYD0R_ADMIN_PORT") or 8999)
ICON_SRC = os.environ.get("ANYD0R_ICON") or ""
TPL = os.environ.get("ANYD0R_TPL") or ""
SSL_CTX = ssl._create_unverified_context()

TEMP_APP = "adtemp"          # 临时通道用的应用名（单段，和站点应用同样的规则）

_lock = threading.Lock()
_sites = {}          # id -> dict
_servers = {}        # id -> Threaded server
_health = {}         # id -> {"ok": bool, "msg": str, "ts": float}
# 临时通道：一个常驻转发器，上游可随时换，不新建应用、不动桌面图标
TEMP = {"id": "temp", "app": TEMP_APP, "name": "临时通道",
        "host": "", "target_port": 0, "scheme": "http", "local_port": 0}


# ---------------- 端口分配 ----------------

def base_port(target_port):
    """按用户要求：80 -> 53080，443 -> 53443，8090 -> 58090"""
    p = int(target_port)
    return 53000 + p if p < 1000 else 50000 + p


def port_free(port):
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    try:
        s.bind(("0.0.0.0", port))
        return True
    except OSError:
        return False
    finally:
        s.close()


def alloc_port(target_port, exclude=()):
    used = {int(v["local_port"]) for k, v in _sites.items() if int(v.get("local_port") or 0)}
    used |= set(int(x) for x in exclude)
    base = base_port(target_port)
    for cand in range(base, base + 200):
        if cand in used:
            continue
        if cand == ADMIN_PORT:
            continue
        if port_free(cand):
            return cand
    raise RuntimeError("端口分配失败：%d 起 200 个端口都不可用" % base)


# ---------------- 站点存储 ----------------

def load_state():
    try:
        with open(STATE) as f:
            d = json.load(f)
        for s in d.get("sites", []):
            _sites[s["id"]] = s
        t = d.get("temp") or {}
        for k in ("host", "target_port", "scheme", "local_port"):
            if t.get(k):
                TEMP[k] = t[k]
    except Exception:
        pass


def save_state():
    os.makedirs(VAR, exist_ok=True)
    tmp = STATE + ".tmp"
    with open(tmp, "w") as f:
        json.dump({"sites": sorted(_sites.values(), key=lambda x: x["id"]),
                   "temp": {k: TEMP.get(k) for k in ("host", "target_port", "scheme", "local_port")}},
                  f, ensure_ascii=False, indent=2)
    os.replace(tmp, STATE)


def slug(text):
    s = re.sub(r"[^a-z0-9]+", "-", (text or "").lower()).strip("-")
    return (s or "site")[:20]


ICON_DIR = os.path.join(VAR, "icons")


def _png_encode(w, h, rgba):
    """最小 PNG 编码器（RGBA8），设备图标普遍只有 32×32，不需要压缩率。"""
    raw = b"".join(b"\x00" + rgba[y * w * 4:(y + 1) * w * 4] for y in range(h))

    def chunk(tag, data):
        return (struct.pack(">I", len(data)) + tag + data +
                struct.pack(">I", zlib.crc32(tag + data) & 0xFFFFFFFF))

    ihdr = struct.pack(">IIBBBBB", w, h, 8, 6, 0, 0, 0)
    return (b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", ihdr) +
            chunk(b"IDAT", zlib.compress(raw, 9)) + chunk(b"IEND", b""))


def _dib_to_png(dib):
    """把 ICO 里的 DIB 像素解成 PNG，支持 8/24/32bpp。
    老设备的 favicon.ico 基本都是这几种，够用了。"""
    try:
        hdr = struct.unpack("<IiiHHIIiiII", dib[:40])
        w, h2, bpp = hdr[1], hdr[2], hdr[4]
        h = abs(h2) // 2 or abs(h2)
        if w <= 0 or h <= 0 or w > 512 or h > 512:
            return None
        off = 40
        palette = []
        if bpp <= 8:
            ncolors = 1 << bpp
            for i in range(ncolors):
                b, g, r, _ = dib[off + i * 4:off + i * 4 + 4]
                palette.append((r, g, b))
            off += ncolors * 4
        stride = ((w * bpp + 31) // 32) * 4
        px = bytearray(w * h * 4)
        for y in range(h):
            row = off + (h - 1 - y) * stride
            for x in range(w):
                if bpp == 32:
                    b, g, r, a = dib[row + x * 4:row + x * 4 + 4]
                elif bpp == 24:
                    b, g, r = dib[row + x * 3:row + x * 3 + 3]
                    a = 255
                elif bpp == 8:
                    idx = dib[row + x]
                    r, g, b = palette[idx] if idx < len(palette) else (0, 0, 0)
                    a = 255
                elif bpp == 4:
                    byte = dib[row + x // 2]
                    idx = (byte >> 4) if x % 2 == 0 else (byte & 0xF)
                    r, g, b = palette[idx] if idx < len(palette) else (0, 0, 0)
                    a = 255
                else:
                    return None
                i = (y * w + x) * 4
                px[i:i + 4] = bytes((r, g, b, a))
        return _png_encode(w, h, bytes(px))
    except Exception:
        return None


def _ico_to_png(data):
    """ICO → PNG：优先取内嵌 PNG，其次解 DIB。取分辨率最大的那一档。"""
    if data[:8] == b"\x89PNG\r\n\x1a\n":
        return data
    if data[:4] != b"\x00\x00\x01\x00":
        return None
    n = struct.unpack("<H", data[4:6])[0]
    best = None
    for i in range(min(n, 16)):
        o = 6 + i * 16
        w = data[o] or 256
        size, offset = struct.unpack("<II", data[o + 8:o + 16])
        chunk = data[offset:offset + size]
        if not chunk:
            continue
        if best is None or w > best[0]:
            best = (w, chunk)
    if not best:
        return None
    chunk = best[1]
    if chunk[:8] == b"\x89PNG\r\n\x1a\n":
        return chunk
    return _dib_to_png(chunk)


def _http_get(url, limit=400000, timeout=8):
    req = urllib.request.Request(url, headers={"User-Agent": "anydoor-icon", "Accept": "*/*"})
    with urllib.request.urlopen(req, timeout=timeout, context=SSL_CTX) as r:
        return r.status, r.headers.get("Content-Type", ""), r.read(limit)



# ---------------- 图标绘制（预置图形 / 文字 / 上传） ----------------

BG_COLORS = ["#1f6feb", "#2fbf71", "#f59e0b", "#ef4444",
             "#8b5cf6", "#0ea5e9", "#64748b", "#111827"]
GLYPHS = ["router", "switch", "nas", "server", "camera", "printer", "shield", "cloud"]
CJK_FONT = "/usr/share/fonts/truetype/droid/DroidSansFallbackFull.ttf"


def _hex_rgb(h):
    h = (h or "").lstrip("#")
    if len(h) == 3:
        h = "".join(c * 2 for c in h)
    try:
        return tuple(int(h[i:i + 2], 16) for i in (0, 2, 4))
    except Exception:
        return (31, 111, 235)


def _new_px(w, h):
    return bytearray(w * h * 4)


def _put(px, w, h, x, y, c):
    if 0 <= x < w and 0 <= y < h:
        i = (y * w + x) * 4
        px[i:i + 4] = bytes((c[0], c[1], c[2], 255))


def _rect(px, w, h, x0, y0, x1, y1, c):
    for y in range(max(0, y0), min(h, y1)):
        for x in range(max(0, x0), min(w, x1)):
            _put(px, w, h, x, y, c)


def _round_rect(px, w, h, x0, y0, x1, y1, r, c):
    for y in range(max(0, y0), min(h, y1)):
        for x in range(max(0, x0), min(w, x1)):
            dx = min(x - x0, x1 - 1 - x)
            dy = min(y - y0, y1 - 1 - y)
            if dx < r and dy < r:
                if (r - dx) ** 2 + (r - dy) ** 2 > r * r:
                    continue
            _put(px, w, h, x, y, c)


def _circle(px, w, h, cx, cy, r, c):
    for y in range(cy - r, cy + r + 1):
        for x in range(cx - r, cx + r + 1):
            if (x - cx) ** 2 + (y - cy) ** 2 <= r * r:
                _put(px, w, h, x, y, c)


def _glyph(px, w, h, name, fg, bg):
    """在 256×256 画布上画一个实心图形，fg 是图形色，bg 用来挖洞。"""
    if name == "router":
        _round_rect(px, w, h, 52, 118, 204, 170, 16, fg)
        _rect(px, w, h, 84, 70, 98, 120, fg)
        _rect(px, w, h, 158, 70, 172, 120, fg)
    elif name == "switch":
        _round_rect(px, w, h, 44, 112, 212, 166, 14, fg)
        for i, x in enumerate((80, 112, 144, 176)):
            _circle(px, w, h, x, 139, 8, bg)
    elif name == "nas":
        _round_rect(px, w, h, 56, 86, 200, 126, 12, fg)
        _round_rect(px, w, h, 56, 138, 200, 178, 12, fg)
        _circle(px, w, h, 78, 106, 7, bg)
        _circle(px, w, h, 78, 158, 7, bg)
    elif name == "server":
        _round_rect(px, w, h, 56, 74, 200, 182, 12, fg)
        _rect(px, w, h, 76, 102, 180, 110, bg)
        _rect(px, w, h, 76, 126, 180, 134, bg)
        _rect(px, w, h, 76, 150, 150, 158, bg)
    elif name == "camera":
        _round_rect(px, w, h, 48, 112, 150, 170, 14, fg)
        _circle(px, w, h, 99, 141, 20, bg)
        _rect(px, w, h, 152, 124, 200, 158, fg)
    elif name == "printer":
        _rect(px, w, h, 84, 66, 172, 104, fg)
        _round_rect(px, w, h, 56, 100, 200, 156, 10, fg)
        _rect(px, w, h, 86, 156, 170, 192, fg)
    elif name == "shield":
        for y in range(64, 200):
            t = (y - 64) / 136.0
            half = int(74 * (1 - t ** 2.2)) + 10
            _rect(px, w, h, 128 - half, y, 128 + half, y + 1, fg)
    elif name == "cloud":
        _circle(px, w, h, 100, 142, 40, fg)
        _circle(px, w, h, 146, 126, 50, fg)
        _circle(px, w, h, 184, 148, 34, fg)
        _rect(px, w, h, 78, 148, 200, 186, fg)


def make_preset_icon(glyph, bg, size=256):
    """预置图标：圆角底色 + 白色图形。圆角外透明，桌面看起来和原生图标一致。"""
    bgc = _hex_rgb(bg)
    fg = (255, 255, 255)
    px = _new_px(size, size)
    _round_rect(px, size, size, 0, 0, size, size, int(size * 0.22), bgc)
    _glyph(px, size, size, glyph if glyph in GLYPHS else "router", fg, bgc)
    return _png_encode(size, size, bytes(px))


def make_char_icon(char, bg, size=256):
    """文字图标：用 ffmpeg 的 drawtext 渲染（NAS 上有 Droid 中文字体），
    这样中文、字母、数字都能画。失败时退回预置图形。"""
    ch = (char or "").strip()[:2]
    if not ch:
        return make_preset_icon("door" if False else "router", bg, size)
    tmp = "/tmp/anydoor_char_icon.png"
    try:
        if os.path.exists(tmp):
            os.remove(tmp)
        r, g, b = _hex_rgb(bg)
        color = "0x%02X%02X%02X" % (r, g, b)
        size_px = int(size * (0.52 if len(ch) > 1 else 0.62))
        vf = ("drawtext=fontfile=%s:text='%s':fontcolor=white:fontsize=%d:"
              "x=(w-text_w)/2:y=(h-text_h)/2" % (CJK_FONT, ch.replace("'", ""), size_px))
        cmd = ["ffmpeg", "-hide_banner", "-loglevel", "error", "-y",
               "-f", "lavfi", "-i", "color=c=%s:s=%dx%d" % (color, size, size),
               "-vf", vf, "-frames:v", "1", tmp]
        subprocess.run(cmd, check=True, capture_output=True, timeout=20)
        with open(tmp, "rb") as f:
            data = f.read()
        if data[:8] == b"\x89PNG\r\n\x1a\n":
            return data
    except Exception as e:
        sys.stderr.write("char icon 失败: %s\n" % e)
    return make_preset_icon("router", bg, size)


def render_icon(app, mode, glyph="router", char="", bg="#1f6feb", data=None):
    """生成并落盘图标。mode: auto / preset / char / upload"""
    os.makedirs(ICON_DIR, exist_ok=True)
    path = os.path.join(ICON_DIR, "%s.png" % app)
    tmp = path + ".tmp"
    if mode == "upload":
        if not data or data[:8] != b"\x89PNG\r\n\x1a\n":
            return None, "只支持 PNG"
        with open(tmp, "wb") as f:
            f.write(data)
    elif mode == "char":
        png = make_char_icon(char, bg)
        with open(tmp, "wb") as f:
            f.write(png)
    else:
        png = make_preset_icon(glyph, bg)
        with open(tmp, "wb") as f:
            f.write(png)
    os.replace(tmp, path)
    os.chmod(path, 0o644)
    return path, ""


def fetch_icon(site):
    """抓站点 favicon 并存成 VAR/icons/<app>.png。返回路径或 None。
    顺序：页面里的 <link rel=icon> → /favicon.ico → /favicon.png → /apple-touch-icon.png"""
    up = _upstream(site)
    if not up:
        return None
    _, _, _, _, origin = up
    base = (site.get("base_path") or "").rstrip("/")
    cands = []
    try:
        _, _, html = _http_get(origin + (base or "") + "/")
        m = re.search(rb"<link[^>]+rel=[\"']?[^\"'>]*icon[^\"'>]*[\"']?[^>]*href=[\"']([^\"']+)",
                      html, re.I)
        if m:
            cands.append(urllib.parse.urljoin(origin + "/", m.group(1).decode("utf-8", "replace")))
    except Exception:
        pass
    for p in ("/favicon.ico", "/favicon.png", "/apple-touch-icon.png"):
        cands.append(origin + p)

    for url in cands:
        try:
            st, ct, body = _http_get(url)
        except Exception:
            continue
        if st != 200 or not body:
            continue
        if "text/html" in ct or body[:5].lower() in (b"<!doc", b"<html"):
            continue
        png = _ico_to_png(body)
        if not png:
            continue
        os.makedirs(ICON_DIR, exist_ok=True)
        path = os.path.join(ICON_DIR, "%s.png" % site["app"])
        tmp = path + ".tmp"
        with open(tmp, "wb") as f:
            f.write(png)
        os.replace(tmp, path)
        os.chmod(path, 0o644)
        sys.stderr.write("icon %s <= %s (%d B)\n" % (site["app"], url, len(png)))
        return path
    sys.stderr.write("icon %s: 未找到可用图标\n" % site["app"])
    return None


def icon_path(appname):
    p = os.path.join(ICON_DIR, "%s.png" % appname)
    return p if os.path.isfile(p) else None


def _with_base(site, path):
    """站点如果挂在子路径下（如 /dist），上游请求要补上这个前缀。
    已经带前缀的绝对路径（/dist/x.js）保持原样，避免 /dist/dist。"""
    base = (site.get("base_path") or "").rstrip("/")
    if not base:
        return path
    p = path if path.startswith("/") else "/" + path
    if p == base or p.startswith(base + "/"):
        return p
    return base + p


def _upstream(site):
    host = (site.get("host") or "").strip()
    if not host:
        return None
    port = int(site.get("target_port") or 80)
    scheme = site.get("scheme") or "http"
    upward = host if ":" in host else "%s:%d" % (host, port)
    return host, port, scheme, upward, "%s://%s" % (scheme, upward)


_logreq = {"on": False}


def reqlog(*parts):
    if _logreq["on"]:
        sys.stderr.write("[req] " + " ".join(str(p) for p in parts) + "\n")


EMPTY_TEMP_PAGE = """<!doctype html><meta charset=utf-8>
<title>任意门 · 临时通道</title>
<style>html,body{height:100%}body{margin:0;background:#f3f3f3;color:#0b0b0c;
font:400 14px/1.6 -apple-system,"SF Pro Text","PingFang SC","Helvetica Neue",Arial,sans-serif;
display:flex;align-items:center;justify-content:center;-webkit-font-smoothing:antialiased}
.box{background:#fff;border:1px solid rgba(11,11,12,.08);border-radius:12px;padding:32px 36px;
text-align:center;max-width:340px;box-shadow:0 1px 2px rgba(11,11,12,.04)}
.mk{width:46px;height:46px;border-radius:13px;background:rgba(0,102,255,.1);color:#0066ff;
display:grid;place-items:center;margin:0 auto 14px}
h1{font-size:15px;font-weight:600;margin:0 0 6px}
p{margin:0;color:rgba(11,11,12,.52);font-size:12.5px;line-height:1.75}
code{font-family:ui-monospace,Menlo,monospace;font-size:12px;background:rgba(11,11,12,.06);
padding:2px 5px;border-radius:4px;color:#0b0b0c}</style>
<div class="box"><div class="mk"><svg width="22" height="22" viewBox="0 0 24 24" fill="none"
stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round">
<path d="M7 21V6.2A2.2 2.2 0 0 1 9.2 4h5.6A2.2 2.2 0 0 1 17 6.2V21"/><path d="M3.5 21h17"/>
<circle cx="13.4" cy="12.6" r="1.05" fill="currentColor" stroke="none"/></svg></div>
<h1>临时通道还没有目标</h1>
<p>去 <code>http://&lt;飞牛地址&gt;:8999</code> 的「临时通道」里填一个地址，这里就会打开它。<br>
想长期用，就把它加成站点。</p></div>
"""


def _clear_page():
    """清本域名下的 cookie / storage / CacheStorage。
    这个页面必须由站点自己的源返回，否则清不到它的数据。"""
    return """<!doctype html><meta charset=utf-8><title>清理中…</title>
<style>html,body{height:100%}body{margin:0;background:#f3f3f3;color:#0b0b0c;
font:400 14px/1.6 -apple-system,"SF Pro Text","PingFang SC","Helvetica Neue",Arial,sans-serif;
display:flex;align-items:center;justify-content:center;-webkit-font-smoothing:antialiased}
.box{background:#fff;border:1px solid rgba(11,11,12,.08);border-radius:12px;padding:26px 34px;
text-align:center;box-shadow:0 1px 2px rgba(11,11,12,.04)}
#msg{font-size:14px;font-weight:500}p{margin:6px 0 0;color:rgba(11,11,12,.52);font-size:12px}</style>
<div class="box"><div id=msg>正在清理本站数据…</div>
<p>cookie、localStorage、sessionStorage、缓存</p></div>
<script>
(async function(){
  var log = [];
  try{ localStorage.clear(); log.push('localStorage'); }catch(e){}
  try{ sessionStorage.clear(); log.push('sessionStorage'); }catch(e){}
  try{ var names = document.cookie.split(';').map(function(s){return s.split('=')[0].trim();}).filter(Boolean);
       names.forEach(function(n){ document.cookie = n + '=; Max-Age=0; path=/'; });
       log.push('cookie×' + names.length); }catch(e){}
  try{ if (window.caches) { var ks = await caches.keys();
       await Promise.all(ks.map(function(k){ return caches.delete(k); })); log.push('cache×' + ks.length); } }catch(e){}
  try{ if (navigator.serviceWorker) { var rs = await navigator.serviceWorker.getRegistrations();
       await Promise.all(rs.map(function(r){ return r.unregister(); })); } }catch(e){}
  document.getElementById('msg').textContent = '已清理：' + (log.join(' · ') || '无可清理项');
})();
</script>
"""


# ---------------- 透明转发 ----------------

def make_handler(site):
    """上游从 site 字典**实时读取**，所以临时通道只要改字典就能换目标。"""

    class H(http.server.BaseHTTPRequestHandler):
        protocol_version = "HTTP/1.1"

        def log_message(self, *a):
            pass

        def do_GET(self):
            self._go()

        do_POST = do_PUT = do_DELETE = do_HEAD = do_PATCH = do_OPTIONS = do_GET

        def _go(self):
            path_only = self.path.split("?")[0]
            if path_only == "/__anydoor_clear":
                body = _clear_page().encode()
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Cache-Control", "no-store")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
                return

            up = _upstream(site)
            if not up:
                body = EMPTY_TEMP_PAGE.encode()
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Cache-Control", "no-store")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
                return
            target_host, target_port, scheme, upward_host, origin = up

            if (self.headers.get("Upgrade") or "").lower() == "websocket":
                return self._ws(target_host, target_port, upward_host)

            length = int(self.headers.get("Content-Length") or 0)
            data = self.rfile.read(length) if length else None
            headers = {}
            for k, v in self.headers.items():
                if k.lower() in ("host", "accept-encoding", "connection", "content-length"):
                    continue
                if k.lower() in ("referer", "origin"):
                    v = origin + "/"
                headers[k] = v
            headers["Accept-Encoding"] = "identity"
            req = urllib.request.Request(origin + _with_base(site, self.path),
                                         data=data, headers=headers, method=self.command)
            try:
                with urllib.request.urlopen(req, timeout=30, context=SSL_CTX) as r:
                    status, hdrs, body = r.status, r.headers, r.read()
            except urllib.error.HTTPError as e:
                status, hdrs, body = e.code, e.headers, e.read()
            except Exception as e:
                sys.stderr.write("[%s] 转发失败 %s: %s\n" % (site.get("id"), self.path, e))
                reqlog(site.get("id"), self.command, self.path, "-> FAIL", e)
                msg = ("任意门：连不上 %s\n%s" % (upward_host, e)).encode()
                self.send_response(502)
                self.send_header("Content-Type", "text/plain; charset=utf-8")
                self.send_header("Content-Length", str(len(msg)))
                self.end_headers()
                self.wfile.write(msg)
                return
            self.send_response(status)
            for k, v in hdrs.items():
                lk = k.lower()
                if lk in ("content-length", "transfer-encoding", "connection",
                          "content-encoding"):
                    continue
                # 目标站的安全策略是「绑定它自己的源」的。
                # 我们把页面搬到了另一个源（内网是 IP:端口，公网是子域名），
                # 原样传出去只会让浏览器拒绝嵌框 / 拒绝加载：
                #   X-Frame-Options: SAMEORIGIN/DENY  → 小窗直接 refused to connect
                #   CSP frame-ancestors               → 同上
                #   CSP upgrade-insecure-requests     → 把我们的 http 子资源升级成 https
                #   HSTS                              → 把策略记到我们域名头上
                if lk in ("x-frame-options", "content-security-policy-report-only",
                          "strict-transport-security", "public-key-pins",
                          "public-key-pins-report-only", "alt-svc"):
                    continue
                if lk == "content-security-policy":
                    v = re.sub(r"(?i)\s*frame-ancestors[^;]*;?", "", v)
                    if not v.strip() or v.strip() == ";":
                        continue
                self.send_header(k, v)
            reqlog(site.get("id"), self.command, self.path, "->", status, len(body))
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            if self.command != "HEAD":
                self.wfile.write(body)

        def _ws(self, target_host, target_port, upward_host):
            """WebSocket：把握手重放给上游，之后双向搬字节"""
            try:
                up = socket.create_connection((target_host.split(":")[0], target_port), timeout=10)
            except Exception as e:
                self.send_error(502, "ws upstream fail: %s" % e)
                return
            lines = ["%s %s HTTP/1.1" % (self.command, _with_base(site, self.path)),
                     "Host: " + upward_host]
            for k, v in self.headers.items():
                if k.lower() in ("host", "proxy-connection"):
                    continue
                lines.append("%s: %s" % (k, v))
            lines.append("Connection: Upgrade")
            up.sendall(("\r\n".join(lines) + "\r\n\r\n").encode())

            def pump(a, b):
                try:
                    while True:
                        chunk = a.recv(65536)
                        if not chunk:
                            break
                        b.sendall(chunk)
                except Exception:
                    pass
                finally:
                    try:
                        b.shutdown(socket.SHUT_WR)
                    except Exception:
                        pass

            t = threading.Thread(target=pump, args=(self.connection, up), daemon=True)
            t.start()
            pump(up, self.connection)
            try:
                up.close()
            except Exception:
                pass
            self.close_connection = True

    return H


class Threaded(socketserver.ThreadingMixIn, http.server.HTTPServer):
    daemon_threads = True
    allow_reuse_address = True


def start_forwarder(site):
    port = int(site["local_port"])
    srv = Threaded(("0.0.0.0", port), make_handler(site))
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    _servers[site["id"]] = srv
    sys.stderr.write("forwarder %s: :%d -> %s://%s:%s\n"
                     % (site["id"], port, site.get("scheme"), site.get("host"), site.get("target_port")))


def stop_forwarder(sid):
    srv = _servers.pop(sid, None)
    if srv:
        try:
            srv.shutdown()
            srv.server_close()
        except Exception:
            pass


# ---------------- 健康探测 ----------------

def probe_site(site, timeout=5):
    up = _upstream(site)
    if not up:
        return False, "未设置目标"
    _, _, scheme, upward, origin = up
    base = (site.get("base_path") or "").rstrip("/")
    url = origin + (base or "") + "/"
    req = urllib.request.Request(url, method="GET",
                                 headers={"User-Agent": "anydoor-probe", "Accept": "*/*"})
    t0 = time.time()
    try:
        with urllib.request.urlopen(req, timeout=timeout, context=SSL_CTX) as r:
            ms = int((time.time() - t0) * 1000)
            return True, "HTTP %d · %dms" % (r.status, ms)
    except urllib.error.HTTPError as e:
        ms = int((time.time() - t0) * 1000)
        # 401/403/404 说明机器活着、只是要登录或路径不对
        return (e.code < 500), "HTTP %d · %dms" % (e.code, ms)
    except Exception as e:
        return False, str(e)[:60]


def _sha(path):
    try:
        import hashlib
        return hashlib.sha256(open(path, "rb").read()).hexdigest()
    except Exception:
        return ""


def fetch_all_icons():
    """抓所有站点图标；只有图标真的变了才重装对应应用（重装 20s/个，不能滥用）。"""
    changed = []
    targets = list(_sites.values()) + ([TEMP] if TEMP.get("local_port") else [])
    for site in targets:
        app = site["app"]
        before = _sha(os.path.join(ICON_DIR, "%s.png" % app))
        try:
            got = fetch_icon(site)
        except Exception as e:
            sys.stderr.write("icon %s 异常: %s\n" % (app, e))
            got = None
        after = _sha(os.path.join(ICON_DIR, "%s.png" % app))
        if got and after and after != before:
            changed.append(site)
    sys.stderr.write("icons: %d 个需要重装\n" % len(changed))
    for site in changed:
        install_app(site)
    sys.stderr.write("icons: done\n")


def probe_all():
    for sid, site in list(_sites.items()):
        try:
            ok, msg = probe_site(site)
        except Exception as e:
            ok, msg = False, str(e)[:60]
        _health[sid] = {"ok": ok, "msg": msg, "ts": time.time()}
    try:
        ok, msg = probe_site(TEMP)
        _health["temp"] = {"ok": ok, "msg": msg, "ts": time.time()}
    except Exception:
        pass


def probe_loop():
    tick = 0
    while True:
        try:
            probe_all()
        except Exception:
            pass
        if tick % 5 == 0:
            try:
                reconcile_full_urls()
            except Exception:
                pass
        tick += 1
        time.sleep(60)


# ---------------- 生成 fnOS 应用条目（空壳，无进程） ----------------

APP_TPL_MAIN = """#!/bin/bash
# 任意门生成：容器/设备的生命周期由外部管理，这里只回应状态
case $1 in
start|stop|status) exit 0 ;;
esac
exit 0
"""


def build_app(site):
    appname = site["app"]
    d = os.path.join(WORKDIR, appname)
    subprocess.run(["rm", "-rf", d], check=False)
    os.makedirs(os.path.join(d, "cmd"), exist_ok=True)
    os.makedirs(os.path.join(d, "config"), exist_ok=True)
    # fnpack 要求一整套 cmd/ 生命周期脚本 + config/，直接复用已验证的模板
    if TPL and os.path.isdir(TPL):
        for sub in ("cmd", "config", "wizard"):
            src = os.path.join(TPL, sub)
            if os.path.isdir(src):
                os.makedirs(os.path.join(d, sub), exist_ok=True)
                subprocess.run(["sh", "-c", "cp -r %s/. %s/" % (src, os.path.join(d, sub))], check=False)
    os.makedirs(os.path.join(d, "app", "ui", "images"), exist_ok=True)
    with open(os.path.join(d, "manifest"), "w") as f:
        f.write("""appname               = %s
version               = 1.0.0
display_name          = %s
desc                  = 由任意门代理的内网页面 %s
arch                  = x86_64
platform              = all
source                = thirdparty
maintainer            = anydoor
distributor           = anydoor
os_min_version        = 0.9.0
install_type          = root
desktop_uidir         = ui
desktop_applaunchname = %s.Web
""" % (appname, site["name"], site.get("host") or "（临时通道）", appname))
    with open(os.path.join(d, "config", "privilege"), "w") as f:
        f.write('{\n    "defaults":\n    {\n        "run-as": "package"\n    }\n}\n')
    with open(os.path.join(d, "config", "resource"), "w") as f:
        f.write('{\n  "data-share": {\n    "shares": []\n  }\n}\n')
    with open(os.path.join(d, "cmd", "main"), "w") as f:
        f.write(APP_TPL_MAIN)
    os.chmod(os.path.join(d, "cmd", "main"), 0o755)
    with open(os.path.join(d, "app", "ui", "config"), "w") as f:
        entry = {
            "title": site["name"], "icon": "images/icon_256.png",
            "type": "iframe", "protocol": "http",
            "port": str(site["local_port"]), "url": "/", "allUsers": True}
        pu = public_url(appname)
        if pu:
            entry["fullUrl"] = pu
        json.dump({".url": {appname + ".Web": entry}}, f, ensure_ascii=False, indent=2)
    src_icon = icon_path(appname) or ICON_SRC
    if src_icon and os.path.isfile(src_icon):
        subprocess.run(["cp", src_icon, os.path.join(d, "app", "ui", "images", "icon_256.png")], check=False)
        for root_name in ("ICON_256.PNG", "ICON.PNG"):
            subprocess.run(["cp", src_icon, os.path.join(d, root_name)], check=False)
    subprocess.run(["chmod", "-R", "a+rX", d], check=False)
    r = subprocess.run(["sh", "-c", "cd %s && fnpack build 2>&1 | tail -2" % d],
                       capture_output=True, text=True)
    sys.stderr.write("build %s: %s\n" % (appname, (r.stdout or "").strip()))
    return os.path.join(d, appname + ".fpk")


def _sql_lit(v):
    return "'" + str(v).replace("'", "''") + "'"


def svc(appname):
    """app_service 里的服务名是 <app>.Web —— 传裸应用名会 UPDATE 0 行且不报错。"""
    appname = (appname or "").strip()
    return appname if appname.endswith(".Web") else appname + ".Web"


def set_full_url(service_name, url, tries=15):
    """把外网地址写进 appcenter 的 app_service.full_url。
    桌面在「非内网 IP」访问时优先用它 —— 比等云端分配 fnDomain 可靠。
    注意：应用刚装完时 app_service 的行还没建好，UPDATE 会命中 0 行且不报错，
    所以这里写完要回读校验，不对就重试。"""
    if not url:
        return False
    tmp = "/tmp/anydoor_fullurl.sql"
    chk = "/tmp/anydoor_fullurl_chk.sql"
    ctrl = ('{"show":0,"showRoute":0,"auth":0,"port":1,"path":0,"fullUrl":1,'
            '"accessPerm":"editable","portPerm":"readonly","pathPerm":"editable",'
            '"fullUrlPerm":"editable"}')
    try:
        with open(tmp, "w") as f:
            f.write("update app_service set full_url = %s where service_name = %s;\n"
                    % (_sql_lit(url), _sql_lit(service_name)))
            f.write("update app_service set control = %s where service_name = %s;\n"
                    % (_sql_lit(ctrl), _sql_lit(service_name)))
        with open(chk, "w") as f:
            f.write("select coalesce(full_url, '') from app_service "
                    "where service_name = %s;\n" % _sql_lit(service_name))
        for i in range(tries):
            subprocess.run(["sh", "-c", "su postgres -c 'psql -d appcenter -q -f %s'" % tmp],
                           capture_output=True, text=True, timeout=20)
            r = subprocess.run(["sh", "-c", "su postgres -c 'psql -d appcenter -tAf %s'" % chk],
                               capture_output=True, text=True, timeout=20)
            got = (r.stdout or "").strip()
            if got == url:
                sys.stderr.write("full_url %s -> %s : ok\n" % (service_name, url))
                return True
            time.sleep(2)
        sys.stderr.write("full_url %s -> %s : 未生效(%r)\n" % (service_name, url, got[:60]))
        return False
    except Exception as e:
        sys.stderr.write("full_url %s: %s\n" % (service_name, e))
        return False


def reconcile_full_urls():
    """对账：把 app_service 里所有站点应用的外网地址按规则补上。
    应用重装后 appcenter 会重建行、full_url 变空，靠单次写入不可靠
    （行是异步创建的），所以加一个幂等的定时对账，谁缺就补谁。"""
    if not CONNECT_DOMAIN:
        return
    sql = "/tmp/anydoor_reconcile.sql"
    try:
        with open(sql, "w") as f:
            f.write("update app_service set full_url = "
                    "'https://' || lower(replace(service_name, '.Web', '')) || "
                    "'-web.' || %s || '/' "
                    "where service_name like 'ad%%.Web' "
                    "and (full_url is null or full_url = '' or full_url not like 'https://%%');\n"
                    % _sql_lit(CONNECT_DOMAIN))
        r = subprocess.run(["sh", "-c", "su postgres -c 'psql -d appcenter -q -f %s'" % sql],
                           capture_output=True, text=True, timeout=25)
        sys.stderr.write("reconcile full_url: %s\n"
                         % ("ok" if r.returncode == 0 else (r.stderr or "")[:120]))
    except Exception as e:
        sys.stderr.write("reconcile full_url: %s\n" % e)


# ---------------- 后台任务（给界面看的进度） ----------------

JOBS = {}
_job_seq = [0]


def job_new(title, total=3):
    with _lock:
        _job_seq[0] += 1
        jid = "j%d" % _job_seq[0]
        JOBS[jid] = {"id": jid, "title": title, "state": "running", "step": 0,
                     "total": total, "text": "准备中…", "detail": "", "ts": time.time()}
        # 只留最近 30 条
        if len(JOBS) > 30:
            for k in sorted(JOBS, key=lambda x: JOBS[x]["ts"])[:len(JOBS) - 30]:
                JOBS.pop(k, None)
    return jid


def job_update(jid, **kw):
    if not jid:
        return
    with _lock:
        j = JOBS.get(jid)
        if j:
            j.update(kw)
            j["ts"] = time.time()


def job_step(jid, text, detail=""):
    if not jid:
        return
    with _lock:
        j = JOBS.get(jid)
        if j:
            j["step"] = min(j["step"] + 1, j["total"])
            j["text"] = text
            j["detail"] = detail
            j["ts"] = time.time()


def job_done(jid, ok=True, msg=""):
    job_update(jid, state="done" if ok else "error",
               text=msg or ("完成" if ok else "失败"),
               step=(JOBS.get(jid, {}).get("total") or 0) if ok else JOBS.get(jid, {}).get("step"))


def app_installed(appname):
    try:
        r = subprocess.run(["sh", "-c", "appcenter-cli list 2>/dev/null"], capture_output=True, text=True)
        return appname in (r.stdout or "")
    except Exception:
        return False


def install_app(site, reinstall=True, jid=None):
    """生成并安装桌面空壳应用。jid 给了就把每一步进度写进去，界面轮询显示。"""
    try:
        job_step(jid, "生成应用包", "打包图标与桌面入口")
        fpk = build_app(site)
        if not os.path.isfile(fpk):
            sys.stderr.write("install %s: fpk 未生成\n" % site["app"])
            job_done(jid, False, "打包失败")
            return False
        job_step(jid, "安装到飞牛桌面" if not reinstall else "替换桌面入口",
                 "卸载旧入口并重新安装" if reinstall else "安装中")
        pre = "appcenter-cli uninstall %s >/dev/null 2>&1; sleep 1; " % site["app"] if reinstall else ""
        cmd = pre + "appcenter-cli install-fpk %s -v 1" % fpk
        r = subprocess.run(["sh", "-c", cmd], capture_output=True, text=True)
        out = ((r.stdout or "") + (r.stderr or "")).replace("\r", "\n")
        ok = "Installation complete" in out or "installed" in out.lower()
        sys.stderr.write("install %s: %s\n" % (site["app"], "ok" if ok else out.strip()[-200:]))
        if ok:
            subprocess.run(["sh", "-c", "appcenter-cli start %s >/dev/null 2>&1" % site["app"]],
                           check=False)
            job_step(jid, "写入外网地址", "让公网也能打开")
            try:
                set_full_url(svc(site["app"]), public_url(site["app"]))
            except Exception as e:
                sys.stderr.write("full_url 失败 %s: %s\n" % (site["app"], e))
            job_done(jid, True, "已更新")
        else:
            job_done(jid, False, out.strip()[-60:] or "安装失败")
        return ok
    except Exception as e:
        sys.stderr.write("install %s 异常: %s\n" % (site["app"], e))
        job_done(jid, False, str(e)[:60])
        return False


# ---------------- 管理接口 ----------------

ADMIN_HTML = """<!doctype html>
<html lang="zh-CN">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>任意门</title>
<link rel="icon" href="/favicon.ico">
<style>
:root{
  --bg0:#f3f3f3; --bg1:#fff; --nav:#fafafa;
  --t0:#0b0b0c; --t1:rgba(11,11,12,.72); --t2:rgba(11,11,12,.52); --t3:rgba(11,11,12,.3);
  --border:rgba(11,11,12,.16); --card:rgba(11,11,12,.08); --divider:rgba(11,11,12,.1);
  --fill0:rgba(11,11,12,.04); --fill1:rgba(11,11,12,.06);
  --pri:#0066ff; --pri-h:#005eeb; --pri-l:rgba(0,102,255,.1);
  --ok:#009e61; --warn:#e06c00; --bad:#db382c;
  --shadow-dlg:0 15px 20px rgba(11,11,12,.06),0 8px 16px -6px rgba(3,3,3,.08),1px 12px 42px -4px rgba(10,10,10,.08);
}
*{box-sizing:border-box}
html,body{height:100%;overflow:hidden}
body{margin:0;background:var(--bg0);color:var(--t0);
  font:400 14px/1.5715 -apple-system,"SF Pro Text","PingFang SC","Helvetica Neue",Arial,sans-serif;
  -webkit-font-smoothing:antialiased}
a{color:var(--pri);text-decoration:none}
::selection{background:var(--pri-l)}
.content::-webkit-scrollbar{width:10px}
.content::-webkit-scrollbar-track{background:transparent}
.content::-webkit-scrollbar-thumb{background:rgba(11,11,12,.16);border-radius:8px;
  border:3px solid transparent;background-clip:content-box}
.content::-webkit-scrollbar-thumb:hover{background:rgba(11,11,12,.3);background-clip:content-box;
  border:3px solid transparent}
.side::-webkit-scrollbar{width:6px}
.side::-webkit-scrollbar-thumb{background:rgba(11,11,12,.14);border-radius:6px}

/* ---------- 顶栏 ---------- */
.topbar{position:sticky;top:0;z-index:30;height:57px;display:flex;align-items:center;gap:12px;
  padding:0 22px;background:var(--bg1);border-bottom:1px solid var(--card)}
.mark{width:30px;height:30px;border-radius:9px;background:var(--pri-l);color:var(--pri);
  display:grid;place-items:center;flex:none}
.brand{display:flex;align-items:center;gap:10px;font-size:15px;font-weight:600;letter-spacing:.2px}
.ver{font:500 11px/1 -apple-system,sans-serif;color:var(--pri);background:var(--pri-l);
  padding:4px 7px;border-radius:6px;letter-spacing:.3px}
.top-actions{margin-left:auto;display:flex;align-items:center;gap:8px}

/* ---------- 骨架 ---------- */
.layout{display:flex;height:calc(100vh - 57px);min-height:0}
.side{width:198px;flex:none;background:var(--nav);border-right:1px solid var(--card);
  padding:12px 10px 16px;display:flex;flex-direction:column;height:100%;overflow-y:auto}
.nav-item{display:flex;align-items:center;gap:10px;height:38px;padding:0 10px;border-radius:8px;
  color:var(--t1);cursor:pointer;font-size:14px;margin-bottom:2px;user-select:none;
  transition:background .12s,color .12s}
.nav-item svg{width:17px;height:17px;flex:none;opacity:.85}
.nav-item:hover{background:var(--fill1)}
.nav-item.active{background:var(--pri-l);color:var(--pri);font-weight:500}
.nav-item.active svg{opacity:1}
.nav-item .cnt{margin-left:auto;font-size:12px;color:var(--t2);font-variant-numeric:tabular-nums}
.nav-item.active .cnt{color:var(--pri)}
.side-foot{margin-top:auto;padding:12px 10px 0;font-size:11.5px;color:var(--t3);line-height:1.7}
.content{flex:1;min-width:0;height:100%;overflow-y:auto;overflow-x:hidden;
  padding:26px 30px 60px;overscroll-behavior:contain}
.wrap{max-width:940px;margin:0 auto}
.page-head{margin:0 0 18px}
.page-head h2{margin:0 0 4px;font-size:20px;font-weight:600;letter-spacing:.2px}
.hint{margin:0;color:var(--t2);font-size:12.5px;line-height:1.7}
.hidden{display:none !important}

/* ---------- 按钮 ---------- */
.btn{height:32px;padding:0 14px;border-radius:8px;border:1px solid transparent;background:transparent;
  font:inherit;font-size:13px;color:var(--t0);cursor:pointer;display:inline-flex;align-items:center;
  gap:6px;white-space:nowrap;transition:background .12s,border-color .12s,color .12s}
.btn svg{width:15px;height:15px}
.btn.primary{background:var(--pri);color:#fff}
.btn.primary:hover{background:var(--pri-h)}
.btn.ghost{background:#fff;border-color:var(--border)}
.btn.ghost:hover{background:var(--nav)}
.btn.text{color:var(--pri);padding:0 8px}
.btn.text:hover{background:var(--pri-l)}
.btn.danger{background:#fff;border-color:rgba(219,56,44,.42);color:var(--bad)}
.btn.danger:hover{background:rgba(219,56,44,.06)}
.btn.sm{height:28px;padding:0 10px;font-size:12.5px;border-radius:7px}
.btn[disabled]{opacity:.45;cursor:not-allowed}

/* ---------- 列表 ---------- */
.list{background:var(--bg1);border:1px solid var(--card);border-radius:12px;overflow:hidden}
.row{display:grid;grid-template-columns:40px minmax(0,1fr) 84px 76px 132px;align-items:center;
  gap:14px;padding:11px 16px;border-top:1px solid var(--card);cursor:pointer;
  transition:background .12s}
.row:first-child{border-top:0}
.row:hover{background:var(--nav)}
.row.dim{opacity:.58}
.ric{width:40px;height:40px;border-radius:10px;background:var(--fill0);object-fit:contain;flex:none}
.rmain{min-width:0}
.rname{font-size:14px;font-weight:500;color:var(--t0);white-space:nowrap;overflow:hidden;
  text-overflow:ellipsis}
.rsub{margin-top:2px;font-size:12px;color:var(--t2);white-space:nowrap;overflow:hidden;
  text-overflow:ellipsis;font-family:ui-monospace,SFMono-Regular,Menlo,monospace}
.racts{display:flex;justify-content:flex-end;gap:4px}
.rport{text-align:right}
.pill{display:inline-flex;align-items:center;justify-content:center;height:22px;padding:0 6px;
  border-radius:6px;background:var(--fill0);color:var(--t2);font-size:12px;
  font-family:ui-monospace,SFMono-Regular,Menlo,monospace;font-variant-numeric:tabular-nums}
.chip{display:inline-flex;align-items:center;gap:6px;height:22px;padding:0 8px;border-radius:6px;
  font-size:12px;white-space:nowrap;justify-self:start}
.chip .d{width:5px;height:5px;border-radius:50%;background:currentColor;flex:none}
.chip.ok{background:rgba(0,158,97,.1);color:var(--ok)}
.chip.bad{background:rgba(219,56,44,.08);color:var(--bad)}
.chip.unk{background:var(--fill1);color:var(--t2)}
.chip.off{background:var(--fill1);color:var(--t3)}

/* ---------- 空状态 ---------- */
.empty{background:var(--bg1);border:1px dashed var(--border);border-radius:12px;padding:56px 24px;
  text-align:center}
.empty .eic{width:52px;height:52px;border-radius:14px;background:var(--pri-l);color:var(--pri);
  display:grid;place-items:center;margin:0 auto 14px}
.empty h3{margin:0 0 6px;font-size:15px;font-weight:500}
.empty p{margin:0 0 18px;color:var(--t2);font-size:12.5px}

/* ---------- 卡片 / 设置行 ---------- */
.card{background:var(--bg1);border:1px solid var(--card);border-radius:12px}
.card-pad{padding:18px 20px}
.srow{display:flex;align-items:center;gap:16px;padding:15px 20px;border-top:1px solid var(--card)}
.srow:first-child{border-top:0}
.srow .st{font-size:13.5px;color:var(--t0)}
.srow .sd{margin-top:2px;font-size:12px;color:var(--t2);line-height:1.6}
.srow .sc{margin-left:auto;flex:none;display:flex;gap:8px}
.kv{display:grid;grid-template-columns:112px minmax(0,1fr);gap:10px 16px;font-size:13px}
.kv dt{color:var(--t2)}
.kv dd{margin:0;color:var(--t0);word-break:break-all;font-family:ui-monospace,SFMono-Regular,Menlo,monospace;font-size:12.5px}
.mono{font-family:ui-monospace,SFMono-Regular,Menlo,monospace;font-size:12.5px}
.muted{color:var(--t2);font-size:12px}

/* ---------- 表单 ---------- */
.field{display:flex;flex-direction:column;gap:6px;min-width:0}
.field label{font-size:12.5px;color:var(--t1)}
.inp{height:32px;width:100%;border:1px solid var(--border);border-radius:6px;background:#fff;
  padding:0 10px;font:inherit;font-size:13.5px;color:var(--t0);transition:border-color .12s,box-shadow .12s}
.inp:hover{border-color:var(--t3)}
.inp:focus{outline:none;border-color:var(--pri);box-shadow:0 0 0 3px var(--pri-l)}
.inp[readonly]{background:var(--nav);color:var(--t1)}
.inp.mono{font-family:ui-monospace,SFMono-Regular,Menlo,monospace;font-size:13px}
.seg{display:flex;background:var(--fill1);border-radius:8px;padding:2px;gap:2px;height:32px}
.seg button{flex:1;border:0;border-radius:6px;background:transparent;font:inherit;font-size:13px;
  color:var(--t1);cursor:pointer;transition:background .12s,color .12s,box-shadow .12s}
.seg button.on{background:#fff;color:var(--pri);font-weight:500;box-shadow:0 1px 3px rgba(11,11,12,.1)}
.grid2{display:grid;grid-template-columns:1fr 1fr;gap:12px 14px}

/* ---------- 弹窗 ---------- */
.mask{position:fixed;inset:0;z-index:60;background:rgba(11,11,12,.45);display:flex;
  align-items:center;justify-content:center;padding:24px}
.mask.lvl2{z-index:70}
.dlg{background:#fff;border-radius:12px;width:700px;max-width:100%;max-height:100%;
  display:flex;flex-direction:column;box-shadow:var(--shadow-dlg)}
.dlg.narrow{width:480px}
.dlg-h{display:flex;align-items:center;gap:12px;padding:18px 22px 0}
.dlg-h h3{margin:0;font-size:16px;font-weight:600}
.dlg-h .sub{font-size:12px;color:var(--t2);margin-top:2px}
.dlg-h .x{margin-left:auto;width:30px;height:30px;border-radius:8px;border:0;background:transparent;
  color:var(--t2);cursor:pointer;display:grid;place-items:center;flex:none}
.dlg-h .x:hover{background:var(--fill1);color:var(--t0)}
.dlg-b{padding:6px 22px 4px;overflow:auto}
.dlg-f{display:flex;align-items:center;gap:8px;padding:14px 22px 18px}
.dlg-f .sp{margin-left:auto}
.sec{margin-top:17px}
.sec-t{display:flex;align-items:center;gap:8px;font-size:12.5px;color:var(--t2);margin:0 0 12px}
.sec-t::after{content:"";flex:1;height:1px;background:var(--card)}
.iconline{display:flex;align-items:center;gap:14px}
.ric48{width:52px;height:52px;border-radius:12px;background:var(--fill0);object-fit:contain;flex:none}
.arow{display:flex;align-items:center;gap:12px;padding:8px 0;border-top:1px solid var(--card)}
.arow:first-child{border-top:0;padding-top:0}
.arow .at{font-size:13px;color:var(--t0)}
.arow .ad{font-size:11px;color:var(--t2);margin-top:1px}
.arow .ac{margin-left:auto;display:flex;gap:6px;flex:none}
.deltext{color:var(--bad);padding:0 8px}
.deltext:hover{background:rgba(219,56,44,.07)}
.warnbox{display:flex;gap:8px;padding:10px 12px;border-radius:8px;background:rgba(224,108,0,.07);
  color:#8a4b00;font-size:12px;line-height:1.6}

/* ---------- 图标编辑器 ---------- */
.glyphs{display:grid;grid-template-columns:repeat(4,1fr);gap:8px}
.glyph{height:74px;border:1px solid var(--border);border-radius:8px;background:#fff;cursor:pointer;
  font:inherit;font-size:12px;color:var(--t1);display:flex;flex-direction:column;align-items:center;
  justify-content:center;gap:5px;transition:all .12s}
.glyph img{width:30px;height:30px;border-radius:7px}
.glyph:hover{border-color:var(--t3);background:var(--nav)}
.glyph.on{border-color:var(--pri);background:var(--pri-l);color:var(--pri);font-weight:500}
.sws{display:flex;gap:9px;flex-wrap:wrap}
.sw{width:30px;height:30px;border-radius:8px;border:2px solid #fff;padding:0;cursor:pointer;
  box-shadow:0 0 0 1px var(--card);transition:box-shadow .12s,transform .12s}
.sw:hover{transform:translateY(-1px)}
.sw.on{box-shadow:0 0 0 2px var(--pri)}

/* ---------- 提示 ---------- */
.toast{position:fixed;left:50%;top:70px;transform:translate(-50%,-10px);z-index:90;
  background:#fff;border:1px solid var(--card);border-radius:10px;padding:10px 16px;font-size:13px;
  box-shadow:0 8px 24px rgba(11,11,12,.14);opacity:0;pointer-events:none;
  transition:opacity .18s,transform .18s;max-width:min(560px,92vw);text-align:center}
.toast.show{opacity:1;transform:translate(-50%,0)}
.toast.bad{color:var(--bad)}

/* ---------- 后台任务卡 ---------- */
#jobs{position:fixed;right:22px;bottom:22px;z-index:85;display:flex;flex-direction:column;
  gap:10px;width:326px;max-width:calc(100vw - 32px)}
.job{background:#fff;border:1px solid var(--card);border-radius:12px;padding:13px 15px;
  box-shadow:0 10px 28px rgba(11,11,12,.13);animation:jin .18s ease-out}
@keyframes jin{from{opacity:0;transform:translateY(8px)}to{opacity:1;transform:none}}
.job-h{display:flex;align-items:center;gap:9px;font-size:13px;margin-bottom:10px}
.job-h b{font-weight:500;color:var(--t0);white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.job-h svg{flex:none}
.job-h .jok{color:var(--ok)}
.job-h .jbad{color:var(--bad)}
.job-bar{height:4px;border-radius:4px;background:var(--fill1);overflow:hidden}
.job-bar i{display:block;height:100%;width:0;background:var(--pri);border-radius:4px;
  transition:width .35s ease}
.job.ok .job-bar i{background:var(--ok)}
.job.bad .job-bar i{background:var(--bad)}
.job-t{margin-top:8px;font-size:12px;color:var(--t2);line-height:1.5}
.spin{width:14px;height:14px;border-radius:50%;flex:none;border:2px solid var(--pri-l);
  border-top-color:var(--pri);animation:sp .7s linear infinite}
@keyframes sp{to{transform:rotate(360deg)}}

/* ---------- 小窗（飞牛桌面里跑的时候） ---------- */
@media (max-width:1080px){
  .content{padding:20px 22px 48px}
}
@media (max-width:900px){
  .row{grid-template-columns:36px minmax(0,1fr) auto 116px;gap:10px;padding:10px 14px}
  .row .rport{display:none}
  .ric{width:36px;height:36px;border-radius:9px}
  .side{width:172px}
  .page-head h2{font-size:18px}
  .mask{padding:14px}
}
@media (max-width:760px){
  .layout{flex-direction:column}
  .side{width:auto;flex:none;height:auto;flex-direction:row;align-items:center;border-right:0;
    border-bottom:1px solid var(--card);padding:7px 10px;gap:4px;overflow:visible}
  .content{flex:1;min-height:0;height:auto}
  .side-foot{display:none}
  .nav-item{margin:0;height:32px;padding:0 10px;font-size:13px}
  .nav-item .cnt{display:none}
  .content{padding:16px 14px 40px}
  .row{grid-template-columns:34px minmax(0,1fr) auto 104px;gap:8px}
  .grid2{grid-template-columns:1fr}
  .dlg-h,.dlg-b,.dlg-f{padding-left:16px;padding-right:16px}
}

</style>
</head>
<body>

<svg style="display:none" aria-hidden="true">
  <symbol id="i-door" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round"><path d="M7 21V6.2A2.2 2.2 0 0 1 9.2 4h5.6A2.2 2.2 0 0 1 17 6.2V21"/><path d="M3.5 21h17"/><circle cx="13.4" cy="12.6" r="1.05" fill="currentColor" stroke="none"/></symbol>
  <symbol id="i-grid" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round"><rect x="3.5" y="3.5" width="7" height="7" rx="2"/><rect x="13.5" y="3.5" width="7" height="7" rx="2"/><rect x="3.5" y="13.5" width="7" height="7" rx="2"/><rect x="13.5" y="13.5" width="7" height="7" rx="2"/></symbol>
  <symbol id="i-bolt" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round"><path d="M13.4 2.6 5.6 13.1h5.2l-.9 8.3 8.5-11.2h-5.4z"/></symbol>
  <symbol id="i-slide" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round"><path d="M4 7h11M19 7h1M4 17h5M13 17h7"/><circle cx="17" cy="7" r="2.1"/><circle cx="11" cy="17" r="2.1"/></symbol>
  <symbol id="i-plus" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.9" stroke-linecap="round"><path d="M12 5.5v13M5.5 12h13"/></symbol>
  <symbol id="i-refresh" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round"><path d="M20.3 12a8.3 8.3 0 1 1-2.6-6"/><path d="M20.6 4.2v4.6h-4.6"/></symbol>
  <symbol id="i-close" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round"><path d="M6.6 6.6l10.8 10.8M17.4 6.6 6.6 17.4"/></symbol>
  <symbol id="i-copy" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.6" stroke-linecap="round" stroke-linejoin="round"><rect x="9" y="9" width="11" height="11" rx="2.4"/><path d="M15 5.6A2.4 2.4 0 0 0 12.6 3.2H6.4A2.4 2.4 0 0 0 4 5.6v6.2A2.4 2.4 0 0 0 6.4 14"/></symbol>
</svg>

<header class="topbar">
  <div class="brand"><span class="mark"><svg width="18" height="18"><use href="#i-door"/></svg></span>任意门</div>
  <div class="top-actions">
    <button class="btn ghost sm" onclick="probeAll(this)"><svg><use href="#i-refresh"/></svg>重新探测</button>
    <button class="btn primary sm" onclick="openAdd()"><svg><use href="#i-plus"/></svg>添加站点</button>
  </div>
</header>

<div class="layout">
  <nav class="side">
    <div class="nav-item active" data-p="sites" onclick="go('sites')"><svg><use href="#i-grid"/></svg>站点<span class="cnt" id="cnt">0</span></div>
    <div class="nav-item" data-p="temp" onclick="go('temp')"><svg><use href="#i-bolt"/></svg>临时通道</div>
    <div class="nav-item" data-p="maint" onclick="go('maint')"><svg><use href="#i-slide"/></svg>维护</div>
    <div class="side-foot">每个站点独立端口<br>桌面图标随保存自动生成</div>
  </nav>

  <section class="content">
    <div class="wrap">

      <div class="page" id="page-sites">
        <div class="page-head">
          <h2>站点</h2>
          <p class="hint">点一行打开设置。桌面上的图标由飞牛应用承载，公网走「应用名-web.域名」。</p>
        </div>
        <div id="sitesBox"></div>
      </div>

      <div class="page hidden" id="page-temp">
        <div class="page-head">
          <h2>临时通道</h2>
          <p class="hint">桌面上固定的「临时通道」图标始终指向这里填的地址。只是随手看一眼的机器，不用加成站点。</p>
        </div>
        <div class="card card-pad">
          <div style="display:flex;align-items:center;gap:10px;margin-bottom:14px">
            <div style="font-size:13.5px">当前指向</div>
            <span id="tempChip"></span>
            <div style="margin-left:auto"><button class="btn text sm" onclick="tempClear()">清除目标</button></div>
          </div>
          <div class="mono" id="tempTarget" style="margin-bottom:16px;color:var(--t1)"></div>
          <form onsubmit="return tempSet(event)" style="display:flex;gap:8px">
            <input class="inp mono" id="tempInput" placeholder="10.10.20.99:8080 或 https://10.10.20.10/login" style="flex:1">
            <button class="btn primary">切换过去</button>
          </form>
        </div>
        <div class="card" style="margin-top:14px">
          <div class="srow"><div><div class="st">内网地址</div><div class="sd">在局域网里直接打开</div></div>
            <div class="sc"><span class="mono" id="tempLocal" style="color:var(--t2)"></span><button class="btn ghost sm" onclick="copyEl('tempLocal',this)">复制</button></div></div>
          <div class="srow"><div><div class="st">公网地址</div><div class="sd">在外网经飞牛 Connect 打开</div></div>
            <div class="sc"><span class="mono" id="tempPublic" style="color:var(--t2)"></span><button class="btn ghost sm" onclick="copyEl('tempPublic',this)">复制</button></div></div>
        </div>
      </div>

      <div class="page hidden" id="page-maint">
        <div class="page-head">
          <h2>维护</h2>
          <p class="hint">批量动作都在这里。重建会逐个重装桌面应用，每个约 20 秒。</p>
        </div>
        <div class="card">
          <div class="srow"><div><div class="st">自动抓取图标</div><div class="sd">按站点页面里的 favicon 重抓一遍，抓不到的保留原图标</div></div>
            <div class="sc"><button class="btn ghost sm" onclick="run('/icons','正在抓取图标…')">开始</button></div></div>
          <div class="srow"><div><div class="st">重新探测</div><div class="sd">逐个检查目标是否连得上，刷新列表里的状态</div></div>
            <div class="sc"><button class="btn ghost sm" onclick="run('/probe','正在探测…')">开始</button></div></div>
          <div class="srow"><div><div class="st">重建全部桌面应用</div><div class="sd">改了端口或外网地址没生效时用；期间桌面图标会短暂消失</div></div>
            <div class="sc"><button class="btn ghost sm" onclick="askRebuild()">重建</button></div></div>
          <div class="srow"><div><div class="st">迁移旧版应用名</div><div class="sd">把旧的双段应用名（anydoor.xxx）改成单段，公网才能拿到子域名</div></div>
            <div class="sc"><button class="btn ghost sm" onclick="run('/migrate','正在迁移…')">迁移</button></div></div>
          <div class="srow"><div><div class="st">请求日志</div><div class="sd">打开后转发过程写进 info.log，排查用</div></div>
            <div class="sc"><button class="btn ghost sm" id="logBtn" onclick="toggleLog()">开启</button></div></div>
        </div>
        <div class="card" style="margin-top:14px">
          <div class="card-pad">
            <dl class="kv">
              <dt>站点数量</dt><dd id="mCount">-</dd>
              <dt>Connect 域名</dt><dd id="mDomain">-</dd>
              <dt>公网入口</dt><dd id="mPattern">-</dd>
              <dt>数据目录</dt><dd id="mDir">-</dd>
            </dl>
          </div>
        </div>
      </div>

    </div>
  </section>
</div>

<!-- 添加站点 -->
<div class="mask hidden" id="maskAdd">
  <div class="dlg narrow">
    <div class="dlg-h"><div><h3>添加站点</h3><div class="sub">本地端口会自动分配，冲突自动加一</div></div>
      <button class="x" onclick="hide('maskAdd')"><svg width="16" height="16"><use href="#i-close"/></svg></button></div>
    <div class="dlg-b">
      <div class="grid2" style="margin-top:16px">
        <div class="field"><label>名称</label><input class="inp" id="a_name" placeholder="如 光猫" autocomplete="off"></div>
        <div class="field"><label>地址</label><input class="inp mono" id="a_host" placeholder="192.168.1.1" autocomplete="off"></div>
        <div class="field"><label>端口</label><input class="inp mono" id="a_port" value="80" autocomplete="off"></div>
        <div class="field"><label>协议</label><div class="seg" id="a_seg"><button class="on" data-v="http">http</button><button data-v="https">https</button></div></div>
        <div class="field" style="grid-column:1/-1"><label>路径（可空）</label><input class="inp mono" id="a_base" placeholder="如 /dist、/login，不需要就留空" autocomplete="off"></div>
      </div>
      <div class="warnbox" style="margin-top:16px">保存后会在飞牛桌面生成一个独立图标，首次安装约 20 秒。</div>
    </div>
    <div class="dlg-f"><span class="sp"></span><button class="btn ghost" onclick="hide('maskAdd')">取消</button>
      <button class="btn primary" onclick="addSite()">添加</button></div>
  </div>
</div>

<!-- 站点设置 -->
<div class="mask hidden" id="maskSite">
  <div class="dlg">
    <div class="dlg-h">
      <img class="ric48" id="s_icon" alt="">
      <div style="min-width:0">
        <h3 id="s_title">站点</h3>
        <div class="sub mono" id="s_app"></div>
      </div>
      <span id="s_chip" style="margin-left:6px"></span>
      <button class="x" onclick="hide('maskSite')"><svg width="16" height="16"><use href="#i-close"/></svg></button>
    </div>
    <div class="dlg-b">
      <div class="sec">
        <div class="sec-t">基本设置</div>
        <div class="grid2">
          <div class="field"><label>名称</label><input class="inp" id="s_name"></div>
          <div class="field"><label>地址</label><input class="inp mono" id="s_host"></div>
          <div class="field"><label>目标端口</label><input class="inp mono" id="s_port"></div>
          <div class="field"><label>协议</label><div class="seg" id="s_seg"><button data-v="http">http</button><button data-v="https">https</button></div></div>
          <div class="field"><label>路径（可空）</label><input class="inp mono" id="s_base" placeholder="如 /dist"></div>
          <div class="field"><label>本地端口</label><input class="inp mono" id="s_local"></div>
        </div>
      </div>

      <div class="sec">
        <div class="sec-t">图标</div>
        <div class="iconline">
          <img class="ric48" id="s_icon2" alt="">
          <div style="min-width:0">
            <div style="font-size:13px">桌面图标</div>
            <div class="muted" style="margin-top:2px">自动抓取、预置图形、单字或自己上传</div>
          </div>
          <div style="margin-left:auto;display:flex;gap:8px">
            <button class="btn ghost sm" onclick="iconAuto()">自动抓取</button>
            <button class="btn ghost sm" onclick="openIcon()">更换图标</button>
          </div>
        </div>
      </div>

      <div class="sec">
        <div class="sec-t">访问地址</div>
        <div class="field" style="margin-bottom:12px"><label>公网</label>
          <div style="display:flex;gap:8px">
            <input class="inp mono" id="s_pub" readonly>
            <button class="btn ghost sm" onclick="copyEl('s_pub',this)">复制</button>
            <a class="btn ghost sm" id="s_pubOpen" target="_blank" rel="noopener">打开</a>
          </div>
        </div>
        <div class="field"><label>内网</label>
          <div style="display:flex;gap:8px">
            <input class="inp mono" id="s_loc" readonly>
            <button class="btn ghost sm" onclick="copyEl('s_loc',this)">复制</button>
            <a class="btn ghost sm" id="s_locOpen" target="_blank" rel="noopener">打开</a>
          </div>
        </div>
      </div>

      <div class="sec">
        <div class="sec-t">应用与维护</div>
        <div class="arow"><div><div class="at">重装桌面应用</div><div class="ad">图标不刷新、桌面打不开时用</div></div>
          <div class="ac"><button class="btn ghost sm" onclick="appOp('reinstall')">重装</button></div></div>
        <div class="arow"><div><div class="at">刷新外网地址</div><div class="ad">重新写入飞牛的应用入口地址</div></div>
          <div class="ac"><button class="btn ghost sm" onclick="appOp('refresh')">刷新</button></div></div>
        <div class="arow"><div><div class="at" id="s_toggleT">停用</div><div class="ad">停用会卸载桌面应用，站点数据保留</div></div>
          <div class="ac"><button class="btn ghost sm" id="s_toggleB" onclick="appOp('toggle')">停用</button></div></div>
        <div class="arow"><div><div class="at">清除本站 Cookie</div><div class="ad">登录串味、白屏时用，会退出该站登录</div></div>
          <div class="ac"><a class="btn ghost sm" id="s_clear" target="_blank" rel="noopener">清除</a></div></div>
      </div>
    </div>
    <div class="dlg-f">
      <button class="btn text sm deltext" onclick="askDelete()">删除站点</button>
      <span class="mono muted" id="s_msg" style="margin-left:6px"></span>
      <span class="sp"></span>
      <button class="btn ghost" onclick="hide('maskSite')">取消</button>
      <button class="btn primary" onclick="saveSite()">保存</button>
    </div>
  </div>
</div>

<!-- 图标设置 -->
<div class="mask hidden lvl2" id="maskIcon">
  <div class="dlg narrow" style="width:520px">
    <div class="dlg-h"><div><h3>图标</h3><div class="sub" id="ic_name"></div></div>
      <button class="x" onclick="hide('maskIcon')"><svg width="16" height="16"><use href="#i-close"/></svg></button></div>
    <div class="dlg-b">
      <div class="iconline" style="margin-top:16px">
        <img class="ric48" id="ic_prev" style="width:64px;height:64px" alt="">
        <div style="display:flex;flex-direction:column;gap:6px">
          <button class="btn ghost sm" onclick="applyIcon('auto')">从站点自动抓取</button>
          <label class="btn ghost sm" style="cursor:pointer">上传 PNG<input type="file" accept="image/png" hidden onchange="uploadIcon(this)"></label>
        </div>
        <div class="muted" id="ic_state" style="margin-left:auto;text-align:right;max-width:150px"></div>
      </div>
      <div class="sec">
        <div class="sec-t">预置图形</div>
        <div class="glyphs" id="ic_glyphs"></div>
      </div>
      <div class="sec">
        <div class="sec-t">底色</div>
        <div class="sws" id="ic_sws"></div>
      </div>
      <div class="sec" style="margin-bottom:6px">
        <div class="sec-t">文字图标</div>
        <div style="display:flex;align-items:center;gap:10px">
          <input class="inp" id="ic_char" maxlength="2" placeholder="如 光" style="width:92px;text-align:center">
          <span class="muted">输入 1–2 个字，底色同上，支持中文</span>
        </div>
      </div>
    </div>
    <div class="dlg-f"><span class="muted">保存后会随应用重装刷新到桌面</span><span class="sp"></span>
      <button class="btn primary" onclick="hide('maskIcon')">完成</button></div>
  </div>
</div>

<!-- 通用确认 -->
<div class="mask hidden lvl2" id="maskAsk">
  <div class="dlg narrow" style="width:430px">
    <div class="dlg-h"><div><h3 id="ask_t">确认</h3><div class="sub" id="ask_d"></div></div></div>
    <div class="dlg-f" style="padding-top:22px"><span class="sp"></span>
      <button class="btn ghost" onclick="hide('maskAsk')">取消</button>
      <button class="btn primary" id="ask_ok">确定</button></div>
  </div>
</div>

<div id="jobs"></div>
<div class="toast" id="toast"></div>

<script>
var D = __DATA_JSON__;
var GLYPHS = [["router","路由"],["switch","交换机"],["nas","NAS"],["server","服务器"],
              ["camera","摄像头"],["printer","打印机"],["shield","安全"],["cloud","云"]];
var COLORS = ["#0066ff","#009e61","#e06c00","#db382c","#7c3aed","#0891b2","#64748b","#1f2937"];
var cur = null, glyph = "router", bg = COLORS[0], iconDirty = false, askCb = null;

function $(id){ return document.getElementById(id); }
function esc(s){
  return String(s == null ? "" : s).replace(/&/g,"&amp;").replace(/</g,"&lt;")
         .replace(/>/g,"&gt;").replace(/"/g,"&quot;");
}
function hide(id){ $(id).classList.add("hidden"); }
function show(id){ $(id).classList.remove("hidden"); }
var tt = null;
function toast(msg, bad){
  var el = $("toast");
  el.textContent = msg;
  el.className = "toast show" + (bad ? " bad" : "");
  clearTimeout(tt);
  tt = setTimeout(function(){ el.className = "toast"; }, 3600);
}

/* ---------- 导航 ---------- */
function go(p){
  var items = document.querySelectorAll(".nav-item");
  for (var i = 0; i < items.length; i++) items[i].classList.toggle("active", items[i].getAttribute("data-p") === p);
  var pages = ["sites","temp","maint"];
  for (var j = 0; j < pages.length; j++) $("page-" + pages[j]).classList.toggle("hidden", pages[j] !== p);
  if (history.replaceState) history.replaceState(null, "", p === "sites" ? location.pathname : "#" + p);
}

/* ---------- 列表 ---------- */
function chipHtml(h, dis){
  if (dis) return '<span class="chip off"><i class="d"></i>已停用</span>';
  if (!h || h.ok === null || h.ok === undefined) return '<span class="chip unk"><i class="d"></i>未检测</span>';
  var cls = h.ok ? "ok" : "bad", txt = h.ok ? "正常" : "连不上";
  return '<span class="chip ' + cls + '" title="' + esc(h.msg) + '"><i class="d"></i>' + txt + '</span>';
}
function renderSites(){
  $("cnt").textContent = D.sites.length;
  if (!D.sites.length){
    $("sitesBox").innerHTML = '<div class="empty"><div class="eic"><svg width="26" height="26"><use href="#i-door"/></svg></div>'
      + '<h3>还没有站点</h3><p>把光猫、路由器、群晖这些内网后台加进来，桌面就会多一个图标。</p>'
      + '<button class="btn primary" onclick="openAdd()"><svg><use href="#i-plus"/></svg>添加第一个站点</button></div>';
    return;
  }
  var out = '<div class="list">';
  D.sites.forEach(function(s){
    var sub = s.scheme + "://" + s.host + ":" + s.target_port + (s.base_path || "");
    out += '<div class="row' + (s.disabled ? " dim" : "") + '" data-id="' + esc(s.id) + '">'
      + '<img class="ric" src="' + esc(s.icon) + '" alt="" onerror="this.style.visibility=hidden">'
      + '<div class="rmain"><div class="rname">' + esc(s.name) + '</div><div class="rsub">' + esc(sub) + '</div></div>'
      + chipHtml(s.health, s.disabled)
      + '<div class="rport"><span class="pill">:' + s.local_port + '</span></div>'
      + '<div class="racts"><a class="btn ghost sm" data-open href="' + esc(s.local_url) + '" target="_blank" rel="noopener">打开</a>'
      + '<button class="btn text sm" data-act="edit">设置</button></div>'
      + '</div>';
  });
  $("sitesBox").innerHTML = out + "</div>";
}

/* ---------- 添加 ---------- */
function openAdd(){
  $("a_name").value = ""; $("a_host").value = ""; $("a_port").value = "80"; $("a_base").value = "";
  setSeg("a_seg", "http");
  show("maskAdd");
  setTimeout(function(){ $("a_name").focus(); }, 60);
}
function setSeg(id, v){
  var bs = $(id).querySelectorAll("button");
  for (var i = 0; i < bs.length; i++) bs[i].classList.toggle("on", bs[i].getAttribute("data-v") === v);
}
function getSeg(id){
  var b = $(id).querySelector("button.on");
  return b ? b.getAttribute("data-v") : "http";
}
["a_seg","s_seg"].forEach(function(id){
  $(id).addEventListener("click", function(e){
    var b = e.target.closest("button"); if (!b) return;
    setSeg(id, b.getAttribute("data-v"));
  });
});
function addSite(){
  var name = $("a_name").value.trim(), host = $("a_host").value.trim();
  if (!name || !host){ toast("名称和地址都要填", true); return; }
  postJson("/add", {name:name, host:host, port:$("a_port").value.trim() || "80",
                    scheme:getSeg("a_seg"), base_path:$("a_base").value.trim()})
  .then(function(r){
    if (r.error){ toast(r.error, true); return; }
    hide("maskAdd");
    if (r.job) watchJob(r.job, "添加「" + name + "」", true);
    else { toast("已添加"); setTimeout(function(){ location.reload(); }, 800); }
  })
  .catch(function(){ toast("添加失败", true); });
}

/* ---------- 站点设置 ---------- */
function openSite(id){
  cur = null;
  for (var i = 0; i < D.sites.length; i++) if (D.sites[i].id === id) cur = D.sites[i];
  if (!cur) return;
  $("s_title").textContent = cur.name;
  $("s_app").textContent = cur.app;
  $("s_chip").innerHTML = chipHtml(cur.health, cur.disabled);
  $("s_icon").src = cur.icon; $("s_icon2").src = cur.icon;
  $("s_name").value = cur.name; $("s_host").value = cur.host;
  $("s_port").value = cur.target_port; $("s_base").value = cur.base_path || "";
  $("s_local").value = cur.local_port;
  setSeg("s_seg", cur.scheme);
  $("s_pub").value = cur.public_url || "（未取到 Connect 域名）";
  $("s_loc").value = cur.local_url;
  $("s_pubOpen").href = cur.public_url || "#";
  $("s_locOpen").href = cur.local_url;
  $("s_clear").href = cur.local_url + "__anydoor_clear";
  $("s_msg").textContent = "";
  $("s_toggleT").textContent = cur.disabled ? "启用" : "停用";
  $("s_toggleB").textContent = cur.disabled ? "启用" : "停用";
  glyph = "router"; bg = COLORS[0]; iconDirty = false;
  show("maskSite");
}
var CH_LABEL = {name:"名称", target:"地址", path:"路径", port:"本地端口", icon:"图标"};
function chNames(list){
  return (list || []).map(function(k){ return CH_LABEL[k] || k; }).join(" · ");
}
var saving = false;
function saveSite(){
  if (!cur || saving) return;
  saving = true;
  $("s_msg").textContent = "保存中…";
  var title = $("s_name").value.trim() || cur.name;
  postJson("/save", {id:cur.id, name:$("s_name").value, host:$("s_host").value,
    port:$("s_port").value, scheme:getSeg("s_seg"), base_path:$("s_base").value,
    local_port:$("s_local").value, icon_changed: iconDirty ? "1" : "0"})
  .then(function(r){
    if (r.error){ $("s_msg").textContent = r.error; toast(r.error, true); return; }
    var ch = r.changed || [];
    if (!ch.length){ $("s_msg").textContent = "没有改动"; toast("没有改动"); return; }
    hide("maskSite");
    if (r.job){
      toast("已保存：" + chNames(ch) + "，正在更新桌面应用");
      watchJob(r.job, "更新「" + title + "」", true);
    } else {
      toast("已保存：" + chNames(ch) + "，立即生效");
      setTimeout(function(){ location.reload(); }, 800);
    }
  })
  .catch(function(){ $("s_msg").textContent = "保存失败"; toast("保存失败", true); })
  .then(function(){ saving = false; });
}
function appOp(op){
  if (!cur) return;
  var o = op === "toggle" ? (cur.disabled ? "enable" : "disable") : op;
  var titles = {reinstall:"重装「" + cur.name + "」", refresh:"刷新外网地址",
                enable:"启用「" + cur.name + "」", disable:"停用「" + cur.name + "」"};
  postJson("/app/op", {id:cur.id, op:o}).then(function(r){
    if (r.error){ toast(r.error, true); return; }
    hide("maskSite");
    if (r.job) watchJob(r.job, titles[o] || "处理中", true);
    else { toast("已提交"); setTimeout(function(){ location.reload(); }, 800); }
  }).catch(function(){ toast("操作失败", true); });
}
function askDelete(){
  if (!cur) return;
  var name = cur.name, id = cur.id;
  ask("删除站点「" + name + "」？", "会同时卸载桌面应用，站点配置不可恢复。", function(){
    postJson("/del", {id:id}).then(function(r){
      hide("maskAsk"); hide("maskSite");
      if (r.job) watchJob(r.job, "删除「" + name + "」", true);
      else { toast("已删除"); setTimeout(function(){ location.reload(); }, 700); }
    }).catch(function(){ toast("删除失败", true); });
  });
}

/* ---------- 图标 ---------- */
function openIcon(){
  if (!cur) return;
  $("ic_name").textContent = cur.name;
  $("ic_prev").src = cur.icon + "?t=" + Date.now();
  $("ic_char").value = ""; $("ic_state").textContent = "";
  drawIconChips();
  show("maskIcon");
}
function drawIconChips(){
  var g = "";
  var hex = bg.replace("#", "");
  GLYPHS.forEach(function(x){
    g += '<button class="glyph' + (x[0] === glyph ? " on" : "") + '" data-g="' + x[0] + '">'
      + '<img src="/preset/' + x[0] + '/' + hex + '.png" alt="">' + x[1] + '</button>';
  });
  $("ic_glyphs").innerHTML = g;
  var c = "";
  COLORS.forEach(function(v){
    c += '<button class="sw' + (v === bg ? " on" : "") + '" data-c="' + v + '" style="background:' + v + '"></button>';
  });
  $("ic_sws").innerHTML = c;
}
$("ic_glyphs").addEventListener("click", function(e){
  var b = e.target.closest("[data-g]"); if (!b) return;
  glyph = b.getAttribute("data-g"); $("ic_char").value = "";
  drawIconChips(); applyIcon("preset");
});
$("ic_sws").addEventListener("click", function(e){
  var b = e.target.closest("[data-c]"); if (!b) return;
  bg = b.getAttribute("data-c");
  drawIconChips(); applyIcon($("ic_char").value.trim() ? "char" : "preset");
});
$("ic_char").addEventListener("input", function(){
  if (this.value.trim()) applyIcon("char");
});
function refreshIcon(){
  var src = "/icon/" + cur.app + ".png?t=" + Date.now();
  $("ic_prev").src = src; $("s_icon").src = src; $("s_icon2").src = src;
}
function applyIcon(mode){
  if (!cur) return;
  $("ic_state").textContent = "生成中…";
  post("/icon/apply", {app:cur.app, mode:mode, glyph:glyph, char:$("ic_char").value.trim(), bg:bg})
  .then(function(t){
    if (!t){
      iconDirty = true;
      $("ic_state").textContent = "已更新";
      refreshIcon();
    } else {
      $("ic_state").textContent = t.slice(0, 40) || "失败";
    }
  });
}
function iconAuto(){
  if (!cur) return;
  post("/icon/apply", {app:cur.app, mode:"auto"}).then(function(t){
    if (!t){ iconDirty = true; refreshIcon(); toast("已抓到站点图标"); }
    else toast(t || "这个站点没有 favicon", true);
  });
}
function uploadIcon(inp){
  var f = inp.files[0]; if (!f || !cur) return;
  $("ic_state").textContent = "上传中…";
  fetch("/icon/upload?app=" + encodeURIComponent(cur.app), {method:"POST", body:f})
  .then(function(r){ return r.text(); }).then(function(t){
    if (t.trim() === "ok"){ iconDirty = true; $("ic_state").textContent = "已上传"; refreshIcon(); }
    else $("ic_state").textContent = t.slice(0, 40) || "失败";
  });
}

/* ---------- 临时通道 ---------- */
function renderTemp(){
  var t = D.temp;
  $("tempChip").innerHTML = t.host ? chipHtml(t.health, false) : '<span class="chip unk"><i class="d"></i>未设置</span>';
  $("tempTarget").textContent = t.host ? (t.scheme + "://" + t.host + ":" + t.port) : "还没有目标，下面填一个地址。";
  $("tempLocal").textContent = t.local_url || "-";
  $("tempPublic").textContent = t.public_url || "-";
}
function tempSet(e){
  e.preventDefault();
  var v = $("tempInput").value.trim();
  if (!v){ toast("先填个地址", true); return false; }
  post("/temp", {url:v}).then(function(){
    $("tempInput").value = "";
    toast("已切换"); setTimeout(function(){ location.reload(); }, 900);
  });
  return false;
}
function tempClear(){
  post("/tempclear", {}).then(function(){
    toast("已清除目标"); setTimeout(function(){ location.reload(); }, 900);
  });
}

/* ---------- 维护 ---------- */
function run(url, msg){
  toast(msg);
  fetch(url, {headers:{"X-Admin-Ajax":"1"}}).then(function(){
    toast(msg + "（后台进行，稍后刷新看结果）");
  });
}
function askRebuild(){
  ask("重建全部桌面应用？", "逐个重装，站点多的话要几分钟，期间桌面图标会短暂消失。", function(){
    hide("maskAsk");
    run("/rebuild", "正在重建…");
  });
}
function toggleLog(){
  var on = !D.meta.log_on;
  fetch("/log?on=" + (on ? "1" : "0")).then(function(r){ return r.text(); }).then(function(){
    D.meta.log_on = on;
    $("logBtn").textContent = on ? "关闭" : "开启";
    toast(on ? "请求日志已开启" : "请求日志已关闭");
  });
}
function probeAll(btn){
  if (btn) btn.disabled = true;
  fetch("/probe").then(function(){ return true; }).then(function(){
    toast("正在探测…");
    setTimeout(function(){ location.reload(); }, 2500);
  });
}
function renderMeta(){
  $("mCount").textContent = D.sites.length + " 个";
  $("mDomain").textContent = D.meta.domain || "未取到";
  $("mPattern").textContent = D.meta.domain ? ("https://<应用名>-web." + D.meta.domain + "/") : "-";
  $("mDir").textContent = D.meta.data_dir || "-";
  $("logBtn").textContent = D.meta.log_on ? "关闭" : "开启";
}

/* ---------- 通用 ---------- */
function postJson(url, obj){
  var body = new URLSearchParams();
  for (var k in obj) if (obj.hasOwnProperty(k)) body.append(k, obj[k]);
  return fetch(url, {method:"POST", body:body, headers:{"X-Admin-Ajax":"1"}})
    .then(function(r){
      return r.text().then(function(t){
        try { return JSON.parse(t); } catch(e){ return {error: (t || "服务无响应").trim()}; }
      });
    });
}
function watchJob(id, title, reloadOnDone){
  var el = document.createElement("div");
  el.className = "job";
  el.innerHTML = '<div class="job-h"><span class="spin"></span><b>' + esc(title) + '</b></div>'
    + '<div class="job-bar"><i></i></div><div class="job-t">准备中…</div>';
  $("jobs").appendChild(el);
  var bar = el.querySelector(".job-bar i"), txt = el.querySelector(".job-t");
  function finish(ok, text, detail){
    el.classList.add(ok ? "ok" : "bad");
    el.querySelector(".spin").outerHTML = ok
      ? '<svg class="jok" width="15" height="15" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.4" stroke-linecap="round" stroke-linejoin="round"><path d="M4.5 12.5l5 5 10-11"/></svg>'
      : '<svg class="jbad" width="15" height="15" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.4" stroke-linecap="round"><path d="M6.5 6.5l11 11M17.5 6.5l-11 11"/></svg>';
    bar.style.width = "100%";
    txt.textContent = text + (detail ? " · " + detail : "");
    if (!ok){ setTimeout(function(){ if (el.parentNode) el.parentNode.removeChild(el); }, 5000); return; }
    if (reloadOnDone) setTimeout(function(){ location.reload(); }, 850);
    else setTimeout(function(){ if (el.parentNode) el.parentNode.removeChild(el); }, 2400);
  }
  function tick(){
    fetch("/job?id=" + encodeURIComponent(id))
    .then(function(r){ return r.json(); })
    .then(function(j){
      if (!j || j.error){ finish(false, "任务丢失"); return; }
      bar.style.width = (j.total ? Math.round(j.step / j.total * 100) : 35) + "%";
      if (j.state === "running"){
        txt.textContent = j.text + (j.total ? "  " + j.step + "/" + j.total : "");
        setTimeout(tick, 650);
      } else {
        finish(j.state === "done", j.text, j.detail);
      }
    })
    .catch(function(){ setTimeout(tick, 1500); });
  }
  tick();
}
function post(url, obj){
  var body = new URLSearchParams();
  for (var k in obj) if (obj.hasOwnProperty(k)) body.append(k, obj[k]);
  return fetch(url, {method:"POST", body:body, headers:{"X-Admin-Ajax":"1"}})
    .then(function(r){ return r.text(); })
    .then(function(t){
      t = (t || "").trim();
      if (t === "ok" || t === "") return "";
      return t;
    });
}
function ask(title, desc, cb){
  $("ask_t").textContent = title;
  $("ask_d").textContent = desc;
  askCb = cb;
  show("maskAsk");
}
$("ask_ok").addEventListener("click", function(){
  var f = askCb; askCb = null;
  if (f) f(); else hide("maskAsk");
});
function copyText(v){
  if (navigator.clipboard && window.isSecureContext){
    navigator.clipboard.writeText(v); toast("已复制"); return;
  }
  var ta = document.createElement("textarea");
  ta.value = v; ta.style.position = "fixed"; ta.style.opacity = "0";
  document.body.appendChild(ta); ta.select();
  try { document.execCommand("copy"); toast("已复制"); } catch(e){ toast("复制失败", true); }
  document.body.removeChild(ta);
}
function copyEl(id, btn){
  var v = $(id).value !== undefined && $(id).tagName === "INPUT" ? $(id).value : $(id).textContent;
  copyText(v);
  if (btn){ var o = btn.textContent; btn.textContent = "已复制";
    setTimeout(function(){ btn.textContent = o; }, 1200); }
}

/* ---------- 事件 ---------- */
$("sitesBox").addEventListener("click", function(e){
  if (e.target.closest("[data-open]")) return;
  var row = e.target.closest(".row");
  if (!row) return;
  openSite(row.getAttribute("data-id"));
});
document.addEventListener("keydown", function(e){
  if (e.key !== "Escape") return;
  if (!$("maskAsk").classList.contains("hidden")) { hide("maskAsk"); return; }
  if (!$("maskIcon").classList.contains("hidden")) { hide("maskIcon"); return; }
  if (!$("maskSite").classList.contains("hidden")) { hide("maskSite"); return; }
  if (!$("maskAdd").classList.contains("hidden")) { hide("maskAdd"); return; }
});
document.addEventListener("click", function(e){
  if (e.target.classList && e.target.classList.contains("mask")) e.target.classList.add("hidden");
});
["a_name","a_host","a_port","a_base"].forEach(function(id){
  $(id).addEventListener("keydown", function(e){ if (e.key === "Enter") addSite(); });
});

renderSites();
renderTemp();
renderMeta();
var h = (location.hash || "").replace("#", "");
if (h && ["temp","maint"].indexOf(h) >= 0) go(h);
</script>
</body>
</html>"""


ICON_MISSING = set()
PRESET_CACHE = {}
FALLBACK_BG = ["#0066ff", "#009e61", "#e06c00", "#7c3aed", "#0891b2", "#db382c", "#475569", "#0f766e"]


def icon_or_make(app):
    """有图标就用；没有就按站点名首字生成一枚，结果落盘复用。"""
    p = icon_path(app)
    if p or app in ICON_MISSING:
        return p
    site = next((x for x in _sites.values() if x["app"] == app), None)
    if site is None and app == TEMP_APP:
        site = TEMP
    if site is None:
        return None
    name = (site.get("name") or app).strip()
    h = 0
    for ch in name:
        h = (h * 31 + ord(ch)) % 9973
    try:
        path, _ = render_icon(app, "char", char=name[:1], bg=FALLBACK_BG[h % len(FALLBACK_BG)])
    except Exception:
        path = None
    if not path:
        ICON_MISSING.add(app)
    return path


def page_data(host):
    """把运行态整理成前端要的一份 JSON：站点 + 临时通道 + 环境信息。"""
    sites = []
    for s_ in _sites.values():
        h = _health.get(s_["id"]) or {}
        ip = icon_or_make(s_["app"])
        try:
            ver = int(os.path.getmtime(ip)) if ip else 0
        except OSError:
            ver = 0
        sites.append({
            "id": s_["id"], "name": s_["name"], "app": s_["app"],
            "host": s_.get("host") or "",
            "target_port": s_.get("target_port") or 0,
            "scheme": s_.get("scheme") or "http",
            "base_path": s_.get("base_path") or "",
            "local_port": s_.get("local_port") or 0,
            "disabled": bool(s_.get("disabled")),
            "health": {"ok": h.get("ok"), "msg": h.get("msg") or ""},
            "local_url": "http://%s:%s/" % (host, s_.get("local_port") or 0),
            "public_url": public_url(s_["app"]),
            "icon": "/icon/%s.png?v=%s" % (s_["app"], ver),
        })
    th = _health.get("temp") or {}
    temp = {
        "host": TEMP.get("host") or "",
        "port": TEMP.get("target_port") or 0,
        "scheme": TEMP.get("scheme") or "http",
        "local_url": ("http://%s:%s/" % (host, TEMP["local_port"])) if TEMP.get("local_port") else "",
        "public_url": public_url(TEMP_APP) if TEMP.get("local_port") else "",
        "health": {"ok": th.get("ok"), "msg": th.get("msg") or ""},
    }
    return {"sites": sites, "temp": temp,
            "meta": {"domain": CONNECT_DOMAIN, "data_dir": VAR, "log_on": _logreq["on"]}}


def render_page(host):
    payload = json.dumps(page_data(host), ensure_ascii=False).replace("</", "<\\/")
    return ADMIN_HTML.replace("__DATA_JSON__", payload)


class Admin(http.server.BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def log_message(self, *a):
        pass

    def _send(self, code, body, ctype="text/html; charset=utf-8", extra=None):
        raw = body.encode() if isinstance(body, str) else body
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Cache-Control", "no-store")
        for k, v in (extra or []):
            self.send_header(k, v)
        self.send_header("Content-Length", str(len(raw)))
        self.end_headers()
        self.wfile.write(raw)

    def _page(self):
        host = (self.headers.get("Host") or "").split(":")[0] or "127.0.0.1"
        return render_page(host)

    def do_GET(self):
        if self.path.split("?")[0] in ("/favicon.ico", "/favicon.png"):
            p = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                             "..", "ui", "images", "icon_256.png")
            if not os.path.isfile(p):
                p = icon_path("anydoor2") or ""
            if p and os.path.isfile(p):
                with open(p, "rb") as f:
                    body = f.read()
                return self._send(200, body, "image/png")
            return self._send(404, b"", "image/png")
        if self.path.split("?")[0] == "/api/sites":
            data = [dict(s, health=_health.get(s["id"])) for s in _sites.values()]
            return self._send(200, json.dumps(data, ensure_ascii=False),
                              "application/json; charset=utf-8")
        if self.path.split("?")[0].startswith("/preset/"):
            bits = self.path.split("?")[0][len("/preset/"):].replace(".png", "").split("/")
            glyph = re.sub(r"[^a-z]", "", bits[0]) or "router"
            bg = "#" + (re.sub(r"[^0-9a-fA-F]", "", bits[1])[:6] if len(bits) > 1 else "0066ff")
            if len(bg) != 7:
                bg = "#0066ff"
            body = PRESET_CACHE.get((glyph, bg))
            if body is None:
                body = make_preset_icon(glyph, bg)
                PRESET_CACHE[(glyph, bg)] = body
            self.send_response(200)
            self.send_header("Content-Type", "image/png")
            self.send_header("Cache-Control", "public, max-age=86400")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return
        if self.path.split("?")[0].startswith("/icon/"):
            app = self.path.split("?")[0][len("/icon/"):].replace(".png", "")
            p = icon_or_make(app)
            if not p:
                body = b""
                self.send_response(404)
            else:
                with open(p, "rb") as f:
                    body = f.read()
                self.send_response(200)
                self.send_header("Content-Type", "image/png")
            self.send_header("Cache-Control", "no-store")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            if body:
                self.wfile.write(body)
            return
        if self.path.split("?")[0] == "/icons":
            threading.Thread(target=fetch_all_icons, daemon=True).start()
            return self._send(200, "fetching icons\n", "text/plain; charset=utf-8")
        if self.path.split("?")[0] == "/log":
            qs = urllib.parse.parse_qs(urllib.parse.urlsplit(self.path).query)
            if "on" in qs:
                _logreq["on"] = qs["on"][0] == "1"
            return self._send(200, "log=%s\n" % ("on" if _logreq["on"] else "off"),
                              "text/plain; charset=utf-8")
        if self.path.split("?")[0] == "/probe":
            threading.Thread(target=probe_all, daemon=True).start()
            return self._send(200, "probing\n", "text/plain; charset=utf-8")
        if self.path.split("?")[0] == "/job":
            qs = urllib.parse.parse_qs(urllib.parse.urlsplit(self.path).query)
            jid = (qs.get("id") or [""])[0]
            j = JOBS.get(jid)
            if not j:
                return self._send(404, json.dumps({"error": "任务不存在"}), "application/json; charset=utf-8")
            return self._send(200, json.dumps(j, ensure_ascii=False),
                              "application/json; charset=utf-8")
        if self.path.split("?")[0] == "/jobs":
            with _lock:
                items = sorted(JOBS.values(), key=lambda x: x["ts"])[-10:]
            return self._send(200, json.dumps(items, ensure_ascii=False),
                              "application/json; charset=utf-8")
        if self.path.split("?")[0] == "/rebuild":
            threading.Thread(target=rebuild_all, daemon=True).start()
            return self._send(200, "rebuilding\n", "text/plain; charset=utf-8")
        if self.path.split("?")[0] == "/migrate":
            threading.Thread(target=migrate_apps, daemon=True).start()
            return self._send(200, "migrating\n", "text/plain; charset=utf-8")
        return self._send(200, self._page())

    def do_POST(self):
        if self.path.split("?")[0] == "/icon/upload":
            qs = urllib.parse.parse_qs(urllib.parse.urlsplit(self.path).query)
            app = (qs.get("app") or [""])[0]
            length = int(self.headers.get("Content-Length") or 0)
            raw = self.rfile.read(length) if length else b""
            path, err = render_icon(app, "upload", data=raw)
            return self._send(200, "ok\n" if path else (err + "\n"),
                              "text/plain; charset=utf-8")
        length = int(self.headers.get("Content-Length") or 0)
        form = urllib.parse.parse_qs(self.rfile.read(length).decode("utf-8", "replace"))
        p = self.path.split("?")[0]
        if p == "/add":
            name, host = form.get("name", [""])[0].strip(), form.get("host", [""])[0].strip()
            if not name or not host:
                return self._send(200, json.dumps({"error": "名称和地址都要填"}, ensure_ascii=False),
                                  "application/json; charset=utf-8")
            jid = add_site(name, host, form.get("port", ["80"])[0],
                           form.get("scheme", ["http"])[0], form.get("base_path", [""])[0])
            return self._send(200, json.dumps({"error": "", "job": jid}, ensure_ascii=False),
                              "application/json; charset=utf-8")
        elif p == "/temp":
            if not set_temp(form.get("url", [""])[0]):
                return self._send(200, "地址看不懂，检查一下\n", "text/plain; charset=utf-8")
        elif p == "/tempclear":
            clear_temp()
        elif p == "/migrate":
            threading.Thread(target=migrate_apps, daemon=True).start()
            return self._send(200, "migrating\n", "text/plain; charset=utf-8")
        elif p == "/rebuild":
            threading.Thread(target=rebuild_all, daemon=True).start()
            return self._send(200, "rebuilding\n", "text/plain; charset=utf-8")
        elif p == "/save":
            err, jid, changed = save_site(form.get("id", [""])[0], form)
            return self._send(200, json.dumps({"error": err, "job": jid, "changed": changed},
                                              ensure_ascii=False),
                              "application/json; charset=utf-8")
        elif p == "/app/op":
            err, jid = app_op(form.get("id", [""])[0], form.get("op", [""])[0])
            return self._send(200, json.dumps({"error": err, "job": jid}, ensure_ascii=False),
                              "application/json; charset=utf-8")
        elif p == "/icon/apply":
            app = form.get("app", [""])[0]
            mode = form.get("mode", ["preset"])[0]
            if mode == "auto":
                site = next((x for x in _sites.values() if x["app"] == app), None)
                if site is None and TEMP.get("app") == app:
                    site = TEMP
                got = fetch_icon(site) if site else None
                return self._send(200, "ok\n" if got else "没找到可用的 favicon\n",
                                  "text/plain; charset=utf-8")
            path, err = render_icon(app, mode,
                                    form.get("glyph", ["router"])[0],
                                    form.get("char", [""])[0],
                                    form.get("bg", ["#1f6feb"])[0])
            return self._send(200, "ok\n" if path else (err + "\n"),
                              "text/plain; charset=utf-8")
        elif p == "/del":
            jid = del_site(form.get("id", [""])[0])
            return self._send(200, json.dumps({"error": "", "job": jid}, ensure_ascii=False),
                              "application/json; charset=utf-8")
        if self.headers.get("X-Admin-Ajax"):
            return self._send(200, "ok\n", "text/plain; charset=utf-8")
        self.send_response(303)
        self.send_header("Location", "/")
        self.send_header("Content-Length", "0")
        self.end_headers()


def connect_domain():
    """读飞牛 Connect 的域名。证书配置里一定有 <子域>.<主域>，
    这是最稳的来源；读不到就返回空串（此时不写 fullUrl，行为退回旧版）。"""
    pat = re.compile(r"[a-z0-9][a-z0-9.-]*\.(?:5ddd\.com|fnos\.net|trzznas\.com)")
    for f in ("/usr/trim/etc/network_gateway_cert.conf",
              "/usr/trim/etc/network_cert_all.conf"):
        try:
            with open(f, errors="replace") as fh:
                for m in pat.finditer(fh.read().lower()):
                    v = m.group(0).rstrip(".")
                    if v.count(".") == 2:
                        return v
        except Exception:
            pass
    return ""


CONNECT_DOMAIN = connect_domain()


def public_url(appname, path="/"):
    """外网访问地址：<appname>-web.<Connect 域名><path>。
    飞牛桌面在「非内网 IP」访问时优先用 fullUrl（wYe 第一分支），
    写死它就不依赖云端是否给这个应用分配了 fnDomain。"""
    if not CONNECT_DOMAIN:
        return ""
    p = path or "/"
    if not p.startswith("/"):
        p = "/" + p
    return "https://%s-web.%s%s" % (appname, CONNECT_DOMAIN, p)


def _appname(sid):
    """飞牛的子域名是 <appname>-web.<用户域>，appname 里出现点号会导致
    云端算不出这个子域名，桌面只能退回 host:port，公网端口不通就是「拒绝连接」。
    所以站点应用一律用单段、纯小写的名字。"""
    return "ad" + re.sub(r"[^a-z0-9]", "", (sid or "").lower())


def add_site(name, host, port, scheme, base_path=""):
    host = (host or "").strip().replace("http://", "").replace("https://", "").strip("/")
    if not host:
        return
    try:
        tport = int(port or 80)
    except ValueError:
        tport = 80
    if ":" in host:                       # 地址里自带端口就用它
        h, _, p = host.partition(":")
        host, tport = h, int(p)
    base = (base_path or "").strip()
    if base and not base.startswith("/"):
        base = "/" + base
    base = base.rstrip("/")
    with _lock:
        sid = slug(name or host)
        base_id = sid
        i = 2
        while sid in _sites:
            sid = "%s-%d" % (base_id, i)
            i += 1
        site = {
            "id": sid,
            "name": name or host,
            "host": host,
            "target_port": tport,
            "scheme": scheme or "http",
            "base_path": base,
            "local_port": alloc_port(tport, exclude=(TEMP.get("local_port") or 0,)),
            "app": _appname(sid),
        }
        _sites[sid] = site
        save_state()
        start_forwarder(site)
    jid = job_new("添加「%s」" % site["name"])
    threading.Thread(target=install_app, args=(site, False, jid), daemon=True).start()
    sys.stderr.write("add site %s -> :%d job=%s\n" % (sid, site["local_port"], jid))
    return jid


# ---------------- 临时通道 ----------------

def parse_target(text):
    """把 '10.0.0.1:8080'、'http://x/y'、'https://x' 解析成 (host, port, scheme)。"""
    raw = (text or "").strip()
    if not raw:
        return None
    scheme = "http"
    m = re.match(r"^(https?)://(.+)$", raw, re.I)
    if m:
        scheme, raw = m.group(1).lower(), m.group(2)
    host, port = raw, 80 if scheme == "http" else 443
    if ":" in raw:
        h, _, p = raw.partition(":")
        host = h
        port = int(p) if p.isdigit() else (80 if scheme == "http" else 443)
    host = host.split("/")[0].strip()
    if not host:
        return None
    return host, port, scheme


def set_temp(text, install_if_needed=True):
    t = parse_target(text)
    if not t:
        return False
    host, port, scheme = t
    with _lock:
        TEMP["host"] = host
        TEMP["target_port"] = port
        TEMP["scheme"] = scheme
        if not TEMP.get("local_port"):
            TEMP["local_port"] = alloc_port(port, exclude=[s["local_port"] for s in _sites.values()])
            start_forwarder(TEMP)
            if install_if_needed:
                threading.Thread(target=lambda: install_app(TEMP, reinstall=False), daemon=True).start()
        save_state()
    threading.Thread(target=lambda: _health.__setitem__("temp", dict(zip(("ok", "msg", "ts"),
                     probe_site(TEMP) + (time.time(),)))), daemon=True).start()
    sys.stderr.write("temp -> %s://%s:%s (:%s)\n" % (scheme, host, port, TEMP.get("local_port")))
    return True


def clear_temp():
    with _lock:
        TEMP["host"] = ""
        TEMP["target_port"] = 0
        save_state()
    sys.stderr.write("temp cleared\n")


# ---------------- 维护 ----------------

def migrate_apps():
    """把旧的双段应用名（anydoor.xxx）迁移成单段（adxxx），并重建安装。"""
    for sid in list(_sites.keys()):
        site = _sites.get(sid)
        if not site:
            continue
        want = _appname(sid)
        if site.get("app") == want:
            continue
        old_app = site.get("app")
        if old_app:
            subprocess.run(["sh", "-c", "appcenter-cli uninstall %s >/dev/null 2>&1" % old_app], check=False)
        with _lock:
            site["app"] = want
            save_state()
        install_app(site)
        sys.stderr.write("migrate %s: %s -> %s\n" % (sid, old_app, want))


REBUILDING = {"on": False}


def rebuild_all():
    if REBUILDING["on"]:
        sys.stderr.write("rebuild skipped: already running\n")
        return
    REBUILDING["on"] = True
    try:
        sys.stderr.write("rebuild start, domain=%s\n" % CONNECT_DOMAIN)
        for sid in list(_sites.keys()):
            site = _sites.get(sid)
            if site:
                install_app(site)
        # 安装过程中 appcenter 会重建 app_service 行，所以 full_url 必须最后统一写
        for sid in list(_sites.keys()):
            site = _sites.get(sid)
            if site:
                set_full_url(svc(site["app"]), public_url(site["app"]))
        if TEMP.get("local_port"):
            set_full_url(svc(TEMP["app"]), public_url(TEMP["app"]))
        sys.stderr.write("rebuild done: %d sites\n" % len(_sites))
    finally:
        REBUILDING["on"] = False


def _restart_forwarder(site):
    stop_forwarder(site["id"])
    try:
        start_forwarder(site)
    except Exception as e:
        sys.stderr.write("重启转发器失败 %s: %s\n" % (site["id"], e))


def save_site(sid, form):
    """保存站点。返回 (错误, 任务id, 变更项列表)。
    只有动了「要写进应用包」的东西（名称 / 本地端口 / 图标）才重装，
    改地址、端口、路径这类只重启转发器，秒生效。"""
    site = _sites.get(sid)
    if not site:
        return "站点不存在", None, []
    name = (form.get("name", [""])[0] or site["name"]).strip()
    host = (form.get("host", [""])[0] or "").strip()
    host = host.replace("http://", "").replace("https://", "").strip("/")
    try:
        tport = int(form.get("port", [""])[0] or site["target_port"])
    except ValueError:
        tport = site["target_port"]
    scheme = form.get("scheme", [site.get("scheme") or "http"])[0] or "http"
    base = (form.get("base_path", [""])[0] or "").strip()
    if base and not base.startswith("/"):
        base = "/" + base
    base = base.rstrip("/")
    try:
        new_local = int(form.get("local_port", [""])[0] or site["local_port"])
    except ValueError:
        new_local = site["local_port"]
    icon_changed = form.get("icon_changed", ["0"])[0] == "1"

    port_changed = new_local != site["local_port"]
    if port_changed and (not port_free(new_local) or new_local == ADMIN_PORT):
        return "本地端口 %d 不可用" % new_local, None, []
    if ":" in host:
        h, _, p = host.partition(":")
        host, tport = h, int(p) if p.isdigit() else tport

    changed = []
    if name != site["name"]:
        changed.append("name")
    if (host, tport, scheme) != (site.get("host"), site.get("target_port"), site.get("scheme")):
        changed.append("target")
    if base != (site.get("base_path") or ""):
        changed.append("path")
    if port_changed:
        changed.append("port")
    if icon_changed:
        changed.append("icon")
    if not changed:
        return "", None, []

    with _lock:
        site.update({"name": name, "host": host, "target_port": tport,
                     "scheme": scheme, "base_path": base})
        if port_changed:
            site["local_port"] = new_local
        save_state()
    if "target" in changed or port_changed:
        _restart_forwarder(site)

    jid = None
    if {"name", "port", "icon"} & set(changed):
        jid = job_new("更新「%s」" % site["name"])
        threading.Thread(target=install_app, args=(site, True, jid), daemon=True).start()
    sys.stderr.write("save site %s -> %s://%s:%s%s (:%s) changed=%s job=%s\n"
                     % (sid, scheme, host, tport, base, site["local_port"],
                        ",".join(changed), jid))
    return "", jid, changed


def app_op(sid, op):
    site = _sites.get(sid)
    if not site:
        return "站点不存在", None
    if op == "disable":
        jid = job_new("停用「%s」" % site["name"], 2)

        def run_disable():
            job_step(jid, "卸载桌面入口")
            subprocess.run(["sh", "-c", "appcenter-cli uninstall %s >/dev/null 2>&1"
                            % site["app"]], check=False)
            with _lock:
                site["disabled"] = True
                save_state()
            job_step(jid, "已停用", "站点配置仍保留")
            job_done(jid, True, "已停用")
            sys.stderr.write("app %s disabled\n" % site["app"])
        threading.Thread(target=run_disable, daemon=True).start()
        return "", jid
    if op == "enable":
        jid = job_new("启用「%s」" % site["name"])
        with _lock:
            site["disabled"] = False
            save_state()
        threading.Thread(target=install_app, args=(site, True, jid), daemon=True).start()
        return "", jid
    if op == "refresh":
        jid = job_new("刷新外网地址", 2)

        def run_refresh():
            job_step(jid, "写入应用入口地址")
            ok = set_full_url(svc(site["app"]), public_url(site["app"]))
            job_done(jid, ok, "已刷新" if ok else "暂未生效，后台会自动重试")
        threading.Thread(target=run_refresh, daemon=True).start()
        return "", jid
    if op == "reinstall":
        jid = job_new("重装「%s」" % site["name"])
        with _lock:
            site["disabled"] = False
            save_state()
        threading.Thread(target=install_app, args=(site, True, jid), daemon=True).start()
        return "", jid
    return "未知操作", None


def del_site(sid):
    with _lock:
        site = _sites.pop(sid, None)
        if not site:
            return None
        stop_forwarder(sid)
        save_state()
    jid = job_new("删除「%s」" % site["name"], 2)

    def run():
        job_step(jid, "卸载桌面入口")
        subprocess.run(["sh", "-c", "appcenter-cli uninstall %s >/dev/null 2>&1"
                        % site["app"]], check=False)
        job_step(jid, "已删除", "桌面图标已移除")
        job_done(jid, True, "已删除")
        sys.stderr.write("del site %s job=%s\n" % (sid, jid))
    threading.Thread(target=run, daemon=True).start()
    return jid


def main():
    os.makedirs(VAR, exist_ok=True)
    os.makedirs(WORKDIR, exist_ok=True)
    load_state()
    for s in list(_sites.values()):
        try:
            start_forwarder(s)
        except Exception as e:
            sys.stderr.write("恢复 %s 失败: %s\n" % (s["id"], e))
    # 临时通道：端口分配过就常驻（即使暂时没目标，也返回一句提示页）
    if not TEMP.get("local_port"):
        try:
            TEMP["local_port"] = alloc_port(80, exclude=[s["local_port"] for s in _sites.values()])
        except Exception as e:
            sys.stderr.write("临时通道端口分配失败: %s\n" % e)
    if TEMP.get("local_port"):
        try:
            start_forwarder(TEMP)
        except Exception as e:
            sys.stderr.write("临时通道启动失败: %s\n" % e)
        if not app_installed(TEMP_APP):
            threading.Thread(target=lambda: install_app(TEMP, reinstall=False), daemon=True).start()
        else:
            threading.Thread(target=lambda: set_full_url(svc(TEMP_APP), public_url(TEMP_APP)), daemon=True).start()
    threading.Thread(target=probe_loop, daemon=True).start()
    threading.Thread(target=lambda: (time.sleep(15), reconcile_full_urls(), probe_all()),
                     daemon=True).start()
    sys.stderr.write("anydoor admin on :%d, %d sites, temp :%s\n"
                     % (ADMIN_PORT, len(_sites), TEMP.get("local_port")))
    sys.stderr.flush()
    Threaded(("0.0.0.0", ADMIN_PORT), Admin).serve_forever()


if __name__ == "__main__":
    main()
