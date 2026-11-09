"""Loopback HTTP server: static UI, JSON API, and Server-Sent Events.

A single background poller fingerprints the allowlisted research files plus
git HEAD/status every `interval` seconds and rebuilds the snapshot only when
the fingerprint changes (and at least every `max_age` seconds). SSE clients
receive `snapshot` events with the new version number and `heartbeat` events
carrying the last poll result, so the UI can tell "server alive but poll
failing" from "connection lost".
"""

from __future__ import annotations

import argparse
import hashlib
import json
import mimetypes
import os
import sys
import threading
import time
from datetime import datetime, timezone
from http import HTTPStatus
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlsplit

from . import estimate, gitinfo, snapshot, sources

HERE = os.path.dirname(os.path.abspath(__file__))
MONITOR_ROOT = os.path.dirname(HERE)
STATIC_DIR = os.path.join(MONITOR_ROOT, "static")
STATIC_FILES = {"/": "index.html", "/index.html": "index.html", "/app.js": "app.js",
                "/estimator.js": "estimator.js", "/style.css": "style.css"}
MAX_SSE_CLIENTS = 32
SSE_MAX_SECONDS = 600  # clients reconnect automatically; bounds stuck sockets


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


class Monitor:
    """Owns the current snapshot and the polling thread."""

    def __init__(self, research_root: str, repo_root: str, manifest_path: str, pathspec: str | None,
                 interval: float = 5.0, max_age: float = 60.0):
        self.research_root = research_root
        self.repo_root = repo_root
        self.manifest_path = manifest_path
        self.pathspec = pathspec
        self.interval = interval
        self.max_age = max_age
        self.cond = threading.Condition()
        self.version = 0
        self.instance = os.urandom(6).hex()  # lets clients detect a server restart (version resets)
        self.snapshot: dict | None = None
        self.snapshot_json = b"{}"
        self.fingerprint: str | None = None
        self._content_key: str | None = None
        self.built_at = 0.0
        self.last_poll_at: str | None = None
        self.last_poll_ok = False
        self.last_poll_error: str | None = None
        self.last_change_at: str | None = None
        self._stop = threading.Event()
        self._thread: threading.Thread | None = None

    def compute_fingerprint(self) -> str:
        h = hashlib.sha256()
        for rel in sources.list_sources(self.research_root):
            st = sources.stat_source(self.research_root, rel)
            if st:
                h.update(f"{rel}\0{st.st_mtime_ns}\0{st.st_size}\n".encode())
        try:
            st = os.stat(self.manifest_path)
            h.update(f"manifest\0{st.st_mtime_ns}\0{st.st_size}\n".encode())
        except OSError:
            h.update(b"manifest-missing\n")
        head = gitinfo.run_git(self.repo_root, ["rev-parse", "HEAD"])
        h.update(b"head\0" + (head.out.encode() if head.ok else b"err"))
        args = ["status", "--porcelain=v1", "-z", "--untracked-files=all"]
        if self.pathspec:
            args += ["--", self.pathspec]
        st_res = gitinfo.run_git(self.repo_root, args)
        h.update(b"status\0" + (st_res.out.encode() if st_res.ok else b"err"))
        if not head.ok:
            raise RuntimeError(f"git rev-parse failed: {head.error}")
        return h.hexdigest()

    def poll_once(self) -> bool:
        """Return True if a new snapshot was published."""
        try:
            fp = self.compute_fingerprint()
            stale = time.time() - self.built_at > self.max_age
            changed = fp != self.fingerprint
            if changed or stale or self.snapshot is None:
                snap = snapshot.build_snapshot(self.research_root, self.repo_root, self.manifest_path, self.pathspec)
                data = json.dumps(snap, ensure_ascii=False, default=str)
                # Rebuild timestamps alone are not a content change.
                key = json.dumps({k: v for k, v in snap.items() if k not in ("generated_at", "build_ms")},
                                 sort_keys=True, default=str)
                with self.cond:
                    content_changed = key != self._content_key
                    self._content_key = key
                    self.fingerprint = fp
                    self.built_at = time.time()
                    if content_changed:
                        self.version += 1
                        self.snapshot = snap
                        self.snapshot_json = data.encode()
                        self.last_change_at = _now_iso()
                    self._record_poll(True, None)
                    self.cond.notify_all()
                return content_changed
            with self.cond:
                self._record_poll(True, None)
                self.cond.notify_all()
            return False
        except Exception as exc:  # keep serving the last good snapshot
            with self.cond:
                self._record_poll(False, f"{type(exc).__name__}: {exc}"[:500])
                self.cond.notify_all()
            return False

    def _record_poll(self, ok: bool, error: str | None) -> None:
        self.last_poll_at = _now_iso()
        self.last_poll_ok = ok
        self.last_poll_error = error

    def status(self) -> dict:
        return {
            "instance": self.instance,
            "version": self.version,
            "server_time": _now_iso(),
            "last_poll_at": self.last_poll_at,
            "last_poll_ok": self.last_poll_ok,
            "last_poll_error": self.last_poll_error,
            "last_change_at": self.last_change_at,
            "poll_interval_s": self.interval,
        }

    def start(self) -> None:
        self.poll_once()
        self._thread = threading.Thread(target=self._loop, name="research-poller", daemon=True)
        self._thread.start()

    def _loop(self) -> None:
        while not self._stop.wait(self.interval):
            self.poll_once()

    def stop(self) -> None:
        self._stop.set()
        with self.cond:
            self.cond.notify_all()


class Handler(BaseHTTPRequestHandler):
    server_version = "ResearchMonitor/1"
    sys_version = ""
    monitor: Monitor
    allowed_hosts: set[str]
    sse_clients = 0
    sse_lock = threading.Lock()

    def log_message(self, fmt: str, *args) -> None:  # quieter, single-line logs
        if os.environ.get("MONITOR_QUIET"):
            return
        sys.stderr.write("%s %s\n" % (self.log_date_time_string(), fmt % args))

    # ---- helpers -------------------------------------------------------
    def _headers(self, status: int, ctype: str, length: int | None = None, extra: dict | None = None) -> None:
        self.send_response(status)
        self.send_header("Content-Type", ctype)
        if length is not None:
            self.send_header("Content-Length", str(length))
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Referrer-Policy", "no-referrer")
        self.send_header("Cache-Control", "no-store")
        self.send_header("Content-Security-Policy",
                         "default-src 'self'; script-src 'self'; style-src 'self'; img-src 'self' data:; "
                         "connect-src 'self'; object-src 'none'; base-uri 'none'; form-action 'none'")
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()

    def _send(self, status: int, body: bytes, ctype: str) -> None:
        self._headers(status, ctype, len(body))
        if self.command != "HEAD":
            self.wfile.write(body)

    def _json(self, status: int, obj) -> None:
        self._send(status, json.dumps(obj, ensure_ascii=False, default=str).encode(), "application/json; charset=utf-8")

    def _host_ok(self) -> bool:
        host = (self.headers.get("Host") or "").strip().lower()
        return not self.allowed_hosts or host in self.allowed_hosts

    # ---- routing -------------------------------------------------------
    def do_HEAD(self) -> None:
        self.do_GET()

    def do_GET(self) -> None:
        if not self._host_ok():
            return self._json(HTTPStatus.MISDIRECTED_REQUEST, {"error": "unexpected Host header"})
        url = urlsplit(self.path)
        path, query = url.path, parse_qs(url.query, max_num_fields=8)
        try:
            if path in STATIC_FILES:
                return self._static(STATIC_FILES[path])
            if path == "/api/snapshot":
                with self.monitor.cond:
                    body, status = self.monitor.snapshot_json, self.monitor.status()
                return self._send(200, b'{"meta":' + json.dumps(status).encode() + b',"snapshot":' + body + b"}",
                                  "application/json; charset=utf-8")
            if path == "/api/status":
                return self._json(200, self.monitor.status())
            if path == "/api/source":
                return self._source(query.get("path", [""])[0])
            if path == "/api/sources":
                return self._json(200, {"sources": sources.list_sources(self.monitor.research_root)})
            if path == "/api/commit":
                res = gitinfo.show_commit(self.monitor.repo_root, query.get("hash", [""])[0])
                return self._json(200 if res.get("ok") else 404, res)
            if path == "/api/estimate":
                return self._estimate(query)
            if path == "/api/events":
                return self._events()
            return self._json(404, {"error": "not found"})
        except (BrokenPipeError, ConnectionResetError):
            return None

    def do_POST(self) -> None:
        self._json(405, {"error": "read-only monitor"})

    do_PUT = do_DELETE = do_PATCH = do_POST

    def _static(self, name: str) -> None:
        full = os.path.join(STATIC_DIR, name)
        try:
            with open(full, "rb") as fh:
                body = fh.read()
        except OSError:
            return self._json(404, {"error": "static file missing"})
        ctype = mimetypes.guess_type(name)[0] or "application/octet-stream"
        if ctype.startswith("text/") or ctype.endswith("javascript"):
            ctype += "; charset=utf-8"
        self._send(200, body, ctype)

    def _source(self, rel: str) -> None:
        try:
            f = sources.read_source(self.monitor.research_root, rel)
        except sources.SourceError as exc:
            return self._json(exc.status, {"error": str(exc)})
        self._json(200, {
            "path": f.path, "size": f.size, "truncated": f.truncated,
            "mtime": datetime.fromtimestamp(f.mtime, timezone.utc).isoformat(timespec="seconds"),
            "text": f.text,
        })

    def _estimate(self, query: dict) -> None:
        try:
            def num(name):
                raw = query.get(name, [None])[0]
                return None if raw in (None, "") else float(raw)
            log10_ops = estimate.work_log10(log2_work=num("log2_work"), sci_work=num("work"))
            result = estimate.estimate(log10_ops, num("gpus") or 0.0, num("rate") or 0.0)
        except (ValueError, TypeError) as exc:
            return self._json(400, {"error": str(exc)})
        self._json(200, result)

    def _events(self) -> None:
        with Handler.sse_lock:
            if Handler.sse_clients >= MAX_SSE_CLIENTS:
                return self._json(503, {"error": "too many live connections"})
            Handler.sse_clients += 1
        try:
            self._headers(200, "text/event-stream; charset=utf-8", extra={"Connection": "keep-alive", "X-Accel-Buffering": "no"})
            self.close_connection = True
            mon = self.monitor
            deadline = time.time() + SSE_MAX_SECONDS
            sent_version = -1
            last_beat = 0.0
            self.wfile.write(b"retry: 3000\n\n")
            while time.time() < deadline:
                with mon.cond:
                    if mon.version == sent_version and time.time() - last_beat < mon.interval:
                        mon.cond.wait(timeout=1.0)
                    status = mon.status()
                if status["version"] != sent_version:
                    self._sse("snapshot", status)
                    sent_version = status["version"]
                    last_beat = time.time()
                elif time.time() - last_beat >= mon.interval:
                    self._sse("heartbeat", status)
                    last_beat = time.time()
        except (BrokenPipeError, ConnectionResetError, TimeoutError, OSError):
            pass
        finally:
            with Handler.sse_lock:
                Handler.sse_clients -= 1

    def _sse(self, event: str, data: dict) -> None:
        self.wfile.write(f"event: {event}\ndata: {json.dumps(data)}\n\n".encode())
        self.wfile.flush()


def make_server(monitor: Monitor, host: str, port: int, extra_hosts: list[str] | None = None) -> ThreadingHTTPServer:
    httpd = ThreadingHTTPServer((host, port), type("BoundHandler", (Handler,), {}))
    httpd.daemon_threads = True
    actual = httpd.server_address[1]
    names = {"127.0.0.1", "localhost", "[::1]", host}
    allowed = {f"{n}:{actual}" for n in names} | {n for n in names}
    allowed |= {h.lower() for h in (extra_hosts or [])}
    httpd.RequestHandlerClass.monitor = monitor
    httpd.RequestHandlerClass.allowed_hosts = set() if "*" in (extra_hosts or []) else allowed
    return httpd


def main(argv: list[str] | None = None) -> int:
    default_repo = os.path.dirname(MONITOR_ROOT)
    p = argparse.ArgumentParser(description="Live read-only monitor for dlp-research")
    p.add_argument("--repo", default=default_repo, help="git repository root (default: parent of research-monitor)")
    p.add_argument("--research-dir", default="dlp-research", help="research directory relative to --repo")
    p.add_argument("--manifest", default=os.path.join(MONITOR_ROOT, "manifest.json"))
    p.add_argument("--host", default="127.0.0.1", help="bind address (default loopback only)")
    p.add_argument("--port", type=int, default=8765, help="port; 0 picks a free port")
    p.add_argument("--interval", type=float, default=5.0, help="poll interval seconds")
    p.add_argument("--allow-host", action="append", default=[],
                   help="extra Host header value to accept (e.g. a preview proxy name); '*' disables the check")
    p.add_argument("--pid-file", help="write the server PID here after binding (removed on exit)")
    args = p.parse_args(argv)
    repo = os.path.realpath(args.repo)
    research_root = os.path.join(repo, args.research_dir)
    mon = Monitor(research_root, repo, args.manifest, args.research_dir, interval=max(1.0, args.interval))
    mon.start()
    httpd = make_server(mon, args.host, args.port, args.allow_host)
    if args.pid_file:
        with open(args.pid_file, "w") as fh:
            fh.write(f"{os.getpid()}\n")
    print(f"research-monitor serving http://{args.host}:{httpd.server_address[1]}/ "
          f"(research={research_root}, poll={mon.interval}s)", flush=True)
    import signal
    signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(KeyboardInterrupt))
    try:
        httpd.serve_forever(poll_interval=0.5)
    except KeyboardInterrupt:
        pass
    finally:
        mon.stop()
        httpd.server_close()
        if args.pid_file:
            try:
                os.remove(args.pid_file)
            except OSError:
                pass
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
