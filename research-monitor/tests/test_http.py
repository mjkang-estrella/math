"""End-to-end tests of the real HTTP server against a temporary fixture repo."""

import http.client
import json
import os
import socket
import threading
import time
import unittest

from monitor import server
from tests.fixture import Fixture, write

os.environ["MONITOR_QUIET"] = "1"


class HttpTests(unittest.TestCase):
    def setUp(self):
        self.fx = Fixture()
        self.mon = server.Monitor(self.fx.research, self.fx.repo, self.fx.manifest, "dlp-research", interval=0.3)
        self.mon.start()
        self.httpd = server.make_server(self.mon, "127.0.0.1", 0)
        self.port = self.httpd.server_address[1]
        self.thread = threading.Thread(target=self.httpd.serve_forever, kwargs={"poll_interval": 0.1}, daemon=True)
        self.thread.start()

    def tearDown(self):
        self.mon.stop()
        self.httpd.shutdown()
        self.httpd.server_close()
        self.fx.close()

    def get(self, path, headers=None, method="GET"):
        conn = http.client.HTTPConnection("127.0.0.1", self.port, timeout=5)
        conn.request(method, path, headers=headers or {})
        resp = conn.getresponse()
        body = resp.read()
        conn.close()
        return resp, body

    def test_index_and_security_headers(self):
        resp, body = self.get("/")
        self.assertEqual(resp.status, 200)
        self.assertIn(b"ECDLP research monitor", body)
        csp = resp.getheader("Content-Security-Policy")
        self.assertIn("script-src 'self'", csp)
        self.assertNotIn("unsafe-inline", csp)
        self.assertEqual(resp.getheader("X-Content-Type-Options"), "nosniff")
        for path in ("/app.js", "/estimator.js", "/style.css"):
            self.assertEqual(self.get(path)[0].status, 200, path)

    def test_snapshot_endpoint(self):
        resp, body = self.get("/api/snapshot")
        self.assertEqual(resp.status, 200)
        data = json.loads(body)
        self.assertTrue(data["meta"]["last_poll_ok"])
        self.assertEqual(data["snapshot"]["findings"][0]["id"], "W001")
        self.assertEqual(data["snapshot"]["state"]["phase"], "active, fixture phase after toy milestone")

    def test_source_endpoint_and_restrictions(self):
        resp, body = self.get("/api/source?path=research/findings/W001-toy.md")
        self.assertEqual(resp.status, 200)
        self.assertTrue(resp.getheader("Content-Type").startswith("application/json"))
        self.assertIn("<script>", json.loads(body)["text"])
        for bad in ("../secret.txt", "%2e%2e/secret.txt", "/etc/passwd", ".git/HEAD", ".git/config",
                    "research/findings/..%2F..%2Fsecret.txt", "Research/../../secret.txt"):
            resp, body = self.get("/api/source?path=" + bad)
            self.assertIn(resp.status, (403, 404), bad)
            self.assertNotIn(b"TOP SECRET", body)
        resp, _ = self.get("/../secret.txt")
        self.assertEqual(resp.status, 404)
        resp, _ = self.get("/static/../monitor/server.py")
        self.assertEqual(resp.status, 404)

    def test_commit_endpoint(self):
        snap = json.loads(self.get("/api/snapshot")[1])["snapshot"]
        short = snap["commits"][0]["short"]
        resp, body = self.get("/api/commit?hash=" + short)
        self.assertEqual(resp.status, 200)
        self.assertEqual(json.loads(body)["subject"], "research: establish toy baseline")
        self.assertEqual(self.get("/api/commit?hash=HEAD")[0].status, 404)
        self.assertEqual(self.get("/api/commit?hash=deadbeef")[0].status, 404)

    def test_estimate_endpoint(self):
        body = json.loads(self.get("/api/estimate?log2_work=128&gpus=1000000&rate=19.3e9")[1])
        self.assertEqual(body["years"], "5.59e+14")
        self.assertEqual(self.get("/api/estimate?log2_work=128&gpus=0&rate=1")[0].status, 400)
        self.assertEqual(self.get("/api/estimate?log2_work=abc&gpus=1&rate=1")[0].status, 400)

    def test_host_header_and_methods(self):
        self.assertEqual(self.get("/api/status", headers={"Host": "evil.example"})[0].status, 421)
        self.assertEqual(self.get("/api/status", headers={"Host": f"localhost:{self.port}"})[0].status, 200)
        self.assertEqual(self.get("/api/status", method="POST")[0].status, 405)
        self.assertEqual(self.get("/nope")[0].status, 404)

    def test_live_refresh_via_sse(self):
        sock = socket.create_connection(("127.0.0.1", self.port), timeout=10)
        sock.sendall(f"GET /api/events HTTP/1.1\r\nHost: 127.0.0.1:{self.port}\r\n\r\n".encode())
        buf = b""

        def read_event(name, deadline):
            nonlocal buf
            while time.time() < deadline:
                while b"\n\n" in buf:
                    block, buf = buf.split(b"\n\n", 1)
                    lines = block.decode().splitlines()
                    if f"event: {name}" in lines:
                        return json.loads([ln for ln in lines if ln.startswith("data: ")][0][6:])
                chunk = sock.recv(4096)
                if not chunk:
                    break
                buf += chunk
            self.fail(f"no {name} event")

        first = read_event("snapshot", time.time() + 5)
        beat = read_event("heartbeat", time.time() + 5)
        self.assertEqual(beat["version"], first["version"])
        self.assertEqual(beat["instance"], self.mon.instance)
        self.assertTrue(beat["last_poll_ok"])

        # A new finding appears (uncommitted) — no restart.
        write(self.fx.path("research/findings/W002-live.md"), "# W002: live\n\nStatus: experiment pending.\n")
        second = read_event("snapshot", time.time() + 8)
        self.assertGreater(second["version"], first["version"])
        snap = json.loads(self.get("/api/snapshot")[1])["snapshot"]
        self.assertIn("W002", [f["id"] for f in snap["findings"]])
        self.assertTrue([f for f in snap["findings"] if f["id"] == "W002"][0]["uncommitted"])

        # Then it is committed: timeline updates.
        self.fx.commit("research: record W002 live finding")
        read_event("snapshot", time.time() + 8)
        snap = json.loads(self.get("/api/snapshot")[1])["snapshot"]
        self.assertEqual(snap["commits"][0]["subject"], "research: record W002 live finding")
        self.assertEqual(snap["repo"]["working_tree"], [])
        sock.close()

    def test_poll_failure_keeps_last_snapshot(self):
        good = json.loads(self.get("/api/snapshot")[1])["snapshot"]
        self.mon.repo_root = os.path.join(self.fx.repo, "missing")
        self.mon.poll_once()
        data = json.loads(self.get("/api/snapshot")[1])
        self.assertFalse(data["meta"]["last_poll_ok"])
        self.assertIn("git rev-parse failed", data["meta"]["last_poll_error"])
        self.assertEqual(data["snapshot"]["findings"], good["findings"])


if __name__ == "__main__":
    unittest.main()


class MainViewMarkupTests(unittest.TestCase):
    """The default view is the answer + visual; process detail lives in a collapsed drawer."""

    def setUp(self):
        here = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        with open(os.path.join(here, "static", "index.html"), encoding="utf-8") as fh:
            self.html = fh.read()
        with open(os.path.join(here, "static", "app.js"), encoding="utf-8") as fh:
            self.js = fh.read()

    def test_answer_first_and_evidence_collapsed(self):
        drawer = self.html.index('<details id="evidence-all"')
        self.assertNotIn("open", self.html[drawer:self.html.index(">", drawer)])
        main_part = self.html[:drawer]
        for needed in ('id="verdict"', 'id="big-time"', 'id="scale"', 'id="gpus"', 'id="hw"', 'id="compare"', "Logarithmic scale"):
            self.assertIn(needed, main_part)
        for detail in ('id="findings-body"', 'id="timeline-body"', 'id="achievements-body"', 'id="evidence-body"', 'id="sources-body"'):
            self.assertNotIn(detail, main_part)
            self.assertIn(detail, self.html[drawer:])
        self.assertNotIn("<progress", self.html)

    def test_frontend_derives_status_from_live_outcome(self):
        self.assertIn("E.comparison(c, s.outcome)", self.js)
        self.assertNotRegex(self.js, r"\.innerHTML\s*=|insertAdjacentHTML|outerHTML\s*=")
