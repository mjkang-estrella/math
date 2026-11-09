"""Live outcome / achievements feed: derived from current sources, never hardcoded."""

import http.client
import json
import os
import threading
import time
import unittest

from monitor import live, server, snapshot
from tests.fixture import STATE, Fixture, write

os.environ["MONITOR_QUIET"] = "1"

POSITIVE_STATE = """# Research checkpoint

Status: active, post-W021 review (2026-10-09). A faster ECDLP algorithm for
secp256k1 was discovered in W021. Complete solver costs remain unproved.

## Established milestones

- `abc1234`, W001: toy baseline.
"""

NO_OUTCOME_STATE = """# Research checkpoint

Status: active, fixture phase. Writers are working on W002.

## Established Milestones

- W001: toy baseline.
"""


class OutcomeTests(unittest.TestCase):
    def setUp(self):
        self.fx = Fixture()

    def tearDown(self):
        self.fx.close()

    def build(self):
        return snapshot.build_snapshot(self.fx.research, self.fx.repo, self.fx.manifest, "dlp-research")

    def test_current_explicit_negative_is_attributed(self):
        o = self.build()["outcome"]
        self.assertEqual(o["status"], "reported_none")
        self.assertEqual(o["label"], "None reported")
        self.assertEqual(o["primary"]["text"], "No faster ECDLP algorithm or cryptographic break has been discovered.")
        self.assertEqual(o["source"], "research/STATE.md")
        self.assertIsNotNone(o["source_mtime"])

    def test_missing_state_is_unknown(self):
        os.remove(self.fx.path("research/STATE.md"))
        o = self.build()["outcome"]
        self.assertEqual(o["status"], "unknown")
        self.assertIn("not assessed", o["label"])

    def test_state_without_statement_is_unknown(self):
        write(self.fx.path("research/STATE.md"), NO_OUTCOME_STATE)
        s = self.build()
        self.assertEqual(s["outcome"]["status"], "unknown")
        self.assertEqual(s["state"]["established_milestones"], ["W001: toy baseline."])  # heading case variant

    def test_positive_headline_is_reported_not_verified(self):
        write(self.fx.path("research/STATE.md"), POSITIVE_STATE)
        o = self.build()["outcome"]
        self.assertEqual(o["status"], "reported_positive")
        self.assertIn("evidence review required", o["label"])
        self.assertNotIn("verified", json.dumps(o).lower().replace("unverified", ""))
        self.assertIn("A faster ECDLP algorithm for secp256k1 was discovered in W021.", [h["text"] for h in o["headline"]])

    def test_mixed_headline_is_conflicting(self):
        write(self.fx.path("research/STATE.md"), STATE.replace("Complete solver costs remain unproved.",
                                                               "We found a speedup over rho for secp256k1."))
        self.assertEqual(self.build()["outcome"]["status"], "conflicting")

    def test_report_style_none_in_later_section(self):
        write(self.fx.path("research/STATE.md"),
              "# Checkpoint\n\nStatus: **active, algorithm-first refocus**. Work continues.\n\n"
              "## Current result report\n\n1. Best work: generic square-root.\n"
              "2. **Verified improvement versus accepted baseline: NONE.** Toy successes are not discoveries.\n")
        o = self.build()["outcome"]
        self.assertEqual(o["status"], "reported_none")
        self.assertIn("Verified improvement versus accepted baseline: NONE.", o["primary"]["text"])

    def test_positive_finding_status_overrides_negative_state(self):
        write(self.fx.path("research/findings/W021-claim.md"), "# W021: claim\n\nStatus: a new algorithm gives a speedup over Pollard rho.\n")
        o = self.build()["outcome"]
        self.assertEqual(o["status"], "conflicting")
        self.assertEqual(o["finding_signals"][0]["id"], "W021")
        self.assertTrue(o["finding_signals"][0]["uncommitted"])

    def test_polarity_heuristic(self):
        cases = {
            "No faster ECDLP algorithm or cryptographic break has been discovered.": "negative",
            "No speedup, whole BSGS cost or cryptographic/tape/hardware result is established.": "negative",
            "Any speedup over rho remains open.": "negative",
            "This is not a speedup.": "negative",
            "W021 gives a faster solver.": "positive",
            "2. **Verified improvement versus accepted baseline: NONE.**": "negative",
            "No verified improvement over rho exists.": "negative",
            "Verified improvement: 2^10 fewer group operations.": "positive",
            "Complete solver costs remain unproved.": None,
            "Known constant-factor addition saving accompanied by sign/key costs.": None,
        }
        for text, want in cases.items():
            self.assertEqual(live.sentence_polarity(text), want, text)


class AchievementFeedTests(unittest.TestCase):
    def setUp(self):
        self.fx = Fixture()

    def tearDown(self):
        self.fx.close()

    def build(self):
        return snapshot.build_snapshot(self.fx.research, self.fx.repo, self.fx.manifest, "dlp-research")

    def test_feed_contains_state_milestones_and_findings(self):
        a = self.build()["achievements"]
        self.assertEqual(a["reported"][0]["text"], "`abc1234`, W001: toy baseline.")
        self.assertEqual(a["reported"][0]["evidence"], "reported")
        self.assertFalse(a["reported"][0]["hashes"][0]["in_git"])  # cited hash not in fixture git log
        (f,) = a["findings"]
        self.assertEqual(f["id"], "W001")
        self.assertEqual(f["review_phrase"], "independently reviewed")  # quoted from the status, not asserted by us
        self.assertTrue(f["in_reviewed_snapshot"])

    def test_appended_milestone_and_new_finding_appear_newest_first(self):
        write(self.fx.path("research/findings/w21_new-thing.md"), "# W021: new thing\n\n**Status:** design pending review.\n")
        self.fx.commit("research: add W021 design")
        head = self.fx_head()
        with open(self.fx.path("research/STATE.md"), encoding="utf-8") as fh:
            original = fh.read()
        text = original.replace(
            "- `abc1234`, W001: toy baseline.", f"- `abc1234`, W001: toy baseline.\n- `{head}`, W021: new design milestone.")
        write(self.fx.path("research/STATE.md"), text)
        a = self.build()["achievements"]
        top = a["reported"][0]
        self.assertEqual(top["text"], f"`{head}`, W021: new design milestone.")
        self.assertTrue(top["hashes"][0]["in_git"])
        self.assertEqual(top["when_basis"], "cited commit")
        self.assertEqual(a["findings"][0]["id"], "W021")  # file name variant normalized
        self.assertEqual(a["findings"][0]["status"], "design pending review.")
        self.assertTrue(a["findings"][0]["newer_than_reviewed_snapshot"])
        self.assertFalse(a["findings"][0]["in_reviewed_snapshot"])

    def fx_head(self):
        from tests.fixture import git
        return git(self.fx.repo, "rev-parse", "--short=7", "HEAD").strip()

    def test_frontend_has_no_hardcoded_outcome(self):
        here = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        with open(os.path.join(here, "static", "app.js"), encoding="utf-8") as fh:
            js = fh.read()
        self.assertNotIn('"End-to-end speedup established", "No"', js)
        self.assertIn("s.outcome", js)
        self.assertIn("achievements", js)


class LiveOverviewHttpTests(unittest.TestCase):
    def setUp(self):
        self.fx = Fixture()
        self.mon = server.Monitor(self.fx.research, self.fx.repo, self.fx.manifest, "dlp-research", interval=0.2)
        self.mon.start()
        self.httpd = server.make_server(self.mon, "127.0.0.1", 0)
        self.port = self.httpd.server_address[1]
        threading.Thread(target=self.httpd.serve_forever, kwargs={"poll_interval": 0.1}, daemon=True).start()

    def tearDown(self):
        self.mon.stop()
        self.httpd.shutdown()
        self.httpd.server_close()
        self.fx.close()

    def snap(self):
        conn = http.client.HTTPConnection("127.0.0.1", self.port, timeout=5)
        conn.request("GET", "/api/snapshot")
        data = json.loads(conn.getresponse().read())
        conn.close()
        return data["snapshot"]

    def wait_for(self, pred, timeout=8):
        deadline = time.time() + timeout
        while time.time() < deadline:
            s = self.snap()
            if pred(s):
                return s
            time.sleep(0.2)
        self.fail("condition not reached via refresh")

    def test_outcome_and_feed_follow_live_edits(self):
        self.assertEqual(self.snap()["outcome"]["status"], "reported_none")
        write(self.fx.path("research/STATE.md"), POSITIVE_STATE)
        s = self.wait_for(lambda s: s["outcome"]["status"] != "reported_none")
        self.assertEqual(s["outcome"]["status"], "reported_positive")
        os.remove(self.fx.path("research/STATE.md"))
        s = self.wait_for(lambda s: s["outcome"]["status"] == "unknown")
        self.assertEqual(s["achievements"]["reported"], [])
        write(self.fx.path("research/STATE.md"), STATE.replace("## Current validation", "- W030: appended milestone.\n\n## Current validation"))
        write(self.fx.path("research/findings/W030-x.md"), "# W030: appended\n\nStatus: finite experiment in progress.\n")
        s = self.wait_for(lambda s: any(r["text"] == "W030: appended milestone." for r in s["achievements"]["reported"]))
        self.assertEqual(s["outcome"]["status"], "reported_none")
        self.assertEqual(s["achievements"]["findings"][0]["id"], "W030")


if __name__ == "__main__":
    unittest.main()
