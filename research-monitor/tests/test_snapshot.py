import os
import unittest

from monitor import gitinfo, snapshot
from tests.fixture import Fixture, write


class SnapshotTests(unittest.TestCase):
    def setUp(self):
        self.fx = Fixture()

    def tearDown(self):
        self.fx.close()

    def build(self):
        return snapshot.build_snapshot(self.fx.research, self.fx.repo, self.fx.manifest, "dlp-research")

    def test_state_phase_headline_and_audits(self):
        s = self.build()
        self.assertEqual(s["warnings"], [])
        self.assertEqual(s["state"]["phase"], "active, fixture phase after toy milestone")
        self.assertIn("No faster ECDLP algorithm or cryptographic break has been discovered.", s["state"]["headline_sentences"])
        self.assertIn("Complete solver costs remain unproved.", s["state"]["headline_sentences"])
        self.assertEqual(s["state"]["current_live_work"][0], "Writer A owns Research/Toy.lean; no query code.")
        self.assertEqual(s["audit"]["count"], 3)
        self.assertEqual(s["audit"]["claimed_in_state"], 3)
        self.assertTrue(any("blocked" in t for t in s["state"]["open_sentences"]))

    def test_findings_status_hints_and_commits(self):
        s = self.build()
        (w,) = s["findings"]
        self.assertEqual(w["id"], "W001")
        self.assertEqual(w["status"], "independently reviewed finite experiment; no speedup.")
        cats = {h["category"]: h["matched"] for h in w["hints"]}
        self.assertEqual(cats["experiment"], "experiment")
        self.assertEqual(cats["reviewed"], "independently reviewed")
        self.assertIn("no-speedup", cats)
        self.assertEqual(len(w["commits"]), 1)
        self.assertFalse(w["uncommitted"])
        self.assertEqual(s["results"][0]["table"]["rows"][0]["q"], 7)

    def test_verdict_line_and_proposal_fallback(self):
        write(self.fx.path("research/findings/W020-x.md"), "# W020: data\n\nVerdict: **verified limited result**, independently reviewed.\nDate: 2026.\n")
        write(self.fx.path("research/findings/W018-results.json"), '{"scope": "graph review"}')
        write(self.fx.path("research/proposals/W018-graphs.md"), "# W018: graph design\n\nStatus: frozen for review.\n")
        by = {f["id"]: f for f in self.build()["findings"]}
        self.assertEqual(by["W020"]["status"], "**verified limited result**, independently reviewed. Date: 2026.")
        self.assertEqual(by["W020"]["status_from"], "Verdict line")
        self.assertEqual(by["W018"]["title"], "W018: graph design")
        self.assertEqual(by["W018"]["primary"], "research/proposals/W018-graphs.md")
        self.assertIn("proposal", by["W018"]["status_from"])

    def test_negated_keywords_are_not_hints(self):
        hints = snapshot.classify_status("W019: report. This is not an accepted mathematical, experimental or performance finding.")
        self.assertNotIn("experiment", [h["category"] for h in hints])
        self.assertEqual(snapshot.classify_status("plain words")[0:0], [])

    def test_unaccepted_is_pending_not_rejected(self):
        cats = [h["category"] for h in snapshot.classify_status("W019: report — UNACCEPTED pending audit")]
        self.assertIn("pending", cats)
        self.assertNotIn("rejected", cats)

    def test_uncommitted_and_new_commit_are_reflected(self):
        write(self.fx.path("research/findings/W002-new.md"), "# W002: new\n\nStatus: design proposal in progress.\n")
        s = self.build()
        w2 = [f for f in s["findings"] if f["id"] == "W002"][0]
        self.assertTrue(w2["uncommitted"])
        self.assertIn({"path": "research/findings/W002-new.md", "state": "untracked"}, s["repo"]["working_tree"])
        self.assertEqual(s["manifest"]["findings_newer_than_manifest"], ["W002"])
        self.fx.commit("research: add W002")
        s = self.build()
        self.assertEqual(s["repo"]["working_tree"], [])
        self.assertEqual(s["commits"][0]["subject"], "research: add W002")
        self.assertEqual(s["commits"][0]["finding_ids"], ["W002"])

    def test_manifest_evidence_is_rechecked(self):
        s = self.build()
        by_id = {r["id"]: r["verification"] for r in s["repo_results"]}
        self.assertTrue(by_id["good"]["ok"])
        self.assertFalse(by_id["stale"]["ok"])
        self.assertFalse(by_id["stale"]["quote_found"])
        self.assertEqual(by_id["stale"]["theorems_missing"], ["Research.Nope.missing"])
        self.assertEqual(by_id["stale"]["findings_missing"], ["W999"])

    def test_complexity_from_live_order(self):
        c = self.build()["complexity"]
        self.assertEqual(c["order_bits"], 256)
        rho = c["references"][0]["log2_ops"]
        self.assertAlmostEqual(rho, 127.825, places=2)  # SafeCurves lists 2^127.8
        self.assertAlmostEqual(c["references"][1]["log2_ops"], 256.0, places=6)


class CorruptAndMissingTests(unittest.TestCase):
    def setUp(self):
        self.fx = Fixture()

    def tearDown(self):
        self.fx.close()

    def build(self, repo=None):
        return snapshot.build_snapshot(self.fx.research, repo or self.fx.repo, self.fx.manifest, "dlp-research")

    def test_missing_state_and_audit(self):
        os.remove(self.fx.path("research/STATE.md"))
        os.remove(self.fx.path("Audit.lean"))
        s = self.build()
        self.assertIsNone(s["state"])
        self.assertIsNone(s["audit"]["count"])
        self.assertTrue(any("STATE.md" in w for w in s["warnings"]))
        self.assertTrue(any("Audit.lean" in w for w in s["warnings"]))

    def test_malformed_json_and_binary_markdown(self):
        write(self.fx.path("research/findings/W003-bad.json"), '{"rows": [1, 2')
        with open(self.fx.path("research/findings/W004-bin.md"), "wb") as fh:
            fh.write(b"\xff\xfe\x00garbage\x00\n# not title\n" + os.urandom(256))
        write(self.fx.path("research/findings/W005-empty.md"), "")
        s = self.build()
        self.assertTrue(any("W003-bad.json: malformed JSON" in w for w in s["warnings"]))
        ids = [f["id"] for f in s["findings"]]
        self.assertIn("W004", ids)
        self.assertIn("W005", ids)
        empty = [f for f in s["findings"] if f["id"] == "W005"][0]
        self.assertEqual(empty["hints"][0]["category"], "unclassified")

    def test_corrupt_manifest(self):
        write(self.fx.manifest, "{not json")
        s = self.build()
        self.assertTrue(any("manifest unreadable" in w for w in s["warnings"]))
        self.assertEqual(s["repo_results"], [])

    def test_not_a_git_repo(self):
        import tempfile
        with tempfile.TemporaryDirectory() as empty:
            s = self.build(repo=empty)
        self.assertEqual(s["commits"], [])
        self.assertTrue(any(w.startswith("git log failed") for w in s["warnings"]))
        self.assertEqual(s["findings"][0]["id"], "W001")

    def test_missing_research_dir(self):
        s = snapshot.build_snapshot(os.path.join(self.fx.repo, "nope"), self.fx.repo, self.fx.manifest, "nope")
        self.assertTrue(any("research directory missing" in w for w in s["warnings"]))
        self.assertEqual(s["findings"], [])


class GitParsingTests(unittest.TestCase):
    def test_parse_log_ignores_garbage(self):
        good = "\x1e" + "\x1f".join(["a" * 40, "aaaaaaa", "2026-10-07T00:00:00+00:00", "2026-10-07T00:00:00+00:00", "x", "subj", "body"]) + "\x1f\nresearch/findings/W007-x.md\n"
        bad = "\x1enot-a-hash\x1fz"
        commits = gitinfo.parse_log(good + bad)
        self.assertEqual(len(commits), 1)
        self.assertEqual(commits[0].finding_ids, ["W007"])

    def test_parse_status(self):
        out = gitinfo.parse_status("?? a b.md\x00 M c.lean\x00garbage\x00")
        self.assertEqual(out, [{"code": "??", "state": "untracked", "path": "a b.md"}, {"code": " M", "state": "modified", "path": "c.lean"}])

    def test_show_commit_rejects_non_hash(self):
        self.assertFalse(gitinfo.show_commit("/", "HEAD; rm -rf /")["ok"])
        self.assertFalse(gitinfo.show_commit("/", "--output=/tmp/x")["ok"])


if __name__ == "__main__":
    unittest.main()
