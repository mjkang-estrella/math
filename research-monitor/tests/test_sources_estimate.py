import json
import math
import os
import unittest

from monitor import estimate, sources
from tests.fixture import Fixture, write


class SourceRestrictionTests(unittest.TestCase):
    def setUp(self):
        self.fx = Fixture()

    def tearDown(self):
        self.fx.close()

    def test_allowlist_shapes(self):
        ok = ["research/STATE.md", "research/findings/W001-toy.md", "research/findings/W001-results.json",
              "Research/Secp256k1.lean", "Audit.lean", "README.md", "research/proposals/archive/W011-x.md",
              "research/artifacts/W019-x.py"]
        bad = ["../secret.txt", "/etc/passwd", "research/../../secret.txt", ".git/config", "research/.hidden.md",
               "research/findings/../STATE.md", ".tools/x", "Research/x.olean", "research\\STATE.md",
               "research/findings/a..b.md", "", "research/findings/W001.md\x00.txt", "lake-manifest.json",
               "scripts/__pycache__/x.pyc", ".env"]
        for p in ok:
            self.assertTrue(sources.is_allowed(p), p)
        for p in bad:
            self.assertFalse(sources.is_allowed(p), p)

    def test_read_and_reject(self):
        f = sources.read_source(self.fx.research, "research/findings/W001-toy.md")
        self.assertIn("<script>", f.text)  # served verbatim as data; UI renders as text
        with self.assertRaises(sources.SourceError) as ctx:
            sources.read_source(self.fx.research, "../secret.txt")
        self.assertEqual(ctx.exception.status, 403)
        with self.assertRaises(sources.SourceError) as ctx:
            sources.read_source(self.fx.research, "research/findings/W404-missing.md")
        self.assertEqual(ctx.exception.status, 404)

    def test_symlink_escape_rejected(self):
        link = self.fx.path("research/findings/W009-link.md")
        os.symlink(os.path.join(self.fx.repo, "secret.txt"), link)
        with self.assertRaises(sources.SourceError):
            sources.read_source(self.fx.research, "research/findings/W009-link.md")
        self.assertNotIn("research/findings/W009-link.md", sources.list_sources(self.fx.research))

    def test_symlinked_directory_rejected(self):
        outside = os.path.join(self.fx.repo, "outside")
        os.makedirs(outside)
        write(os.path.join(outside, "W010-x.md"), "secret")
        os.rename(self.fx.path("Research"), self.fx.path("Research.bak"))
        os.symlink(outside, self.fx.path("Research"))
        write(os.path.join(outside, "Evil.lean"), "secret")
        with self.assertRaises(sources.SourceError):
            sources.read_source(self.fx.research, "Research/Evil.lean")

    def test_truncation_cap(self):
        write(self.fx.path("research/findings/W011-big.txt"), "x" * 5000)
        f = sources.read_source(self.fx.research, "research/findings/W011-big.txt", max_bytes=1000)
        self.assertTrue(f.truncated)
        self.assertEqual(len(f.text), 1000)
        self.assertEqual(f.size, 5000)

    def test_listing_excludes_unlisted(self):
        write(self.fx.path("research/findings/notes.docx"), "x")
        listed = sources.list_sources(self.fx.research)
        self.assertIn("research/STATE.md", listed)
        self.assertNotIn("research/findings/notes.docx", listed)
        self.assertFalse(any(p.startswith(".git") for p in listed))


class EstimateTests(unittest.TestCase):
    def test_reference_values(self):
        one = estimate.estimate(estimate.work_log10(log2_work=128), 1, 19.3e9)
        self.assertEqual(one["years"], "5.59e+20")
        self.assertEqual(one["gpu_years"], "5.59e+20")
        self.assertAlmostEqual(10 ** (one["log10_years"] - 20), 5.587, places=2)
        million = estimate.estimate(estimate.work_log10(log2_work=128), 1e6, 19.3e9)
        self.assertEqual(million["years"], "5.59e+14")
        self.assertEqual(million["gpu_years"], "5.59e+20")  # GPU-years independent of count
        self.assertEqual(million["seconds"], "1.76e+22")

    def test_sci_and_log2_agree(self):
        a = estimate.work_log10(log2_work=128)
        b = estimate.work_log10(sci_work=2.0 ** 128)
        self.assertAlmostEqual(a, b, places=12)

    def test_huge_work_no_overflow(self):
        r = estimate.estimate(estimate.work_log10(log2_work=4096), 1, 1)
        self.assertTrue(math.isfinite(r["log10_years"]))
        self.assertTrue(r["years"].endswith("e+1225"))

    def test_rounding_carry(self):
        self.assertEqual(estimate.sci(math.log10(9.9996)), "1.00e+1")

    def test_invalid(self):
        for kwargs in ({"log2_work": -1}, {"log2_work": float("nan")}, {"sci_work": 0.5}, {}):
            with self.assertRaises(estimate.EstimateError):
                estimate.work_log10(**kwargs)
        for g, r in ((0, 1), (1, 0), (-1, 1), (float("inf"), 1)):
            with self.assertRaises(estimate.EstimateError):
                estimate.estimate(10, g, r)


if __name__ == "__main__":
    unittest.main()


class ManifestHardwareTests(unittest.TestCase):
    """The live manifest must not invent H200/B200 benchmarks or a research improvement."""

    def setUp(self):
        here = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        with open(os.path.join(here, "manifest.json"), encoding="utf-8") as fh:
            self.est = json.load(fh)["estimator"]

    def test_unbenchmarked_hardware_has_no_rate(self):
        hw = {h["id"]: h for h in self.est["hardware"]}
        for gid in ("h200", "b200"):
            self.assertIs(hw[gid]["benchmarked"], False)
            self.assertIsNone(hw[gid]["ops_per_sec"])
            self.assertTrue(hw[gid]["source"]["url"].startswith("https://docs.nvidia.com/"))
        ref = hw[self.est["reference_hardware"]]
        self.assertIs(ref["benchmarked"], True)
        self.assertEqual(ref["ops_per_sec"], 19.3e9)
        self.assertEqual(ref["ops_per_sec"], self.est["default_ops_per_sec_per_gpu"])

    def test_reference_numbers_and_flat_current_result(self):
        self.assertIsNone(self.est["current_result"])
        self.assertIn(1000000, self.est["gpu_presets"])
        self.assertIn(100, self.est["speed_multipliers"])
        lw = estimate.work_log10(log2_work=self.est["default_log2_work"])
        self.assertEqual(estimate.estimate(lw, 1e6, 19.3e9 * 100)["years"], "5.59e+12")
        self.assertEqual(estimate.estimate(lw, 1e6, 19.3e9)["years"], "5.59e+14")
