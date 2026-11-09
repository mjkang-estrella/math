import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from random import Random
from unittest.mock import patch

from factoring_lab.algorithms import ALGORITHMS
from factoring_lab.core import BudgetExceeded, Meter, valid_factor
from factoring_lab.corpus import FAMILIES, generate, is_prime, make_case
from factoring_lab.runner import ROOT, iterate, run_one, summary_text, validate_config, verify_run
from factoring_lab.worker import evaluate


class CorrectnessTests(unittest.TestCase):
    def test_checker_rejects_invalid_witnesses(self):
        for d in (None, True, False, 0, 1, -3, 15, 30, 2, 3.0, "3"):
            self.assertFalse(valid_factor(15, d), repr(d))
        self.assertTrue(valid_factor(15, 3))

    def test_deterministic_baselines_exhaustive(self):
        for name in ("trial", "fermat"):
            for n in range(300):
                d = ALGORITHMS[name](n, Random(0), Meter(100_000))
                if n >= 4 and not is_prime(n):
                    self.assertTrue(valid_factor(n, d), (name, n, d))
                else:
                    self.assertIsNone(d, (name, n, d))

    def test_rho_all_small_composites_multiple_seeds(self):
        for n in range(4, 300):
            if not is_prime(n):
                for seed in (0, 1, 17):
                    d = ALGORITHMS["rho"](n, Random(seed), Meter(100_000))
                    self.assertTrue(valid_factor(n, d), (n, seed, d))

    def test_budget_is_not_reset_between_restarts(self):
        result = evaluate({"algorithm": "rho", "n": 97, "seed": 1,
                           "max_events": 100, "max_operand_bits": 4096})
        self.assertEqual(result["status"], "event_budget")
        self.assertEqual(result["total_events"], 100)
        self.assertIsNone(result["factor"])

    def test_width_limit(self):
        with self.assertRaises(BudgetExceeded):
            Meter(max_operand_bits=8).mul(255, 255)

    def test_corpus_exact_and_reproducible(self):
        for bits in (12, 16, 24, 28):
            for family in FAMILIES:
                a = make_case(bits, family, 42, 0)
                self.assertEqual(a, make_case(bits, family, 42, 0))
                p, q = a["factors"]
                self.assertEqual(a["n"], p * q)
                self.assertEqual(a["n"].bit_length(), bits)
                self.assertTrue(is_prime(p) and is_prime(q))
                if family == "square":
                    self.assertEqual(p, q)
                if family == "balanced":
                    self.assertGreaterEqual(q - p, 1 << max(1, bits // 2 - 3))

    def test_config_rejects_bad_limits(self):
        config = json.loads((ROOT / "configs/smoke.json").read_text())
        for field, value in (("total_seconds", float("nan")), ("timeout_seconds", 0),
                             ("max_events", -1), ("bits", [2048]), ("algorithm_seeds", [1, 1])):
            bad = {**config, field: value}
            with self.assertRaises(ValueError, msg=field):
                validate_config(bad)

    def test_real_subprocess_timeout(self):
        result = run_one("rho", 2147483647, 11,
                         {"max_events": 10**9, "max_operand_bits": 4096}, 0.02)
        self.assertEqual(result["status"], "timeout")
        self.assertLess(result["process_seconds"], 2)

    def test_parent_rechecks_worker_witness(self):
        fake = subprocess.CompletedProcess([], 0, json.dumps({"status": "success", "factor": 7}), "")
        with patch("factoring_lab.runner.subprocess.run", return_value=fake):
            result = run_one("rho", 15, 11, {"max_events": 10, "max_operand_bits": 100}, 1)
        self.assertEqual(result["status"], "invalid")

    def test_report_retains_failed_trials(self):
        rows = [{"family": "balanced", "bits": 16, "algorithm": "rho", "composite": True,
                 "status": "success", "total_events": 40},
                {"family": "balanced", "bits": 16, "algorithm": "rho", "composite": True,
                 "status": "timeout"}]
        text = summary_text(rows)
        self.assertIn("1/2", text)
        self.assertIn("timeout:1", text)
        self.assertIn("selection-biased", text)

    def test_roundtrip_artifacts_and_tamper_detection(self):
        config = json.loads((ROOT / "configs/smoke.json").read_text())
        config.update(bits=[12], families=["balanced"], algorithms=["trial"],
                      algorithm_seeds=[11], include_controls=False)
        with tempfile.TemporaryDirectory() as tmp:
            tmp = Path(tmp)
            cfg = tmp / "config.json"
            cfg.write_text(json.dumps(config))
            run = iterate(cfg, "H001", tmp / "run")
            verify_run(run)
            row = json.loads((run / "results.jsonl").read_text())
            self.assertEqual(row["status"], "success")
            self.assertNotIn("factors", row)
            self.assertTrue((run / "source/Factoring/Contract.lean").is_file())
            with self.assertRaises(FileExistsError):
                iterate(cfg, "H001", run)
            with (run / "results.jsonl").open("a") as stream:
                stream.write("{}\n")
            with self.assertRaisesRegex(ValueError, "hash mismatch"):
                verify_run(run)

    def test_unregistered_idea_cannot_run(self):
        with self.assertRaisesRegex(ValueError, "Status: preregistered"):
            iterate(ROOT / "configs/smoke.json", "H002")


if __name__ == "__main__":
    unittest.main()
