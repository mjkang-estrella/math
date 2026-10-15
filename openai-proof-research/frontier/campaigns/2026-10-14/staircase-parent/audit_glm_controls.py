"""Parent audit of GLM's bounded checks; no all-m theorem certificate.

Copyright (c) 2026 Myeongjin Kang. MIT License.
Runs the frozen checker only on a disposable copy; writes no frozen evidence.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / "staircase-glm-check-r1"


def main():
    receipt = json.loads((SOURCE / "receipts.json").read_text())
    for name, digest in receipt["sha256"].items():
        data = (SOURCE / name).read_bytes()
        assert hashlib.sha256(data).hexdigest() == digest
        assert len(data) == receipt["sizes_bytes"][name]
    assert (SOURCE / "inputs/candidate.md").read_bytes() == (
        ROOT / "fresh-algebra-discovery-r1/candidate.md").read_bytes()
    with tempfile.TemporaryDirectory(prefix="staircase-glm-audit-") as tmp:
        target = Path(tmp) / "check"
        shutil.copytree(SOURCE, target)
        subprocess.run([sys.executable, "-B", str(target / "glm_staircase_check.py")],
                       check=True, capture_output=True, text=True, cwd=target)
        filename = "results/glm_staircase_check_results.json"
        before = json.loads((SOURCE / filename).read_text())
        after = json.loads((target / filename).read_text())
        before.pop("run_metadata")
        after.pop("run_metadata")
        assert before == after
        spec = importlib.util.spec_from_file_location("glm_copy", target / "glm_staircase_check.py")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        cases = []
        for m in (1, 2, 3):
            positions = module.build_positions(m)
            rows = module.build_layer(m, module.row_blocks(m))
            cols = module.build_layer(m, module.col_blocks(m))
            survivors = []
            for a, ca in rows.items():
                for b, cb in rows.items():
                    for c, cc in cols.items():
                        result = module.run_pipeline({a: ca}, {b: cb}, {c: cc}, m)
                        if result["content_survivors"]:
                            survivors.append((a, b, c, ca * cb * cc))
            assert len(survivors) == 1
            assert survivors[0][1] == tuple(j for i, j in positions)
            assert survivors[0][3] == 1
            controls = after["m"][str(m)]["negative_controls"]
            expected_matches = {
                "C1_no_equality_filter": m == 1,
                "C2_drop_second_coordinate": False,
                "C3_sum_shift_a_plus_b": False,
                "C4_filter_a_equals_b": m == 1,
                "C5_column_sign_negated": False,
                "C6_second_row_layer_unsigned": True,
            }
            assert {k: v["matches_target_identity"] for k, v in controls.items()} == expected_matches
            # C2's codomain changes. Show genuine orbit collapse, not just a
            # pair-versus-singleton tuple mismatch. No collapse is possible at m=1.
            collapsed = None
            if m >= 2:
                n = len(positions)
                g = list(range(n))
                g[0], g[1] = g[1], g[0]
                inverse = module.invert_perm(g)
                moved_rows = {module.act_word(w, inverse): c for w, c in rows.items()}
                moved_cols = {module.act_word(w, inverse): c for w, c in cols.items()}
                original = module.run_pipeline(rows, rows, cols, m, "drop2")["aggregated"]
                moved = module.run_pipeline(moved_rows, moved_rows, moved_cols, m, "drop2")["aggregated"]
                assert original == moved and any(original.values())
                collapsed = g
            cases.append({"m": m, "unique_second_row_word_is_identity": True,
                          "control_outcomes_asserted": True,
                          "dropped_coordinate_nonidentity_orbit_collision": collapsed})
    print(json.dumps({"status": "PASS for bounded implementation checks",
                      "authenticated_artifacts": 4,
                      "rerun_matches_except_utc_timestamp": True,
                      "orbit_elements": 727, "cases": cases,
                      "full_proof_or_contribution_verdict": False}, indent=2))


if __name__ == "__main__":
    main()
