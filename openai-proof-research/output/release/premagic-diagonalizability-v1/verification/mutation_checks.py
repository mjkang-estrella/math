#!/usr/bin/env python3
"""Require Lean to reject two deliberately broken counterexample certificates."""
import argparse
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path, required=True)
    parser.add_argument("--mathlib-packages", type=Path, required=True)
    args = parser.parse_args()
    source = (ROOT / "formal/Premagic.lean").read_text()
    mutations = {
        "changed_matrix_entry": ("!![4, 4, 1; 2, 2, 5; 3, 3, 3]", "!![4, 4, 2; 2, 2, 5; 3, 3, 3]"),
        "false_row_sum": ("(∑ j, M K i j) = 9", "(∑ j, M K i j) = 8"),
    }
    out = ROOT / "build/mutations"
    out.mkdir(parents=True, exist_ok=True)
    libs = sorted(args.mathlib_packages.resolve().glob("*/.lake/build/lib/lean"))
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, libs)))
    results = []
    for name, (before, after) in mutations.items():
        if source.count(before) != 1:
            raise SystemExit(f"Mutation anchor is not unique: {name}")
        target = out / (name + ".lean")
        target.write_text(source.replace(before, after))
        run = subprocess.run([str(args.lean_bin.resolve()), str(target)],
                             env=env, capture_output=True, text=True)
        log = run.stdout + run.stderr
        (out / (name + ".log")).write_text(log)
        rejected = run.returncode != 0 and "error:" in log
        if "unknown module" in log or "object file" in log:
            rejected = False
        results.append({"mutation": name, "exit_code": run.returncode,
                        "rejected_by_Lean": rejected})
    receipt = {"status": "PASS" if all(r["rejected_by_Lean"] for r in results) else "FAIL",
               "mutations": results}
    (ROOT / "build/mutation-checks.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))
    if receipt["status"] != "PASS":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
