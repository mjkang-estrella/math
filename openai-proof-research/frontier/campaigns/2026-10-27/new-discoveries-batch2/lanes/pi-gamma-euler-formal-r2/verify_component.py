#!/usr/bin/env python3
"""Fresh replay of the pi-gamma-euler-formal-r2 component in a clean temp dir.

Copies the lane sources to a new temporary directory and recompiles everything
from source with the pinned Lean 4.34.1 / Mathlib d13f23b toolchain via
run_lean.py (absolute pinned package paths).  Then reruns the type/axiom audit.
"""
import hashlib
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

LANE = Path(__file__).resolve().parent
FORMAL = LANE / "formal"
FILES = ["GammaDefs.lean", "GammaEuler.lean", "GammaRatio.lean", "Checks.lean", "run_lean.py"]


def sha256(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main() -> int:
    ok = True
    hashes = {f: sha256(FORMAL / f) for f in FILES}
    print("source hashes:")
    for f, h in hashes.items():
        print(f"  {f}  sha256 {h}")
    with tempfile.TemporaryDirectory(prefix="gammaeuler-replay-") as tmp:
        tmp = Path(tmp)
        for f in FILES:
            shutil.copy(FORMAL / f, tmp / f)
        order = ["GammaDefs.lean", "GammaEuler.lean", "GammaRatio.lean"]
        for mod in order:
            olean = mod[:-5] + ".olean"
            r = subprocess.run(
                [sys.executable, str(tmp / "run_lean.py"), mod, "-o", olean],
                cwd=tmp, capture_output=True, text=True,
            )
            print(f"--- compile {mod} (exit {r.returncode})")
            if r.stdout.strip():
                print(r.stdout.strip())
            if r.stderr.strip():
                print(r.stderr.strip())
            if r.returncode != 0:
                ok = False
        r = subprocess.run(
            [sys.executable, str(tmp / "run_lean.py"), "Checks.lean"],
            cwd=tmp, capture_output=True, text=True,
        )
        out = r.stdout + r.stderr
        print(f"--- audit Checks.lean (exit {r.returncode})")
        print(out)
        if r.returncode != 0:
            ok = False
        if "error" in out:
            ok = False
        for decl in ["finite_sum_eq_logGammaSeq", "tendsto_logGammaSeq_mix",
                     "tendsto_partialSum_logDefect", "seriesTerm_nonneg",
                     "gammaHasSum", "gammaHasSum'", "logDefect_shift",
                     "logDefect_eq_log_iff_ratio", "sourceLevel_iff_defect"]:
            marker = f"'GammaLevel.{decl}' depends on axioms:"
            if marker not in out:
                print(f"MISSING axiom report for {decl}")
                ok = False
        banned = ["sorry", "admit", "'sorryAx'", "native_decide"]
        for b in banned:
            if b in out:
                print(f"BANNED token {b} in audit output")
                ok = False
    print("REPLAY:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
