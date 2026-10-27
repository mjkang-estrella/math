#!/usr/bin/env python3
"""Own-authored Lean runner for the pi-sendov-selection-formal lane.

Sets LEAN_PATH so that files in this directory compile against the pinned Mathlib
checkout of the 2026-10-14 campaign, plus the current directory itself (so that
ConvexWeights.lean can import a previously built Selection.olean).

Pinned binary : /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean
Pinned Mathlib: openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
                (mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612)

Usage (from any cwd):
    python3 run_lean.py [extra lean flags] File.lean
e.g.
    python3 run_lean.py -DwarningAsError=true Selection.lean
"""
import os
import subprocess
import sys
from pathlib import Path

LEAN = Path("/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean")
HERE = Path(__file__).resolve().parent
PACKAGES = Path(
    "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/"
    "2026-10-14/formal/.lake/packages"
)

env = dict(os.environ)
lean_paths = [str(HERE)] + sorted(
    str(p / ".lake" / "build" / "lib" / "lean")
    for p in PACKAGES.iterdir()
    if (p / ".lake" / "build" / "lib" / "lean").is_dir()
)
env["LEAN_PATH"] = ":".join(lean_paths)
raise SystemExit(subprocess.run([str(LEAN), *sys.argv[1:]], env=env).returncode)
