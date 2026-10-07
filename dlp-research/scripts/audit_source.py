"""Conservative lexical screen. False positives in comments are intentional.

This catches common accidental proof escapes; it is not an adversarial checker.
Imported code, changed statements, and kernel integrity require separate review.
"""
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parents[1]
sources = [root / "Research.lean", root / "Main.lean", *sorted((root / "Research").rglob("*.lean"))]
for path in sources:
    source = path.read_text()
    forbidden = re.search(r"\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b|skipKernelTC|decide\s*\+native", source)
    if forbidden:
        sys.exit(f"Source review required: {path.relative_to(root)} contains {forbidden.group()!r}")
print(f"Source screen passed ({len(sources)} files).")
