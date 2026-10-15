#!/usr/bin/env python3
"""Verify publication-copy equivalence against the frozen reviewed sources."""
from pathlib import Path
import json
import difflib

p = Path(__file__).resolve().parent
reviewed = p.parent / "p-gradient-manuscript"
a = (reviewed / "main.tex").read_text()
b = (p / "main.tex").read_text()
assert (p / "metadata-only.diff").read_text() == "".join(difflib.unified_diff(
    a.splitlines(True), b.splitlines(True),
    fromfile="reviewed/main.tex", tofile="publication/main.tex"))
for item in json.loads((p / "editorial-replacements.json").read_text()):
    assert b.count(item["publication"]) == 1
    b = b.replace(item["publication"], item["reviewed"])
marker = r"\section{Statement and inputs}"
assert a[a.index(marker):] == b[b.index(marker):]
files = []
for f in sorted(reviewed.glob("*.tex")):
    if f.name != "main.tex":
        assert f.read_bytes() == (p / f.name).read_bytes()
        files.append(f.name)
print(json.dumps({"status": "PASS", "unchanged_proof_sources": files,
    "body_after_exact_editorial_reversal": "byte-identical",
    "scope": "Editorial equivalence, not a new mathematical proof audit"}, indent=2))
