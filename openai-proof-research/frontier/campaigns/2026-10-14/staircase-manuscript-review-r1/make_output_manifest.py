#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang, no affiliation. MIT License.
"""List bytes and SHA-256 of every file in this review directory except the manifest itself."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
files = []
for p in sorted(HERE.iterdir()):
    if p.is_file() and p.name != "output-manifest.json":
        data = p.read_bytes()
        files.append({"path": p.name, "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()})
print(json.dumps({"directory": "frontier/campaigns/2026-10-14/staircase-manuscript-review-r1",
                  "author": "Myeongjin Kang", "affiliation": None,
                  "license": {"prose": "CC BY 4.0", "code": "MIT"},
                  "verdict": "PASS (full manuscript); final-package conditions F1-F2; no count change",
                  "files": files}, indent=1))
