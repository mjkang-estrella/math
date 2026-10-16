#!/usr/bin/env python3
"""Verify the review seal and recheck frozen input integrity, without writes.

Original review code: copyright 2026 Myeongjin Kang, MIT license.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
manifest = json.loads((ROOT / "output-manifest.json").read_text())
assert manifest["verdict"] == "PASS"
assert manifest["gate"] == "first_independent_full_proof_only"
expected_names = {r["path"] for r in manifest["files"]}
actual_names = {str(p.relative_to(ROOT)) for p in ROOT.rglob("*") if p.is_file()
                and p.name not in {"output-manifest.json", "SHA256SUMS"}}
assert actual_names == expected_names
for r in manifest["files"]:
    b = (ROOT / r["path"]).read_bytes()
    assert len(b) == r["bytes"]
    assert hashlib.sha256(b).hexdigest() == r["sha256"]
for line in (ROOT / "SHA256SUMS").read_text().splitlines():
    sha, name = line.split(maxsplit=1)
    assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == sha
checked = subprocess.run([sys.executable, "-B", str(ROOT / "audit_inputs.py")],
                         check=True, capture_output=True, text=True)
assert json.loads(checked.stdout) == json.loads((ROOT / "input-audit.json").read_text())
controls = json.loads((ROOT / "independent-controls.json").read_text())
assert controls["status"] == "PASS"
assert sum(r["permutations"] for r in controls["orbit_cases"]) == 727
print(json.dumps({"review_seal": "PASS", "frozen_inputs": "PASS",
                  "review_files": len(expected_names), "proof_gate": manifest["verdict"]},
                 sort_keys=True))
