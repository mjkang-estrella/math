#!/usr/bin/env python3
"""MIT. Read-only, externally anchored identity check; not a proof checker."""
import argparse
import hashlib
import json
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--anchor", required=True)
args = parser.parse_args()
base = Path(__file__).resolve().parent
manifest = base / "manifest.json"
assert hashlib.sha256(manifest.read_bytes()).hexdigest() == args.anchor
records = json.loads(manifest.read_text())["files"]
names = [r["path"] for r in records]
assert len(names) == len(set(names))
actual = {str(p.relative_to(base)) for p in base.rglob("*")
          if p.is_file() and p != manifest}
assert actual == set(names), (actual - set(names), set(names) - actual)
for r in records:
    p = base / r["path"]
    assert p.resolve().is_relative_to(base.resolve()) and not p.is_symlink()
    data = p.read_bytes()
    assert len(data) == r["bytes"]
    assert hashlib.sha256(data).hexdigest() == r["sha256"], r["path"]
source = json.loads((base / "source-receipt.json").read_text())
for r in source:
    data = (base / r["local"]).read_bytes()
    assert len(data) == r["bytes"]
    assert hashlib.sha256(data).hexdigest() == r["sha256"]
    assert hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest() == r["git_blob"]
primary = json.loads((base / "primary-receipt.json").read_text())
for kind in ("pdf", "text"):
    r = primary[kind]
    assert hashlib.sha256((base / r["path"]).read_bytes()).hexdigest() == r["sha256"]
print(json.dumps({"status": "IDENTITY_ONLY", "payloads": len(records),
                  "pinned_inputs": len(source), "primary_pdfs": 1,
                  "counted": False, "frozen_target": False}))
