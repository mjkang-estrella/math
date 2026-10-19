#!/usr/bin/env python3
"""Read-only verifier. Usage: python3 -B tools/verify.py <manifest-sha256> [--controls]

Checks, without writing anything:
1. SHA-256 of MANIFEST.json equals the externally supplied anchor;
2. every manifest entry matches on disk, and no unlisted public file exists;
3. every private upstream copy matches its pinned git blob id and SHA-256;
4. the private CCO24 copy matches primary-identities.json;
5. optionally, tools/controls.py passes (run with -B, no bytecode written)."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
errors = []


def sha256(b):
    return hashlib.sha256(b).hexdigest()


def git_blob(b):
    return hashlib.sha1(b"blob %d\0" % len(b) + b).hexdigest()


if len(sys.argv) < 2:
    sys.exit(__doc__)
anchor = sys.argv[1].strip().lower()

manifest_bytes = (ROOT / "MANIFEST.json").read_bytes()
if sha256(manifest_bytes) != anchor:
    errors.append("MANIFEST.json does not match the external anchor")
manifest = json.loads(manifest_bytes)

listed = set()
for e in manifest["files"]:
    listed.add(e["path"])
    p = ROOT / e["path"]
    if not p.is_file():
        errors.append(f"missing {e['path']}")
        continue
    data = p.read_bytes()
    if len(data) != e["size"] or sha256(data) != e["sha256"]:
        errors.append(f"hash mismatch {e['path']}")

for p in ROOT.rglob("*"):
    rel = p.relative_to(ROOT).as_posix()
    if (p.is_file() and not rel.startswith("private/") and "__pycache__" not in rel
            and rel not in listed and rel not in {"MANIFEST.json", "MANIFEST.sha256"}):
        errors.append(f"unlisted file {rel}")

for r in json.loads((ROOT / "source-receipts.json").read_text(encoding="utf-8")):
    data = (ROOT / r["local"]).read_bytes()
    if git_blob(data) != r["tree_blob"] or sha256(data) != r["sha256"] or r["status"] != "ok":
        errors.append(f"upstream receipt mismatch {r['path']}")

for ident in json.loads((ROOT / "primary-identities.json").read_text(encoding="utf-8")):
    if ident.get("local"):
        data = (ROOT / ident["local"]).read_bytes()
        if sha256(data) != ident["sha256"] or len(data) != ident["size"]:
            errors.append(f"primary identity mismatch {ident['id']}")

if "--controls" in sys.argv[2:]:
    rc = subprocess.run([sys.executable, "-B", str(ROOT / "tools" / "controls.py")],
                        capture_output=True, text=True).returncode
    if rc != 0:
        errors.append("controls failed")

for e in errors:
    print("FAIL", e)
print(f"verify: {'PASS' if not errors else 'FAIL'} ({len(manifest['files'])} manifest files)")
sys.exit(1 if errors else 0)
