#!/usr/bin/env python3
"""Write MANIFEST.json (SHA-256 of every archive file except the manifest,
its detached hash and private/) and MANIFEST.sha256."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXCLUDE = {"MANIFEST.json", "MANIFEST.sha256"}

entries = []
for p in sorted(ROOT.rglob("*")):
    rel = p.relative_to(ROOT).as_posix()
    if not p.is_file() or rel in EXCLUDE or rel.startswith("private/") or "__pycache__" in rel:
        continue
    data = p.read_bytes()
    entries.append({"path": rel, "size": len(data), "sha256": hashlib.sha256(data).hexdigest()})

manifest = json.dumps({"archive": "fresh-arithmetic-discovery-r72-recovery-r4", "files": entries},
                      indent=1, ensure_ascii=False) + "\n"
(ROOT / "MANIFEST.json").write_text(manifest, encoding="utf-8")
digest = hashlib.sha256(manifest.encode("utf-8")).hexdigest()
(ROOT / "MANIFEST.sha256").write_text(f"{digest}  MANIFEST.json\n", encoding="utf-8")
print(digest)
