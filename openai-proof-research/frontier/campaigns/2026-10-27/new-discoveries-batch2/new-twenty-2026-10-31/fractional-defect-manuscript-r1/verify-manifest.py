#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parent
m=json.loads((root/'manifest.json').read_text())
for name,receipt in m.items():
 p=root/name
 assert p.is_file(),name
 assert p.stat().st_size==receipt['bytes'],name
 assert hashlib.sha256(p.read_bytes()).hexdigest()==receipt['sha256'],name
print(f'PASS: {len(m)} dossier members match manifest (manifest itself excluded).')
