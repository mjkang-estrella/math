#!/usr/bin/env python3
"""Verify frozen review records without resealing. Copyright 2026 Myeongjin Kang; MIT."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parent
for name in ['input-manifest.json','output-manifest.json']:
 m=json.loads((H/name).read_text());root=Path(m['root']) if 'root' in m else H
 for r in m['files']:
  b=(root/r['path']).read_bytes()
  assert len(b)==r['bytes'] and hashlib.sha256(b).hexdigest()==r['sha256'],r['path']
 print('PASS',name,len(m['files']),'hash/size records')
for name in ['authentication.json','controls-receipt.json','support-checks.json']:
 assert json.loads((H/name).read_text())['status']=='PASS',name
assert json.loads((H/'build-receipt.json').read_text())['status'].startswith('PASS')
assert json.loads((H/'verdict.json').read_text())['verdict']=='PASS_SCOPED_SUPPORT'
print('PASS independent formal review evidence; no manifest was rewritten')
