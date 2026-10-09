#!/usr/bin/env python3
"""One-time I38 artifact seal. Refuses to overwrite an existing seal."""
import datetime
import json
from pathlib import Path
from audit import ROOT, S, sha

E = Path(__file__).resolve().parent
REPORT = ROOT/'frontier/iterations/i38-inequality-stability-discovery.md'
destination = S/'artifact-seal.json'
assert not destination.exists(), 'Seal already exists: never regenerate it during verification'
paths = [REPORT]+list(S.rglob('*'))+list(E.rglob('*'))
files = []
for p in sorted(paths):
    if not p.is_file() or '__pycache__' in p.parts or p == E/'verification.json':
        continue
    data = p.read_bytes()
    files.append({'path':str(p.relative_to(ROOT)),'bytes':len(data),'sha256':sha(data)})
destination.write_text(json.dumps({'schema':'i38-artifact-seal-v1','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Report and all I38-owned immutable artifacts, including ignored downloaded caches. Seal excludes itself and generated verification.json. External corpus identities are bound through external-dependencies.json and checked against the complete tree.','accepted_count_change':False,'files':files},indent=2)+'\n')
print(json.dumps({'sealed_files':len(files),'seal_sha256':sha(destination.read_bytes())},indent=2))
