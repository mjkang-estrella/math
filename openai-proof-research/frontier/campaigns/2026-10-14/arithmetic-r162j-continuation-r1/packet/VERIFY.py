#!/usr/bin/env python3
"""Read-only exact-packet verifier. Supply detached anchors explicitly."""
import argparse,hashlib,json
from pathlib import Path
p=argparse.ArgumentParser()
p.add_argument('--packet',required=True)
p.add_argument('--report',required=True)
p.add_argument('--final-sha256',required=True)
p.add_argument('--manifest-sha256',required=True)
p.add_argument('--report-sha256',required=True)
a=p.parse_args();root=Path(a.packet).resolve();report=Path(a.report).resolve()
def digest(path):
 if path.is_symlink():raise SystemExit('Symlink rejected: '+str(path))
 return hashlib.sha256(path.read_bytes()).hexdigest()
for path,want in [(root/'FINAL.md',a.final_sha256),(root/'MANIFEST.json',a.manifest_sha256),(report,a.report_sha256)]:
 if digest(path)!=want:raise SystemExit('Detached anchor mismatch: '+str(path))
m=json.loads((root/'MANIFEST.json').read_text());expected=set()
for e in m['files']:
 rel=e['path'];q=root/rel
 if Path(rel).is_absolute() or '..' in Path(rel).parts:raise SystemExit('Unsafe manifest path')
 if rel in expected:raise SystemExit('Duplicate manifest path')
 expected.add(rel)
 if not q.is_file() or q.stat().st_size!=e['size'] or digest(q)!=e['sha256']:raise SystemExit('Packet mismatch: '+rel)
actual=set()
for q in root.rglob('*'):
 if q.is_symlink():raise SystemExit('Symlink rejected: '+str(q))
 if q.is_file() and q!=root/'MANIFEST.json':actual.add(q.relative_to(root).as_posix())
if actual!=expected:raise SystemExit('Exact inventory mismatch')
print(json.dumps({'artifact_verification':'passed','files':len(expected),'detached_anchors':'FINAL/MANIFEST/outside REPORT','writes':0,'mathematical_gate':False}))
