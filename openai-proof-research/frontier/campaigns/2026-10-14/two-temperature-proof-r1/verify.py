#!/usr/bin/env python3
"""Read-only review package byte check. Original code MIT; not a proof checker."""
import argparse, hashlib, json
from pathlib import Path, PurePosixPath
parser=argparse.ArgumentParser();parser.add_argument('--anchor',required=True);args=parser.parse_args()
r=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
s=(r/'seal.json').read_bytes();assert sha(s)==args.anchor,'seal anchor'
m=(r/'manifest.json').read_bytes();assert sha(m)==json.loads(s)['manifest_sha256'],'manifest'
entries=json.loads(m)['files'];names=set()
for x in entries:
 n=x['path'];p=PurePosixPath(n)
 assert not p.is_absolute() and '..' not in p.parts and str(p)==n and n not in names
 names.add(n)
assert not any(p.is_symlink() or p.is_dir() for p in r.iterdir()),'unexpected directory or symlink'
assert {p.name for p in r.iterdir()}==names|{'manifest.json','seal.json'},'membership'
for x in entries:
 b=(r/x['path']).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'],x['path']
print(json.dumps({'integrity':'PASS','payload_files':len(entries),'scope':'byte integrity only; read report for mathematical verdict'}))
