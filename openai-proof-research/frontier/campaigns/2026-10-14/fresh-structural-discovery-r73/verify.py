#!/usr/bin/env python3
"""Integrity only; requires an externally supplied manifest digest and canonical tree."""
import argparse, hashlib, json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--anchor',required=True);p.add_argument('--tree',type=Path,required=True);a=p.parse_args()
r=Path(__file__).resolve().parent
h=lambda b:hashlib.sha256(b).hexdigest()
def require(ok, reason):
    if not ok: raise SystemExit(reason)
m=r/'MANIFEST.json'
require(h(m.read_bytes())==a.anchor,'MANIFEST_ANCHOR')
d=json.loads(m.read_text())
actual={str(x.relative_to(r)) for x in r.rglob('*') if x.is_file() and x!=m}
require(actual==set(d),'EXACT_MEMBERSHIP')
for name,v in d.items():
    b=(r/name).read_bytes();require(h(b)==v['sha256'] and len(b)==v['bytes'],'PAYLOAD_HASH:'+name)
tb=a.tree.read_bytes();require(h(tb)=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b','TREE_ANCHOR')
t=json.loads(tb);require(len(t['tree'])==13223 and not t.get('truncated',False),'TREE_COMPLETENESS')
entries={x['path']:x for x in t['tree']}
s=json.loads((r/'source299-receipts.json').read_text())
require(s['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','SOURCE_PIN')
for v in s['sources']:
    b=(r/'private'/v['path']).read_bytes()
    git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
    require(entries[v['path']]['sha']==git==v['git_blob'] and h(b)==v['sha256'] and len(b)==v['bytes'],'CANONICAL_BLOB:'+v['path'])
for v in json.loads((r/'private/primary/receipt.json').read_text()):
    for ext,key in [('pdf','pdf_sha256'),('txt','text_sha256')]:
        require(h((r/'private/primary'/(v['name']+'.'+ext)).read_bytes())==v[key],'PRIMARY_RECEIPT')
print(json.dumps({'status':'PASS','payloads':len(d),'canonical_blobs':len(s['sources']),'tree_entries':len(t['tree']),'meaning':'integrity only; not mathematical or contribution review'}))
