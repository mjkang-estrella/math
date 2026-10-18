#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Verify the exact checkpoint inventory against an externally supplied anchor."""
import argparse,hashlib,json,pathlib,sys
ap=argparse.ArgumentParser()
ap.add_argument('--expected-manifest-sha256',required=True)
a=ap.parse_args()
p=pathlib.Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
b=(p/'manifest.json').read_bytes()
if sha(b)!=a.expected_manifest_sha256:sys.exit('REJECT: wrong external manifest anchor')
m=json.loads(b)
expected=set(m['files'])
actual={str(f.relative_to(p)) for f in p.rglob('*') if f.is_file() and f.name!='manifest.json'}
if actual!=expected:sys.exit('REJECT: exact inventory mismatch')
for name,digest in m['files'].items():
 f=p/name
 if f.is_symlink() or sha(f.read_bytes())!=digest:sys.exit('REJECT: payload '+name)
t=json.loads((p/'private/recovery-context/preprints-tree.json').read_text())
assert t['truncated'] is False and len(t['tree'])==13223
lookup={e['path']:e.get('sha') for e in t['tree']}
u=json.loads((p/'private/recovery-context/upstream.json').read_text())
assert u['commit']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
rs=json.loads((p/'source-receipts.json').read_text())
for r in rs:
 b=(p/r['local']).read_bytes()
 blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert blob==r['git_blob']==lookup[r['path']]
 assert sha(b)==r['sha256']
 assert r['url']=='https://raw.githubusercontent.com/openai/math/'+u['commit']+'/'+r['path']
rp=json.loads((p/'primary-receipts.json').read_text())
for r in rp:assert sha((p/r['local']).read_bytes())==r['sha256']
print(json.dumps({'status':'inventory_verified','payloads':len(expected),'pinned_source_blobs':len(rs),'primary_pdfs':len(rp),'scope':'bytes and provenance; no proof or contribution verdict'},sort_keys=True))
