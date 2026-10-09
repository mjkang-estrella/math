#!/usr/bin/env python3
"""Snapshot only the assigned i15 scope; verify immutable Git blob identities."""
import hashlib, json, shutil, datetime, re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'frontier/sources/i15_odd_order_topology'
def digest(b): return hashlib.sha256(b).hexdigest()
def dump(name,obj):
    p=OUT/name; p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(obj,indent=2)+'\n')
inputs=['AGENTS.md','sources/upstream.json','sources/CONTENTS.md','sources/preprints-tree.json',
 'frontier/iterations/i07-structures.md','frontier/reviews/i07-structures-r2.md',
 'frontier/reviews/i07-structures-novelty-r3.md',
 'frontier/sources/i07_structures/retrieval-manifest.json',
 'frontier/sources/i07_structures/theorem-contracts.json',
 'frontier/sources/i07_structures_novelty_r3/reading-index.json',
 'frontier/sources/i07_structures_novelty_r3/topology-statement-inventory.json']
records=[]
for n in inputs:
    b=(ROOT/n).read_bytes(); p=OUT/'inputs'/n; p.parent.mkdir(parents=True,exist_ok=True); p.write_bytes(b)
    records.append(dict(path=n,snapshot=str(p.relative_to(ROOT)),sha256=digest(b),bytes=len(b)))
dump('input-manifest.json',records)
t=json.loads((ROOT/'sources/preprints-tree.json').read_text()); assert not t['truncated']
idx={x['path']:x for x in t['tree']}; assert len(idx)==len(t['tree'])
ds=sorted({x['path'].split('/')[1] for x in t['tree']})
keys=('aspheric','disk-embedding','poincare','pd4','nielsen','borel','equivariant','grope','surgery')
dump('inventory-screen.json',dict(entries=len(idx),blobs=sum(x['type']=='blob' for x in idx.values()),manuscripts=len(ds),truncated=t['truncated'],keywords=keys,title_matches=[d for d in ds if any(s in d.lower() for s in keys)]))
manifest=json.loads((ROOT/'frontier/sources/i07_structures/retrieval-manifest.json').read_text())
for r in manifest:
    b=(ROOT/'frontier/sources/i07_structures/upstream'/r['path']).read_bytes()
    assert digest(b)==r['sha256'] and len(b)==r['bytes']
    git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
    assert git==idx[r['path']]['sha']; assert 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb' in r['url']
    p=OUT/'upstream'/r['path']; p.parent.mkdir(parents=True,exist_ok=True); p.write_bytes(b)
    r.update(git_blob_sha1=git,snapshot=str(p.relative_to(ROOT)))
dump('pinned-manifest.json',manifest)
literature=[]
for lane in ['i07_structures','i07_structures_novelty_r3']:
    m=ROOT/f'frontier/sources/{lane}/literature/manifest.json'
    for r in json.loads(m.read_text()):
        for ext in ['pdf','txt']:
            src=m.parent/(r['name']+'.'+ext)
            if not src.exists(): continue
            b=src.read_bytes(); expected=r['sha256' if ext=='pdf' else 'text_sha256']; assert digest(b)==expected
            p=OUT/'literature'/(r['name']+'.'+ext); p.parent.mkdir(parents=True,exist_ok=True); p.write_bytes(b)
        literature.append(dict(r,retained_from=str(m.relative_to(ROOT))))
dump('literature/retained-manifest.json',literature)
print(json.dumps(dict(inputs=len(records),pinned_files=len(manifest),literature=len(literature),inventory=len(idx))))
