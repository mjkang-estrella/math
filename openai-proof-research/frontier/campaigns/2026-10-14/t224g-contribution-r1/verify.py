#!/usr/bin/env python3
"""Read-only integrity check for the T224G contribution review r1. Not mathematics."""
import argparse, hashlib, json, sys
from pathlib import Path
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def verify(root, anchor, author=None):
    root=Path(root); raw=(root/'MANIFEST.json').read_bytes()
    if hashlib.sha256(raw).hexdigest()!=anchor: raise ValueError('external manifest anchor mismatch')
    m=json.loads(raw)
    if m.get('verdict')!='TECHNICAL' or m.get('counts')!=0 or m.get('accepts') is not False: raise ValueError('verdict/count fields altered')
    actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() and p.name!='MANIFEST.json' and '__pycache__' not in p.parts}
    if actual!=set(m['files']): raise ValueError('inventory mismatch')
    for n,h in m['files'].items():
        if sha(root/n)!=h: raise ValueError('payload hash mismatch: '+n)
    if author:
        for n,h in m['author_anchors'].items():
            if sha(Path(author)/n)!=h: raise ValueError('author anchor mismatch: '+n)
    return {'status':'PASS_INTEGRITY_ONLY','files':len(m['files']),'author_anchors_checked':bool(author)}
if __name__=='__main__':
    a=argparse.ArgumentParser(); a.add_argument('--root',default=str(Path(__file__).resolve().parent)); a.add_argument('--manifest-sha256',required=True); a.add_argument('--author-packet'); x=a.parse_args()
    try: print(json.dumps(verify(x.root,x.manifest_sha256,x.author_packet)))
    except (ValueError,KeyError,OSError) as e: sys.exit('REJECT: '+str(e))
