#!/usr/bin/env python3
"""Read-only integrity check of the T224G proof-review packet. Integrity is not mathematics."""
import argparse, hashlib, json
from pathlib import Path
AUTHOR={'MANIFEST.json':'0011c7f5be653b7479c8701a69b2cfeb026246072fba299559a978ec6bd0aef8',
'scope-status.json':'ab52a8e5ed90a18ca5871b6d74ed8b88e1439803ef6e3fd23ccb553c0c7ef2e4',
'candidate-proof.md':'6ae5388f38f83abcbbe0397ed3e40a3ba6875a0d997ccf17df444b4234e742d3',
'author-assembly-status.json':'8715210720d3f85a352ad84768e9f29846757ea446f7cd7485f4d0b462b51b3d',
'bulk-kernel-and-boundary.md':'2d4d60d062d93496a84dc7bae446c6b2c5486719ac21c2877bac6732c7c01386',
'generator-and-history-majorant.md':'74e785d42d56b0246e388cc2a49c7ce647de72981892a0bb7c263f66aa85a1a7',
'single-jump-replacement.md':'a8d22058010edb9247c435fedb3bcac76060589325ea7d28475ae5407daeb9f6',
'fixed-coefficient-replacement.md':'c88ee95f5d6dd644baaf3f8a1ef37b3be59ca2de28d8ed0c7d1d9c336a869c85',
'path-series-tightness.md':'077ec932ed73415d0d5e0de3dc92250e3db1d42854dac0a281f13427f468a1e9',
'comparison-and-dependencies.md':'885e49a15ed133dcabb9e722fc7420a2265a6a204392f492fad8034579e90f4c',
'reading-limits.md':'78bde178f5290bb09d0fb1f91c216b8fd30bd8b07d4c8c31885cc1950da12854'}
TREE='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(c,r):
    if not c:raise ValueError(r)
def verify(root,anchor,author=None,tree=None):
    need(sha(root/'MANIFEST.json')==anchor,'external review manifest anchor mismatch')
    m=json.loads((root/'MANIFEST.json').read_text());files=m['files']
    actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() and p.name!='MANIFEST.json' and '__pycache__' not in p.parts}
    need(actual==set(files),'review inventory mismatch')
    for n,h in files.items():
        need('..' not in Path(n).parts and not Path(n).is_absolute(),'unsafe path')
        need(sha(root/n)==h,'review payload hash mismatch: '+n)
    s=json.loads((root/'review-status.json').read_text())
    need(s['counted'] is False and s['accepted'] is False and s['count_change']==0,'count/acceptance forbidden')
    need(s['verdict']=='PASS_FULL_T224G_AFTER_REQUIRED_REPAIR_R1' and s['frozen_author_text']=='NEEDS_REVISION_R1','verdict field altered')
    need(s['scope_sha256']==AUTHOR['scope-status.json'] and s['author_manifest_sha256']==AUTHOR['MANIFEST.json'],'author anchor in status altered')
    if author:
        for n,h in AUTHOR.items():need(sha(Path(author)/n)==h,'author anchor mismatch: '+n)
    if tree:need(sha(tree)==TREE,'canonical tree anchor mismatch')
    return {'status':'PASS_REVIEW_INTEGRITY_ONLY','payloads':len(files),'author_anchors_checked':bool(author),'canonical_tree_checked':bool(tree),'mathematics_verified_by_script':False}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=Path(__file__).resolve().parent)
    p.add_argument('--manifest-sha256',required=True);p.add_argument('--author-root');p.add_argument('--canonical-tree');a=p.parse_args()
    try:print(json.dumps(verify(a.root,a.manifest_sha256,a.author_root,a.canonical_tree),indent=2,sort_keys=True))
    except (ValueError,KeyError,OSError) as e:raise SystemExit('REJECT: '+str(e))
