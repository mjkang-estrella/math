# Author: Myeongjin Kang. No affiliation. SPDX-License-Identifier: MIT
"""Verify externally anchored exact packet inventory and source receipts."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

def sha(b): return hashlib.sha256(b).hexdigest()
def require(ok, message):
    if not ok: raise ValueError(message)
def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--expected-manifest-sha256',required=True)
    ap.add_argument('--replay',action='store_true')
    args=ap.parse_args()
    root=Path(__file__).resolve().parent
    raw=(root/'MANIFEST.json').read_bytes()
    require(sha(raw)==args.expected_manifest_sha256,'external manifest anchor mismatch')
    manifest=json.loads(raw)
    entries=manifest['files']; names=[r['path'] for r in entries]
    require(len(names)==len(set(names)),'duplicate inventory path')
    require(all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in names),'unsafe inventory path')
    actual=[]
    for p in root.rglob('*'):
        require(not p.is_symlink(),'symlink in packet')
        if p.is_file() and p!=root/'MANIFEST.json':actual.append(p.relative_to(root).as_posix())
    require(sorted(actual)==sorted(names),'exact inventory mismatch')
    for r in entries:
        b=(root/r['path']).read_bytes()
        require(len(b)==r['size'] and sha(b)==r['sha256'],'payload mismatch: '+r['path'])
    tree=json.loads((root/'private/context/sources__preprints-tree.json').read_text())
    require(tree.get('truncated') is False,'source tree truncated')
    blobs={r['path']:r['sha'] for r in tree['tree'] if r['type']=='blob'}
    pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
    source=json.loads((root/'source-receipts.json').read_text())
    for r in source:
        b=(root/r['local']).read_bytes()
        git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
        require(git==r['git_blob']==blobs[r['path']],'Git blob mismatch: '+r['path'])
        require(sha(b)==r['sha256'] and len(b)==r['size'],'source receipt mismatch')
        require(r['url']=='https://raw.githubusercontent.com/openai/math/'+pin+'/'+r['path'],'unpinned source URL')
    primary=json.loads((root/'primary-receipts.json').read_text())
    for r in primary:
        b=(root/r['path']).read_bytes()
        require(sha(b)==r['sha256'] and len(b)==r['size'],'primary receipt mismatch')
    context=json.loads((root/'context-receipts.json').read_text())
    for r in context:
        b=(root/r['local']).read_bytes()
        require(sha(b)==r['sha256'] and len(b)==r['size'],'context receipt mismatch')
    if args.replay:
        result=subprocess.run([sys.executable,'-B',str(root/'checks.py')],capture_output=True,text=True,check=True)
        require(json.loads(result.stdout)==json.loads((root/'validation.json').read_text()),'diagnostic replay mismatch')
    print(json.dumps(dict(status='PASS',payload_files=len(entries),pinned_sources=len(source),primary_bodies=len(primary),context_snapshots=len(context),replayed=args.replay,meaning='integrity and finite diagnostics only; no full theorem or priority')))
if __name__=='__main__':
    try:main()
    except Exception as e:
        print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
