#!/usr/bin/env python3
# Original code MIT; Myeongjin Kang, no affiliation.
import argparse, hashlib, json
from pathlib import Path

def digest(b): return hashlib.sha256(b).hexdigest()
def verify(root, anchor):
    b=(root/'output-manifest.json').read_bytes()
    assert digest(b)==anchor, 'external anchor mismatch'
    manifest=json.loads(b)
    paths=list(root.rglob('*'))
    assert not any(p.is_symlink() for p in paths), 'symlink'
    files={str(p.relative_to(root)) for p in paths if p.is_file()}
    dirs={str(p.relative_to(root)) for p in paths if p.is_dir()}
    assert files==set(manifest['files'])|{'output-manifest.json'}, 'file membership'
    assert dirs==set(manifest['directories']), 'directory membership'
    for name,sha in manifest['files'].items():
        assert digest((root/name).read_bytes())==sha, 'file hash: '+name
    count=0
    for receipt in ['source168-receipt.json','source131-receipt.json']:
        data=json.loads((root/receipt).read_text())
        assert data['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
        for entry in data['files']:
            b=(root/entry['local']).read_bytes()
            assert digest(b)==entry['sha256']
            assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==entry['git_blob']
            count+=1
    return {'status':'PASS_INTEGRITY_ONLY','payload_files':len(manifest['files']),'directories':len(dirs),'pinned_blobs':count}
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--anchor',required=True);ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);a=ap.parse_args()
    try: print(json.dumps(verify(a.root,a.anchor),sort_keys=True))
    except Exception as e: print('FAIL: '+str(e));raise SystemExit(1)
