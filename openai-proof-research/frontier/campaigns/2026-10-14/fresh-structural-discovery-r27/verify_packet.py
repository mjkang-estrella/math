#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Read-only detached-anchor identity verification; no mathematical verdict."""
from pathlib import Path
import argparse,hashlib,json,sys

def sha(b):return hashlib.sha256(b).hexdigest()
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seal-sha256',required=True);args=ap.parse_args()
    root=Path(__file__).resolve().parent
    raw=(root/'manifest.json').read_bytes()
    assert len(args.seal_sha256)==64 and sha(raw)==args.seal_sha256,'external anchor mismatch'
    obj=json.loads(raw);files=obj['files'];dirs=obj['directories']
    assert len(files)==len({x['path'] for x in files}),'duplicate inventory path'
    actual_files=set();actual_dirs=set()
    for p in root.rglob('*'):
        assert not p.is_symlink(),'symlink forbidden'
        rel=p.relative_to(root).as_posix()
        if p.is_dir():actual_dirs.add(rel)
        elif p.is_file():actual_files.add(rel)
        else:raise AssertionError('nonregular entry')
    assert actual_files=={x['path'] for x in files}|{'manifest.json'},'file membership mismatch'
    assert actual_dirs==set(dirs),'directory membership mismatch'
    for row in files:
        p=Path(row['path']);assert not p.is_absolute() and '..' not in p.parts,'unsafe path'
        b=(root/p).read_bytes();assert len(b)==row['bytes'] and sha(b)==row['sha256'],'payload mismatch: '+str(p)
    scope=sha((root/'original-scope.md').read_bytes())
    assert scope=='4f4f5103561d77dd475a5b8f50bbcd0d8989e102c18392ace80cb0b52a735984','frozen scope changed'
    receipt=json.loads((root/'source-receipt.json').read_text())
    assert receipt['pin']=='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb' and receipt['complete_tree_truncated'] is False
    assert len(receipt['files'])==7
    for row in receipt['files']:
        b=(root/row['local']).read_bytes()
        assert sha(b)==row['sha256']
        assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==row['git_blob']
    for row in json.loads((root/'private'/'primary-receipts.json').read_text()):
        b=(root/row['file']).read_bytes();assert sha(b)==row['sha256'] and len(b)==row['bytes']
    print(json.dumps({'status':'IDENTITY_ONLY_OK','payloads':len(files),'directories':len(dirs),'pinned_blobs':7,'primary_bodies':3,'scope_sha256':scope},sort_keys=True))
if __name__=='__main__':
    try:main()
    except (AssertionError,KeyError,ValueError,OSError) as e:
        print('IDENTITY_CHECK_FAILED: '+str(e),file=sys.stderr);sys.exit(1)
