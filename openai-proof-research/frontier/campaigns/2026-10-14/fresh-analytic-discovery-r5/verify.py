#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT license.
"""Read-only authentication before replay. Never creates manifests or receipts."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys


def digest(path):
    data=path.read_bytes()
    return {'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}


def main():
    root=Path(__file__).resolve().parent
    seal=json.loads((root/'seal.json').read_text())
    for name,want in seal['inventories'].items():
        assert digest(root/name)==want, 'inventory authentication failed: '+name
    inventories=[]
    for name in ['input-manifest.json','output-manifest.json']:
        obj=json.loads((root/name).read_text())
        inventories.append(obj)
        for name,want in obj['files'].items():
            path=root/name
            assert not path.is_symlink(), 'symlink not permitted: '+name
            assert path.is_file(), 'missing file: '+name
            assert digest(path)==want, 'content authentication failed: '+name
    expected=set().union(*(set(x['files']) for x in inventories))
    expected.update(['input-manifest.json','output-manifest.json','seal.json'])
    actual={str(f.relative_to(root)) for f in root.rglob('*') if f.is_file()}
    assert actual==expected, 'inventory membership mismatch: '+str(sorted(actual^expected))
    # No check runs until both inventories, every input/output and the stored
    # receipt itself have been authenticated. Code cannot reseal evidence.
    replay=subprocess.run([sys.executable,'-B',str(root/'checks.py')],cwd=root,
                          stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
    assert not replay.stderr, 'unexpected checker stderr'
    assert replay.stdout==(root/'check-receipt.json').read_bytes(), 'receipt replay mismatch'
    print(json.dumps({'authentication':'PASS','read_only':True,
                      'receipt_replay':'PASS','files_authenticated':len(expected)-3,
                      'target_B':'UNRESOLVED','substantial_complete_theorem':False},
                     indent=2,sort_keys=True))


if __name__=='__main__':
    try:
        main()
    except Exception as error:
        print('VERIFICATION FAILED: '+str(error),file=sys.stderr)
        sys.exit(1)
