"""Read-only artifact verification against three REQUIRED detached SHA256 anchors."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath

def digest(data): return hashlib.sha256(data).hexdigest()

def verify(root, anchors):
    contents={}
    for name, expected in anchors.items():
        if len(expected)!=64 or any(c not in '0123456789abcdef' for c in expected):
            raise ValueError('invalid explicit SHA256 anchor: '+name)
        path=root/name
        if path.is_symlink(): raise ValueError('anchor file is a symlink: '+name)
        data=path.read_bytes()
        if digest(data)!=expected: raise ValueError('detached anchor mismatch: '+name)
        contents[name]=data
    manifest=json.loads(contents['MANIFEST.json'])
    if manifest.get('scope')!='exact packet files': raise ValueError('wrong scope')
    expected={}
    for item in manifest['files']:
        name=item['path']; rel=PurePosixPath(name)
        if rel.is_absolute() or '..' in rel.parts or not rel.parts or rel.parts[0]!='packet':
            raise ValueError('unsafe manifest path')
        if name in expected: raise ValueError('duplicate manifest path')
        expected[name]=item
    actual={}
    packet=root/'packet'
    if packet.is_symlink(): raise ValueError('packet symlink')
    for path in packet.rglob('*'):
        if path.is_symlink(): raise ValueError('packet symlink: '+str(path))
        if path.is_file(): actual[path.relative_to(root).as_posix()]=path
    if set(actual)!=set(expected): raise ValueError('exact packet file set mismatch')
    for name, path in actual.items():
        data=path.read_bytes(); item=expected[name]
        if len(data)!=item['bytes'] or digest(data)!=item['sha256']:
            raise ValueError('packet content mismatch: '+name)
    return len(actual)

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root',required=True,type=Path)
    ap.add_argument('--manifest-sha256',required=True)
    ap.add_argument('--final-sha256',required=True)
    ap.add_argument('--report-sha256',required=True)
    a=ap.parse_args()
    try:
        n=verify(a.root,{'MANIFEST.json':a.manifest_sha256,'FINAL.md':a.final_sha256,'REPORT.md':a.report_sha256})
    except (OSError,ValueError,KeyError,TypeError) as e:
        ap.exit(1,'FAIL: '+str(e)+'\n')
    print('PASS: detached anchors and exact packet bytes ('+str(n)+' files); artifact integrity only')
