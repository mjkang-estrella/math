#!/usr/bin/env python3
"""Read-only byte/membership verifier. Explicit detached anchors are mandatory."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import stat

ENVELOPES = {'FINAL.md', 'MANIFEST.json', 'REPORT.md'}

def digest(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda: f.read(1024*1024), b''):
            h.update(b)
    return h.hexdigest()

def verify(root, anchors):
    if root.is_symlink() or not root.is_dir():
        raise ValueError('root is not an ordinary directory')
    actual = {}
    for directory, dirs, files in os.walk(root, followlinks=False):
        for name in dirs:
            p = Path(directory)/name
            if p.is_symlink():
                raise ValueError('directory symlink: '+str(p))
        for name in files:
            p = Path(directory)/name
            st = p.lstat()
            if not stat.S_ISREG(st.st_mode) or st.st_nlink != 1:
                raise ValueError('nonregular/symlink/multiply linked file: '+str(p))
            rel = p.relative_to(root).as_posix()
            actual[rel] = {'path': rel, 'size': st.st_size, 'sha256': digest(p)}
    for name in ENVELOPES:
        if name not in actual or actual[name]['sha256'] != anchors[name]:
            raise ValueError('detached anchor mismatch: '+name)
    manifest = json.loads((root/'MANIFEST.json').read_text(encoding='utf-8'))
    if manifest.get('excluded_envelopes') != sorted(ENVELOPES):
        raise ValueError('wrong envelope set')
    expected = {}
    for row in manifest['files']:
        rel = row['path']
        if not isinstance(rel,str) or Path(rel).is_absolute() or '..' in Path(rel).parts:
            raise ValueError('unsafe manifest path')
        if rel in expected or rel in ENVELOPES:
            raise ValueError('duplicate/envelope payload entry')
        expected[rel] = row
    payload = {k:v for k,v in actual.items() if k not in ENVELOPES}
    if payload != expected:
        raise ValueError('payload byte or exact-membership mismatch')
    return {'payload_files': len(payload), 'whole_root_files': len(actual),
            'byte_membership_match': True, 'read_only': True}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',required=True,type=Path)
    for name in ['final','manifest','report']:
        parser.add_argument('--'+name+'-sha256',required=True)
    args=parser.parse_args()
    anchors={name.upper()+'.md' if name!='manifest' else 'MANIFEST.json':
             getattr(args,name+'_sha256') for name in ['final','manifest','report']}
    try:
        print(json.dumps(verify(args.root,anchors),sort_keys=True))
    except (ValueError,OSError,KeyError,TypeError) as exc:
        parser.exit(1,'FAIL: '+str(exc)+'\n')

if __name__ == '__main__':
    main()
