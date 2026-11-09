"""Read-only verification of this packet with three explicit detached anchors."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def files(root):
    found={}
    for directory,dirs,names in os.walk(root,followlinks=False):
        for name in dirs+names:
            if (Path(directory)/name).is_symlink():
                raise ValueError('symlink in packet')
        for name in names:
            path=Path(directory)/name
            found[path.relative_to(root).as_posix()]=path
    return found


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--root',required=True)
    for name in ['final','manifest','report']:
        parser.add_argument('--'+name+'-sha256',required=True)
    args=parser.parse_args()
    root=Path(args.root).resolve(strict=True)
    for name,relative in [('final','private/FINAL.md'),('manifest','private/MANIFEST.json'),('report','REPORT.md')]:
        anchor=getattr(args,name+'_sha256')
        if len(anchor)!=64 or any(c not in '0123456789abcdef' for c in anchor):
            raise ValueError('invalid explicit anchor')
        if digest(root/relative)!=anchor:
            raise ValueError(name+' detached anchor mismatch')
    manifest=json.loads((root/'private/MANIFEST.json').read_text())
    entries=manifest['files']
    listed={}
    for entry in entries:
        rel=entry['path']
        p=PurePosixPath(rel)
        if p.is_absolute() or '..' in p.parts or p.as_posix()!=rel or rel in listed:
            raise ValueError('unsafe or duplicate manifest entry')
        listed[rel]=entry
    actual=files(root)
    expected=set(actual)-{'private/MANIFEST.json','REPORT.md'}
    if set(listed)!=expected:
        raise ValueError('payload membership mismatch')
    for rel,entry in listed.items():
        if actual[rel].stat().st_size!=entry['bytes'] or digest(actual[rel])!=entry['sha256']:
            raise ValueError('payload mismatch: '+rel)
    controls=root/'private/controls'
    anchor=json.loads((controls/'expected.json').read_text())['sha256']
    if digest(controls/'original.txt')!=anchor or digest(controls/'copy-good.txt')!=anchor:
        raise ValueError('positive copied control failed')
    if digest(controls/'copy-bad.txt')==anchor:
        raise ValueError('negative copied control failed')
    print(json.dumps({'artifact_integrity_only':True,'payload_files':len(entries),
                      'payload_bytes':sum(x['bytes'] for x in entries),
                      'positive_copy_matches':True,'altered_copy_rejected':True,
                      'mathematical_gate':False},sort_keys=True))

if __name__=='__main__':
    main()
