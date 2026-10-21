#!/usr/bin/env python3
"""Read-only exact membership and SHA256 checker. No writes or network calls."""
import argparse, hashlib, json, os
from pathlib import Path

ENVELOPES = {'FINAL.md', 'MANIFEST.json', 'REPORT.md'}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def verify(root, anchors):
    root = Path(root)
    if root.is_symlink() or not root.is_dir():
        raise ValueError('root must be a real directory')
    for name in ENVELOPES:
        p = root / name
        if p.is_symlink() or not p.is_file():
            raise ValueError('missing/nonregular envelope: ' + name)
        if sha(p) != anchors[name]:
            raise ValueError('detached anchor mismatch: ' + name)
    m = json.loads((root/'MANIFEST.json').read_text())
    if m.get('schema') != 'r144-exact-payload-v1':
        raise ValueError('wrong manifest schema')
    records = m['files']
    expected = {}
    for e in records:
        s = e['path']
        p = Path(s)
        if (p.is_absolute() or '..' in p.parts or str(p) != s
                or s in ENVELOPES or s in expected):
            raise ValueError('invalid/duplicate payload name')
        expected[s] = e
    actual = set()
    for base, dirs, files in os.walk(root, followlinks=False):
        for n in dirs:
            if (Path(base)/n).is_symlink():
                raise ValueError('symlink directory')
        for n in files:
            p = Path(base)/n
            if p.is_symlink() or not p.is_file():
                raise ValueError('nonregular file')
            s = p.relative_to(root).as_posix()
            if s not in ENVELOPES:
                actual.add(s)
    if actual != set(expected):
        raise ValueError('exact payload membership mismatch')
    for s,e in expected.items():
        p = root/s
        if p.stat().st_size != e['size'] or sha(p) != e['sha256']:
            raise ValueError('payload mismatch: '+s)
    return len(expected)

if __name__ == '__main__':
    a=argparse.ArgumentParser(description=__doc__)
    a.add_argument('root', type=Path)
    a.add_argument('--final', required=True)
    a.add_argument('--manifest', required=True)
    a.add_argument('--report', required=True)
    args=a.parse_args()
    try:
        count=verify(args.root, {'FINAL.md':args.final,
            'MANIFEST.json':args.manifest,'REPORT.md':args.report})
        print(json.dumps({'integrity':'matched','payload_files':count,
                          'envelopes':3,'mathematical_gate':False}))
    except Exception as e:
        a.exit(1, str(e)+'\n')
