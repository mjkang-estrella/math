"""Read-only exact-member verifier. Anchors must be supplied independently."""
import argparse, hashlib, json
from pathlib import Path, PurePosixPath

OUTSIDE = {'FINAL.md', 'MANIFEST.json', 'REPORT.md'}

def digest(data):
    return hashlib.sha256(data).hexdigest()

def verify(root, anchors):
    root = Path(root)
    if root.is_symlink() or not root.is_dir():
        raise ValueError('invalid root')
    for name in OUTSIDE:
        p = root / name
        if p.is_symlink() or not p.is_file():
            raise ValueError('missing or nonregular envelope')
        if digest(p.read_bytes()) != anchors[name]:
            raise ValueError('detached envelope mismatch: ' + name)
    obj = json.loads((root / 'MANIFEST.json').read_text())
    if obj.get('schema') != 'r157-exact-selected-members-v1':
        raise ValueError('unsupported manifest')
    records = obj['files']
    expected = {}
    for r in records:
        name = r['path']; rel = PurePosixPath(name)
        if rel.is_absolute() or any(x in ('', '.', '..') for x in name.split('/')):
            raise ValueError('unsafe manifest path')
        if name in OUTSIDE or name in expected:
            raise ValueError('duplicate or excluded manifest path')
        expected[name] = r
    actual = set()
    for p in root.rglob('*'):
        if p.is_symlink():
            raise ValueError('symlink rejected')
        if p.is_dir():
            continue
        if not p.is_file():
            raise ValueError('nonregular member rejected')
        name = p.relative_to(root).as_posix()
        if name not in OUTSIDE:
            actual.add(name)
    if actual != set(expected):
        raise ValueError('exact membership mismatch')
    for name,r in expected.items():
        data = (root / name).read_bytes()
        if len(data) != r['size'] or digest(data) != r['sha256']:
            raise ValueError('payload byte mismatch: ' + name)
    return len(expected)

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('root')
    p.add_argument('--final-sha', required=True)
    p.add_argument('--manifest-sha', required=True)
    p.add_argument('--report-sha', required=True)
    a = p.parse_args()
    anchors = {'FINAL.md': a.final_sha, 'MANIFEST.json': a.manifest_sha,
               'REPORT.md': a.report_sha}
    try:
        count = verify(a.root, anchors)
    except (OSError, ValueError, KeyError, TypeError) as e:
        raise SystemExit('REJECT: ' + str(e))
    print('VERIFIED exact payload members:', count,
          '; three detached envelope anchors; byte/membership check only')
