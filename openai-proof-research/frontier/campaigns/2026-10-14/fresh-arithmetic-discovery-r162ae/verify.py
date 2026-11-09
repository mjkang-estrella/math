#!/usr/bin/env python3
"""Read-only integrity check; explicit external anchors are required. Not a math gate."""
import argparse, hashlib, json
from pathlib import Path, PurePosixPath

def digest(b):
    return hashlib.sha256(b).hexdigest()

def verify(root, anchors):
    root = Path(root)
    for name in ('FINAL.md', 'MANIFEST.json', 'REPORT.md'):
        p = root / name
        if p.is_symlink() or digest(p.read_bytes()) != anchors[name]:
            raise ValueError('detached anchor mismatch: ' + name)
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    entries = manifest['files']
    listed = set()
    total = 0
    for e in entries:
        name = e['path']
        rel = PurePosixPath(name)
        if rel.is_absolute() or '..' in rel.parts or str(rel) != name or name in listed:
            raise ValueError('unsafe/duplicate manifest path')
        listed.add(name)
        p = root / name
        if any(q.is_symlink() for q in (p, *p.parents)):
            raise ValueError('symlink: ' + name)
        b = p.read_bytes()
        if len(b) != e['bytes'] or digest(b) != e['sha256']:
            raise ValueError('manifest mismatch: ' + name)
        total += len(b)
    outside = {'MANIFEST.json', 'REPORT.md', 'ANCHORS.json'}
    actual = set()
    for p in root.rglob('*'):
        if p.is_symlink():
            raise ValueError('unexpected symlink')
        if p.is_file():
            actual.add(p.relative_to(root).as_posix())
    if actual - outside != listed:
        raise ValueError('exact file membership mismatch')
    auth = root / 'packet/private/canonical-authentication.json'
    canonical = 0
    if auth.exists():
        for e in json.loads(auth.read_text()):
            b = (root / 'packet/private/canonical' / e['path']).read_bytes()
            g = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
            if len(b) != e['bytes'] or digest(b) != e['sha256'] or g != e['git_blob']:
                raise ValueError('canonical binding mismatch')
            canonical += 1
    return {'selected_files': len(entries), 'selected_bytes': total,
            'canonical_blobs': canonical, 'anchors': 'all three match',
            'scope': 'artifact integrity only; no mathematical gate'}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--final-sha256', required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--report-sha256', required=True)
    a = parser.parse_args()
    anchors = {'FINAL.md': a.final_sha256, 'MANIFEST.json': a.manifest_sha256,
               'REPORT.md': a.report_sha256}
    print(json.dumps(verify(a.root, anchors), sort_keys=True))

if __name__ == '__main__':
    main()
