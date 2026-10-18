#!/usr/bin/env python3
"""MIT. Write MANIFEST.json for a review directory. Never run on an authenticated sealed copy."""
import hashlib, json, sys
from pathlib import Path


def seal(root):
    root = Path(root)
    files, dirs = [], ['.']
    for p in sorted(root.rglob('*')):
        rel = p.relative_to(root).as_posix()
        if p.is_symlink():
            raise ValueError('symlink: ' + rel)
        if p.is_dir():
            dirs.append(rel)
        elif rel != 'MANIFEST.json':
            b = p.read_bytes()
            files.append({'path': rel, 'bytes': len(b), 'sha256': hashlib.sha256(b).hexdigest()})
    m = {'directory': 'frontier/campaigns/2026-10-14/t197h-proof-r1', 'files': files,
         'directories': sorted(dirs),
         'note': 'Anchor must be supplied externally; identity only.'}
    (root / 'MANIFEST.json').write_text(json.dumps(m, indent=2) + '\n')
    return hashlib.sha256((root / 'MANIFEST.json').read_bytes()).hexdigest()


if __name__ == '__main__':
    print(seal(sys.argv[1]))
