"""Read-only artifact verification; requires three detached SHA256 anchors."""
import argparse
import hashlib
import json
from pathlib import Path

def digest(data):
    return hashlib.sha256(data).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--final', required=True)
    parser.add_argument('--manifest', required=True)
    parser.add_argument('--report', required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    for name, expected in [('FINAL.md', args.final), ('MANIFEST.json', args.manifest), ('REPORT.md', args.report)]:
        if len(expected) != 64 or any(c not in '0123456789abcdef' for c in expected):
            raise SystemExit('Invalid explicit anchor: ' + name)
        if digest((root / name).read_bytes()) != expected:
            raise SystemExit('Detached anchor mismatch: ' + name)
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    seen = set()
    for item in manifest['files']:
        rel = item['path']
        path = root / rel
        if rel in seen or Path(rel).is_absolute() or '..' in Path(rel).parts or path.is_symlink():
            raise SystemExit('Invalid or duplicate manifest path')
        if not path.resolve().is_relative_to(root):
            raise SystemExit('Manifest path leaves own root')
        seen.add(rel)
        data = path.read_bytes()
        if len(data) != item['bytes'] or digest(data) != item['sha256']:
            raise SystemExit('Selected artifact mismatch: ' + rel)
    copy = (root / 'packet/private/control-copy.txt').read_bytes()
    changed = (root / 'packet/private/control-changed.txt').read_bytes()
    original_excerpt = (root / 'packet/private/scope.md').read_bytes()[:96]
    if copy != original_excerpt or digest(copy) != digest(original_excerpt):
        raise SystemExit('Copied own-text positive control failed')
    if len(changed) != len(copy) or sum(a != b for a,b in zip(copy,changed)) != 1 or digest(changed) == digest(copy):
        raise SystemExit('Copied own-text altered control failed')
    print('Verified three explicit detached anchors and %d selected files; tiny copied own-text controls behave as expected. Artifact integrity only.' % len(seen))

if __name__ == '__main__':
    main()
