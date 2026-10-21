#!/usr/bin/env python3
"""Read-only identity checks. Explicit detached anchors are mandatory; no scanning."""
import argparse, hashlib, json, re, stat
from pathlib import Path, PurePosixPath

def digest(b):
    return hashlib.sha256(b).hexdigest()

def inside(root, name):
    p = PurePosixPath(name)
    if p.is_absolute() or not p.parts or any(x in ('..', '.') for x in p.parts):
        raise ValueError('unsafe relative path')
    target = root
    for component in p.parts:
        target = target / component
        if target.is_symlink():
            raise ValueError('symlink rejected: ' + name)
    if not target.resolve().is_relative_to(root.resolve()):
        raise ValueError('path escape')
    return target

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', required=True)
    for n in ('final', 'manifest', 'report'):
        ap.add_argument('--'+n+'-sha256', required=True)
    ap.add_argument('--originals-project')
    args = ap.parse_args()
    root = Path(args.root)
    if root.is_symlink():
        raise ValueError('root symlink')
    for label in ('final', 'manifest', 'report'):
        h = getattr(args, label+'_sha256')
        if not re.fullmatch('[0-9a-f]{64}', h):
            raise ValueError('invalid explicit anchor')
        name = label.upper()+('.json' if label == 'manifest' else '.md')
        if digest(inside(root, name).read_bytes()) != h:
            raise ValueError('detached anchor mismatch: '+name)
    m = json.loads(inside(root, 'MANIFEST.json').read_text())
    seen = set()
    for x in m['files']:
        name = x['path']
        if name in seen or name in ('FINAL.md','MANIFEST.json','REPORT.md','ANCHORS.json'):
            raise ValueError('duplicate or envelope payload')
        seen.add(name)
        p = inside(root, name)
        b = p.read_bytes()
        if len(b) != x['bytes'] or digest(b) != x['sha256']:
            raise ValueError('payload mismatch: '+name)
        if stat.S_IMODE(p.stat().st_mode) != x['mode']:
            raise ValueError('payload mode mismatch: '+name)
    count = 0
    if args.originals_project:
        anchors = json.loads(inside(root, m['original_anchors']).read_text())
        project = Path(args.originals_project)
        for x in anchors:
            p = inside(project, x['original'])
            with p.open('rb') as f:
                f.seek(x['start']); b = f.read(x['end']-x['start'])
            if len(b) != x['end']-x['start'] or digest(b) != x['sha256']:
                raise ValueError('explicit original mismatch: '+x['original'])
            if stat.S_IMODE(p.stat().st_mode) != x['mode']:
                raise ValueError('original mode mismatch: '+x['original'])
            count += 1
    print(json.dumps({'artifact_identity':'PASS','payload_files':len(seen),'explicit_original_slices':count,'mathematical_gate':False}))

if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError) as e:
        print('artifact identity FAIL:', e)
        raise SystemExit(1)
