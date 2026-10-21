#!/usr/bin/env python3
"""Read-only packet verifier. All detached anchors must be supplied explicitly."""
import argparse, hashlib, json, sys
from pathlib import Path, PurePosixPath

def sha(data):
    return hashlib.sha256(data).hexdigest()

def require(condition, message):
    if not condition:
        raise ValueError(message)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', required=True)
    ap.add_argument('--final-sha', required=True)
    ap.add_argument('--manifest-sha', required=True)
    ap.add_argument('--report-sha', required=True)
    ap.add_argument('--project-root', help='Optionally check exact recorded original anchors, read-only.')
    args=ap.parse_args()
    root=Path(args.root).resolve()
    for name, expected in [('FINAL.md',args.final_sha),('MANIFEST.json',args.manifest_sha),('REPORT.md',args.report_sha)]:
        require(len(expected)==64 and all(c in '0123456789abcdef' for c in expected), 'Invalid explicit anchor: '+name)
        p=root/name
        require(not p.is_symlink() and p.is_file(), 'Missing/symlink anchor file: '+name)
        require(sha(p.read_bytes())==expected, 'Detached anchor mismatch: '+name)
    manifest=json.loads((root/'MANIFEST.json').read_text())
    require(manifest.get('schema')=='r171-exact-selection-v1', 'Unknown manifest schema')
    seen=set()
    detached={'FINAL.md','MANIFEST.json','REPORT.md','ANCHORS.json'}
    for row in manifest['files']:
        rel=row['path']; posix=PurePosixPath(rel)
        require(not posix.is_absolute() and '..' not in posix.parts and str(posix)==rel, 'Unsafe/noncanonical manifest path')
        require(rel not in seen and rel not in detached, 'Duplicate/detached payload entry: '+rel)
        seen.add(rel); p=root.joinpath(*posix.parts)
        require(not p.is_symlink() and p.is_file() and p.resolve().is_relative_to(root), 'Missing/unsafe payload: '+rel)
        b=p.read_bytes()
        require(len(b)==row['bytes'] and sha(b)==row['sha256'], 'Payload mismatch: '+rel)
    actual=set()
    for p in root.rglob('*'):
        require(not p.is_symlink(), 'Symlink in packet')
        if p.is_file():
            rel=p.relative_to(root).as_posix()
            if rel not in detached: actual.add(rel)
    require(actual==seen, 'File selection differs from manifest')
    if args.project_root:
        project=Path(args.project_root).resolve()
        def original(rel):
            posix=PurePosixPath(rel)
            require(not posix.is_absolute() and '..' not in posix.parts, 'Unsafe original path')
            return project.joinpath(*posix.parts)
        for z in json.loads((root/'private/direct-anchors.json').read_text()):
            with original(z['path']).open('rb') as f:
                f.seek(z['start']); b=f.read(z['end']-z['start'])
            require(len(b)==z['end']-z['start'] and sha(b)==z.get('selection_sha256',z.get('sha256')), 'Direct original mismatch: '+z['path'])
        for z in json.loads((root/'private/completed-exceptions.json').read_text()):
            b=original(z['path']).read_bytes()
            require(len(b)==z['bytes'] and sha(b)==z['sha256'], 'Completed original mismatch: '+z['path'])
        for name in ['original-extents.json','original-equivariant-extents.json']:
            for z in json.loads((root/'private'/name).read_text()):
                b=original(z['path']).read_bytes()
                require(sha(b)==z['sha256'] and sha(b[z['start']:z['end']])==z['selection_sha256'], 'Original section mismatch: '+z['path'])
    print('Artifact verification succeeded: '+str(len(seen))+' selected files; three explicit detached anchors.'+( ' Exact original anchors unchanged.' if args.project_root else ''))
    print('Artifact consistency only; no mathematical grade, acceptance or count.')

if __name__=='__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError) as exc:
        print('Artifact verification failed: '+str(exc), file=sys.stderr)
        sys.exit(1)
