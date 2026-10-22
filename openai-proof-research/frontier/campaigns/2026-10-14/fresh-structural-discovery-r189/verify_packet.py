#!/usr/bin/env python3
"""Read-only verifier. Supply detached anchors from outside the packet."""
import argparse, hashlib, json
from pathlib import Path, PurePosixPath

DETACHED = {'FINAL.md', 'MANIFEST.json', 'REPORT.md', 'ANCHORS.json', 'SEAL-TESTS.json'}

def digest(b):
    return hashlib.sha256(b).hexdigest()

def verify(root, anchors):
    root = root.resolve(strict=True)
    for name in ('FINAL.md', 'MANIFEST.json', 'REPORT.md'):
        p = root / name
        if p.is_symlink() or digest(p.read_bytes()) != anchors[name]:
            raise ValueError('detached anchor mismatch: '+name)
    manifest = json.loads((root/'MANIFEST.json').read_bytes())
    if manifest['format'] != 'r189-exact-packet-v1':
        raise ValueError('wrong format')
    entries = manifest['files']
    selected = set()
    for entry in entries:
        s = entry['path']; rel = PurePosixPath(s)
        if rel.is_absolute() or '..' in rel.parts or str(rel) != s or s in selected:
            raise ValueError('unsafe or duplicate path')
        if s in DETACHED or s.startswith('private/controls/'):
            raise ValueError('detached/control path in selected packet')
        p = root
        for part in rel.parts:
            p = p / part
            if p.is_symlink(): raise ValueError('symlink in selected packet')
        raw = p.read_bytes()
        if len(raw) != entry['bytes'] or digest(raw) != entry['sha256']:
            raise ValueError('selected payload mismatch: '+s)
        selected.add(s)
    actual = set()
    for p in root.rglob('*'):
        s = p.relative_to(root).as_posix()
        if s == 'private/controls' or s.startswith('private/controls/'):
            continue
        if p.is_symlink(): raise ValueError('unexpected symlink')
        if p.is_file() and s not in DETACHED:
            actual.add(s)
    if actual != selected:
        raise ValueError('selected file-set mismatch')
    return {'artifact_verification':'matched', 'selected_files':len(selected)}

def main():
    a=argparse.ArgumentParser()
    a.add_argument('--root', required=True)
    a.add_argument('--final-sha256', required=True)
    a.add_argument('--manifest-sha256', required=True)
    a.add_argument('--report-sha256', required=True)
    x=a.parse_args()
    for v in (x.final_sha256,x.manifest_sha256,x.report_sha256):
        if len(v)!=64 or any(c not in '0123456789abcdef' for c in v):
            a.error('anchors must be explicit lowercase SHA256 hex')
    anchors={'FINAL.md':x.final_sha256,'MANIFEST.json':x.manifest_sha256,'REPORT.md':x.report_sha256}
    try:
        print(json.dumps(verify(Path(x.root),anchors),sort_keys=True))
    except (OSError,ValueError,KeyError,TypeError) as e:
        print(json.dumps({'artifact_verification':'rejected','reason':str(e)},sort_keys=True))
        raise SystemExit(1)
if __name__=='__main__': main()
