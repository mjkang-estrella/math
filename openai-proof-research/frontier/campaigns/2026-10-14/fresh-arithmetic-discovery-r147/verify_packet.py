#!/usr/bin/env python3
"""Read-only artifact check. Supply all three detached SHA256 anchors explicitly."""
import argparse
import hashlib
import json
import re
from pathlib import Path, PurePosixPath


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def safe(root, name):
    q = PurePosixPath(name)
    if q.is_absolute() or not q.parts or any(v in ('..', '.') for v in q.parts):
        raise ValueError('unsafe relative path: ' + name)
    p = root
    for part in q.parts:
        p = p / part
        if p.is_symlink():
            raise ValueError('symlink in selected path: ' + name)
    if not p.is_file() or not p.resolve().is_relative_to(root.resolve()):
        raise ValueError('missing or escaped selected file: ' + name)
    return p


def main():
    a = argparse.ArgumentParser(description=__doc__)
    a.add_argument('--root', type=Path, required=True)
    a.add_argument('--final-sha256', required=True)
    a.add_argument('--manifest-sha256', required=True)
    a.add_argument('--report-sha256', required=True)
    a.add_argument('--originals-project', type=Path,
                   help='Optional exact-anchor slice comparison; no traversal or writes.')
    args = a.parse_args()
    root = args.root
    for name, anchor in [('FINAL.md', args.final_sha256),
                         ('MANIFEST.json', args.manifest_sha256),
                         ('REPORT.md', args.report_sha256)]:
        if re.fullmatch('[0-9a-f]{64}', anchor) is None:
            raise ValueError('invalid explicit anchor for ' + name)
        if digest(safe(root, name)) != anchor:
            raise ValueError('detached anchor mismatch: ' + name)
    manifest = json.loads(safe(root, 'MANIFEST.json').read_text())
    if manifest.get('schema') != 'r147-selected-packet-v1':
        raise ValueError('unsupported manifest schema')
    seen = set()
    for item in manifest['files']:
        name = item['path']
        if name in seen or name in ('FINAL.md', 'MANIFEST.json', 'REPORT.md', 'ANCHORS.json'):
            raise ValueError('duplicate or envelope in selected payload: ' + name)
        seen.add(name)
        p = safe(root, name)
        if p.stat().st_size != item['bytes'] or digest(p) != item['sha256']:
            raise ValueError('selected payload mismatch: ' + name)
    frozen = manifest.get('frozen_statement')
    if frozen:
        if frozen['path'] not in seen or digest(safe(root, frozen['path'])) != frozen['sha256']:
            raise ValueError('frozen statement mismatch')
    auth = manifest.get('source_authentication')
    if auth:
        if auth not in seen:
            raise ValueError('unbound source authentication')
        for item in json.loads(safe(root, auth).read_text()):
            name = 'private/source/' + PurePosixPath(item['path']).name
            if name not in seen:
                raise ValueError('unbound source object')
            data = safe(root, name).read_bytes()
            blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
            if len(data) != item['bytes'] or blob != item['blob'] or hashlib.sha256(data).hexdigest() != item['sha256']:
                raise ValueError('source object mismatch: ' + name)
    original_count = 0
    if args.originals_project:
        name = manifest.get('original_anchors')
        if not name or name not in seen:
            raise ValueError('no bound original anchors')
        for item in json.loads(safe(root, name).read_text()):
            p = safe(args.originals_project, item['path'])
            with p.open('rb') as f:
                f.seek(item['start'])
                data = f.read(item['end'] - item['start'])
            if len(data) != item['end'] - item['start'] or hashlib.sha256(data).hexdigest() != item['sha256']:
                raise ValueError('original slice changed: ' + item['path'])
            original_count += 1
    print(json.dumps({'artifact_verification': 'matched', 'selected_files': len(seen),
                      'exact_original_slices': original_count,
                      'writes': 0, 'mathematical_judgment': 'none'}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError, json.JSONDecodeError) as exc:
        raise SystemExit(str(exc))
