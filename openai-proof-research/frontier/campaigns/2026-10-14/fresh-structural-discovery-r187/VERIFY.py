#!/usr/bin/env python3
"""Read-only selected-packet verification; explicit detached anchors are mandatory."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys


def sha(data):
    return hashlib.sha256(data).hexdigest()


def inside(root, relative):
    rel = PurePosixPath(relative)
    if rel.is_absolute() or '..' in rel.parts or not rel.parts:
        raise ValueError('unsafe relative path: ' + relative)
    path = root.joinpath(*rel.parts).resolve(strict=True)
    if not path.is_relative_to(root):
        raise ValueError('path escapes selected root: ' + relative)
    if not path.is_file():
        raise ValueError('not a regular file: ' + relative)
    return path


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', required=True, type=Path)
    for label in ['final', 'manifest', 'report']:
        ap.add_argument('--' + label + '-sha', required=True)
    ap.add_argument('--originals', type=Path, help='Optional actual project root; exact recorded spans only')
    args = ap.parse_args()
    root = args.root.resolve(strict=True)
    anchors = [('FINAL.md', args.final_sha), ('private/MANIFEST.json', args.manifest_sha), ('REPORT.md', args.report_sha)]
    for name, expected in anchors:
        if not re.fullmatch('[0-9a-f]{64}', expected):
            raise ValueError('invalid detached anchor: ' + name)
        if sha(inside(root, name).read_bytes()) != expected:
            raise ValueError('detached anchor mismatch: ' + name)
    manifest = json.loads(inside(root, 'private/MANIFEST.json').read_bytes())
    if manifest.get('schema') != 'r187-selected-packet-v1':
        raise ValueError('unsupported manifest schema')
    seen = set()
    for rec in manifest['files']:
        name = rec['path']
        if name in seen or name in ['private/MANIFEST.json', 'REPORT.md', 'ANCHORS.json']:
            raise ValueError('duplicate or detached payload: ' + name)
        seen.add(name)
        data = inside(root, name).read_bytes()
        if len(data) != rec['bytes'] or sha(data) != rec['sha256']:
            raise ValueError('payload mismatch: ' + name)
    if 'FINAL.md' not in seen:
        raise ValueError('FINAL absent from payload')
    source_count = 0
    if 'private/source-auth.json' in seen:
        for rec in json.loads(inside(root, 'private/source-auth.json').read_bytes()):
            suffix = rec['local'].split('/private/source/', 1)[1]
            name = 'private/source/' + suffix
            if name not in seen:
                raise ValueError('authenticated source absent from selected payload')
            data = inside(root, name).read_bytes()
            blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
            if len(data) != rec['bytes'] or sha(data) != rec['sha256'] or blob != rec['git_blob']:
                raise ValueError('source authentication mismatch: ' + name)
            source_count += 1
    original_count = 0
    if args.originals is not None:
        if 'private/original-bindings.json' not in seen:
            raise ValueError('no authenticated original-span bindings')
        project = args.originals.resolve(strict=True)
        for rec in json.loads(inside(root, 'private/original-bindings.json').read_bytes()):
            start, end = rec['start'], rec['end']
            if not isinstance(start, int) or not isinstance(end, int) or not 0 <= start <= end:
                raise ValueError('invalid exact original extent')
            with inside(project, rec['path']).open('rb') as handle:
                handle.seek(start)
                data = handle.read(end - start)
            if len(data) != end - start or sha(data) != rec['sha256']:
                raise ValueError('original span mismatch: ' + rec['path'])
            if 'copy' in rec:
                if rec['copy'] not in seen or inside(root, rec['copy']).read_bytes() != data:
                    raise ValueError('selected copy differs from original span: ' + rec['path'])
            original_count += 1
    print(json.dumps({'artifact_verification': 'matched', 'payload_files': len(seen), 'source_blobs': source_count, 'original_spans': original_count, 'mathematical_gate': False}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError, IndexError, TypeError) as error:
        print('VERIFICATION FAILED: ' + str(error), file=sys.stderr)
        sys.exit(1)
