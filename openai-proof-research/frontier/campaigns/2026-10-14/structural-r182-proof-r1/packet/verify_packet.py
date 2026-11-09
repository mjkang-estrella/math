#!/usr/bin/env python3
"""Read-only artifact verifier; never a mathematical correctness gate."""
import argparse
import hashlib
import json
import stat
from pathlib import Path, PurePosixPath


def digest(data):
    return hashlib.sha256(data).hexdigest()


def safe_relative(value):
    p = PurePosixPath(value)
    if p.is_absolute() or '..' in p.parts or p.as_posix() != value:
        raise ValueError('Non-canonical relative path: ' + value)
    return p


def checked_file(base, relative):
    p = base.joinpath(*safe_relative(relative).parts)
    current = base
    for component in safe_relative(relative).parts:
        current = current / component
        if current.is_symlink():
            raise ValueError('Symlink forbidden: ' + str(current))
    if not p.is_file():
        raise ValueError('Missing file: ' + str(p))
    return p


def run(root, final_anchor, manifest_anchor, report_anchor, originals=False, project=None):
    packet = root / 'packet'
    for relative, expected in [('FINAL.json', final_anchor),
                               ('packet/MANIFEST.json', manifest_anchor),
                               ('REPORT.md', report_anchor)]:
        if len(expected) != 64 or any(c not in '0123456789abcdef' for c in expected):
            raise ValueError('Explicit lowercase SHA256 anchor required: ' + relative)
        if digest(checked_file(root, relative).read_bytes()) != expected:
            raise ValueError('Detached anchor mismatch: ' + relative)
    manifest = json.loads((packet / 'MANIFEST.json').read_bytes())
    final = json.loads((root / 'FINAL.json').read_bytes())
    if final['manifest_sha256'] != manifest_anchor:
        raise ValueError('FINAL does not bind this manifest')
    if final['report_sha256'] != report_anchor:
        raise ValueError('FINAL does not bind this REPORT')
    expected = set()
    for entry in manifest['members']:
        relative = entry['path']
        if relative == 'MANIFEST.json' or relative in expected:
            raise ValueError('Invalid/duplicate manifest member: ' + relative)
        expected.add(relative)
        p = checked_file(packet, relative)
        data = p.read_bytes()
        if len(data) != entry['bytes'] or digest(data) != entry['sha256']:
            raise ValueError('Member bytes mismatch: ' + relative)
        if stat.S_IMODE(p.stat().st_mode) != entry['mode']:
            raise ValueError('Member mode mismatch: ' + relative)
    # Traversal is confined to this explicitly selected OWN packet, never the project.
    found = set()
    stack = [packet]
    while stack:
        directory = stack.pop()
        for p in directory.iterdir():
            if p.is_symlink():
                raise ValueError('Packet symlink forbidden: ' + str(p))
            if p.is_dir():
                stack.append(p)
            elif p.is_file():
                found.add(p.relative_to(packet).as_posix())
            else:
                raise ValueError('Unexpected packet node: ' + str(p))
    if found != expected | {'MANIFEST.json'}:
        raise ValueError('Exact packet membership mismatch')
    checked = 0
    if originals:
        if project is None:
            raise ValueError('--project required with --originals')
        # This anchored list enumerates exact admitted paths/windows. No discovery.
        anchors = json.loads((packet/'private/original-anchors.json').read_bytes())
        for entry in anchors:
            p = checked_file(project, entry['original'])
            if 'range' in entry:
                lo, hi = entry['range']
                with p.open('rb') as handle:
                    handle.seek(lo)
                    data = handle.read(hi-lo)
            else:
                data = p.read_bytes()
            if len(data) != entry['bytes'] or digest(data) != entry['sha256']:
                raise ValueError('Original bytes mismatch: ' + entry['original'])
            if stat.S_IMODE(p.stat().st_mode) != entry['mode']:
                raise ValueError('Original mode mismatch: ' + entry['original'])
            checked += 1
    return {'artifact_verification': 'PASS', 'packet_members': len(expected),
            'original_anchors_checked': checked, 'mathematical_gate': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--final-sha256', required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--report-sha256', required=True)
    parser.add_argument('--originals', action='store_true')
    parser.add_argument('--project', type=Path)
    args = parser.parse_args()
    try:
        result = run(args.root, args.final_sha256, args.manifest_sha256,
                     args.report_sha256, args.originals, args.project)
    except (ValueError, KeyError, OSError, json.JSONDecodeError) as exc:
        print(json.dumps({'artifact_verification': 'FAIL', 'reason': str(exc),
                          'mathematical_gate': False}))
        raise SystemExit(1)
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
