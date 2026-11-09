#!/usr/bin/env python3
"""Read-only verifier. Explicit detached anchors are required; no discovery or writes."""
import argparse
import hashlib
import json
import stat
from pathlib import Path, PurePosixPath

ROOT_REL = 'frontier/campaigns/2026-10-14/arithmetic-r162aj-proof-r1'

def digest(data):
    return hashlib.sha256(data).hexdigest()

def checked_path(project, relative):
    q = PurePosixPath(relative)
    if q.is_absolute() or '..' in q.parts:
        raise ValueError('non-relative path')
    p = project.joinpath(*q.parts)
    for candidate in [p, *p.parents]:
        if candidate.is_symlink():
            raise ValueError('symlink refused: ' + str(candidate))
        if candidate == project:
            break
    if not stat.S_ISREG(p.stat().st_mode):
        raise ValueError('not a regular file: ' + relative)
    return p

def matches(project, entry):
    p = checked_path(project, entry['path'])
    if 'range' in entry:
        lo, hi = entry['range']
        with p.open('rb') as f:
            f.seek(lo)
            data = f.read(hi-lo)
    else:
        data = p.read_bytes()
    return (len(data) == entry['bytes'] and digest(data) == entry['sha256']
            and oct(stat.S_IMODE(p.stat().st_mode)) == entry['mode'])

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--final-sha256', required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--report-sha256', required=True)
    args = parser.parse_args()
    project = Path.cwd()
    root = project / ROOT_REL
    if Path(__file__).resolve().parent != root.resolve():
        raise SystemExit('Run with the specified project as working directory.')
    for name, expected in [('FINAL.md', args.final_sha256),
                           ('MANIFEST.json', args.manifest_sha256),
                           ('REPORT.md', args.report_sha256)]:
        p = checked_path(project, ROOT_REL + '/' + name)
        if digest(p.read_bytes()) != expected:
            raise SystemExit('Detached anchor mismatch: ' + name)
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    for entry in manifest['artifacts'] + manifest['readonly_inputs']:
        if not matches(project, entry):
            raise SystemExit('Byte/range/mode mismatch: ' + entry['path'])
    controls = json.loads((root / 'private/controls/cases.json').read_text())
    for case in controls:
        actual = matches(project, case['reference'])
        if actual != case['should_match']:
            raise SystemExit('Control failed: ' + case['name'])
    print('VERIFIED: detached anchors; %d artifacts; %d readonly inputs; %d copied controls.'
          % (len(manifest['artifacts']), len(manifest['readonly_inputs']), len(controls)))
    print('Journal verification read only bytes [4801,6347). No file was written.')
    print('Artifact checks are not mathematical correctness gates.')

if __name__ == '__main__':
    main()
