#!/usr/bin/env python3
"""Read-only exact-packet verification. Requires three detached SHA256 anchors.
No author verifier, old binding, outside source, network or mathematical gate.
The same validate() function is used for virtual preflight and sealed disk data.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def safe(path, directory=False):
    assert isinstance(path, str) and path
    if directory and path == '.':
        return
    p = PurePosixPath(path)
    assert not p.is_absolute() and str(p) == path
    assert '\\' not in path and all(x not in ('', '.', '..') for x in path.split('/'))


def snapshot(root):
    """Walk only the explicitly provided packet root; reject symlinks before descent."""
    root = Path(root)
    assert stat.S_ISDIR(root.lstat().st_mode)
    files, dirs = {}, {'.': root.lstat().st_mode}
    pending = [root]
    while pending:
        parent = pending.pop()
        with os.scandir(parent) as scan:
            entries = sorted(scan, key=lambda x: x.name)
        for entry in entries:
            p = Path(entry.path)
            rel = p.relative_to(root).as_posix()
            safe(rel)
            mode = entry.stat(follow_symlinks=False).st_mode
            if stat.S_ISDIR(mode):
                dirs[rel] = mode
                pending.append(p)
            else:
                assert stat.S_ISREG(mode), 'Nonregular member: ' + rel
                files[rel] = {'mode': mode, 'raw': p.read_bytes()}
    return files, dirs


def validate(files, dirs, final_sha, manifest_sha, report_sha):
    for anchor in (final_sha, manifest_sha, report_sha):
        assert re.fullmatch('[0-9a-f]{64}', anchor), 'Explicit SHA256 anchor required'
    for name, anchor in [('FINAL.md', final_sha), ('MANIFEST.json', manifest_sha), ('REPORT.md', report_sha)]:
        assert sha(files[name]['raw']) == anchor, 'Detached anchor mismatch: ' + name
    manifest = json.loads(files['MANIFEST.json']['raw'])
    assert set(manifest) == {'schema', 'payload', 'directories', 'envelopes'}
    assert manifest['schema'] == 'r162cb-contribution-r1-exact-v1'
    records = manifest['payload']
    paths = [x['path'] for x in records]
    assert paths == sorted(set(paths)), 'Payload records must be sorted and unique'
    assert 'FINAL.md' in paths and 'verify.py' in paths
    assert not {'MANIFEST.json', 'REPORT.md'} & set(paths)
    for record in records:
        assert set(record) == {'path', 'sha256', 'bytes', 'mode'}
        name = record['path']; safe(name)
        item = files[name]
        assert stat.S_ISREG(record['mode']) and item['mode'] == record['mode'], 'Full file mode: ' + name
        assert len(item['raw']) == record['bytes'], 'Length: ' + name
        assert sha(item['raw']) == record['sha256'], 'SHA256: ' + name
    envelopes = manifest['envelopes']
    assert [x['path'] for x in envelopes] == ['MANIFEST.json', 'REPORT.md']
    for record in envelopes:
        assert set(record) == {'path', 'mode'}
        assert stat.S_ISREG(record['mode']) and files[record['path']]['mode'] == record['mode']
    assert set(files) == set(paths) | {'MANIFEST.json', 'REPORT.md'}, 'Exact file membership mismatch'
    drecords = manifest['directories']
    dpaths = [x['path'] for x in drecords]
    assert dpaths == sorted(set(dpaths)) and '.' in dpaths
    for record in drecords:
        assert set(record) == {'path', 'mode'}
        name = record['path']; safe(name, directory=True)
        assert stat.S_ISDIR(record['mode']) and dirs[name] == record['mode'], 'Full directory mode: ' + name
    assert set(dirs) == set(dpaths), 'Exact directory membership mismatch'
    report = files['REPORT.md']['raw'].decode('utf-8')
    for token in ('FINAL_SHA256: ' + final_sha, 'MANIFEST_SHA256: ' + manifest_sha,
                  'FINAL_BYTES: ' + str(len(files['FINAL.md']['raw'])),
                  'MANIFEST_BYTES: ' + str(len(files['MANIFEST.json']['raw']))):
        assert token in report, 'Report detached binding missing: ' + token
    return {'result': 'MATCH', 'payload_files': len(paths), 'total_files': len(files),
            'directories_including_root': len(dirs), 'mathematical_gate': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True)
    parser.add_argument('--final-sha256', required=True)
    parser.add_argument('--manifest-sha256', required=True)
    parser.add_argument('--report-sha256', required=True)
    args = parser.parse_args()
    files, dirs = snapshot(Path(args.root))
    result = validate(files, dirs, args.final_sha256, args.manifest_sha256, args.report_sha256)
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
