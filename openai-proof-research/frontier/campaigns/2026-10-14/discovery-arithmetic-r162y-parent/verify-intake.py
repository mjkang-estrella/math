#!/usr/bin/env python3
"""Verify this completed packet and originals; no mathematical gate assigned."""
from pathlib import Path
import hashlib
import json
import os
import stat
import subprocess
import sys

P = Path(__file__).resolve().parents[4]
D = Path(__file__).resolve().parent
R = P / 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162y'
ANCHORS = {'FINAL.md': '304c77f4e1038cdcc7ab76a4bd9c99311dc2cee1a8c74f0a4c467bf2bfb4ade3',
           'packet/private/MANIFEST.json': '9788d5edfd0d6fe0f0d54787b3265693ae97f69685066e7d48dcf1c118171b82',
           'REPORT.md': 'ebc7bef08b01fbb83c27e1b95cdc983f0ab4ef89dc863a5ef6288a924fcb1acc'}
sha = lambda data: hashlib.sha256(data).hexdigest()
load = lambda path: json.loads(path.read_bytes())


def main():
    for path, expected in ANCHORS.items():
        assert sha((R / path).read_bytes()) == expected
    command = [sys.executable, '-I', '-B', str(R / 'packet/verify.py'), '--root', str(R),
               '--final-sha', ANCHORS['FINAL.md'], '--manifest-sha', ANCHORS['packet/private/MANIFEST.json'],
               '--report-sha', ANCHORS['REPORT.md']]
    result = subprocess.run(command, cwd=P, capture_output=True, text=True)
    assert result.returncode == 0, result.stderr
    snapshot = load(D / 'private/intake/root-before.json')
    found = set()
    for directory, dirs, files in os.walk(R, followlinks=False):
        assert all(not (Path(directory) / name).is_symlink() for name in dirs)
        for name in files:
            path = Path(directory) / name
            rel = str(path.relative_to(R))
            assert rel in snapshot and stat.S_ISREG(path.lstat().st_mode)
            data = path.read_bytes()
            assert len(data) == snapshot[rel]['bytes'] and sha(data) == snapshot[rel]['sha256']
            assert path.stat().st_mode == snapshot[rel]['mode']
            found.add(rel)
    assert found == snapshot.keys() and len(found) == 69
    manifest = load(R / 'packet/private/MANIFEST.json')
    assert len(manifest['files']) == 65
    raw_tree = (P / 'sources/preprints-tree.json').read_bytes()
    assert sha(raw_tree) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree = json.loads(raw_tree)
    assert len(tree['tree']) == 13223 and len(raw_tree) == 4858136 and not tree['truncated']
    index = {e['path']: e for e in tree['tree']}
    entries = load(R / 'packet/private/canonical-authentication.json')
    assert len(entries) == 29
    for entry in entries:
        copies = [path for path in snapshot if path.endswith('/' + entry['path'])]
        assert len(copies) == 1
        raw = (R / copies[0]).read_bytes()
        item = index[entry['path']]
        blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        assert item['type'] == 'blob' and len(raw) == item['size'] == entry['bytes']
        assert blob == item['sha'] == entry['git_blob'] and sha(raw) == entry['sha256']
    for entry in load(D / 'private/completed-direct-inputs.json'):
        path = P / entry['path']
        assert sha(path.read_bytes()) == entry['sha256'] and path.stat().st_mode == entry['mode']
    for path, expected in load(D / 'intake-baseline.json')['protected'].items():
        assert sha((P / path).read_bytes()) == expected
    controls = load(R / 'packet/private/controls/results.json')['results']
    assert len(controls) == 5 and all(value is True for value in controls.values())
    print(json.dumps({'result': 'MATCH', 'integrity_only': True, 'packet_files': 65,
        'whole_root_files_unchanged': 69, 'canonical_blobs_matched': 29,
        'completed_direct_originals_unchanged': 5, 'anchors': ANCHORS,
        'saved_copied_controls_checked_not_rerun': controls,
        'verifier_output': result.stdout.strip(),
        'manifest_does_not_check_file_modes_or_directory_membership': True,
        'separate_full_file_snapshot_checks_modes': True,
        'parent_source_primary_semantic_rereading_this_intake': False,
        'mathematical_grade_assigned': False}, indent=2))


if __name__ == '__main__':
    main()
