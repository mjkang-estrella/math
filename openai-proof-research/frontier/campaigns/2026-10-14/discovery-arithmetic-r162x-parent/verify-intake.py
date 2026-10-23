#!/usr/bin/env python3
"""Authenticate the completed r162x selection without assigning a math gate."""
from pathlib import Path
import hashlib
import json
import os
import stat
import subprocess
import sys

P = Path(__file__).resolve().parents[4]
D = Path(__file__).resolve().parent
R = P / 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162x'
ANCHORS = {'FINAL.md': '9abb5cdf2046f5cd06eacfc41a2a245c5fe2eab5f6ed66736aaeec717c3213e1',
           'MANIFEST.json': '51bbe597c7c456452a3579f079c1b3187908366572987f5753f7ae567a4db64a',
           'REPORT.md': '8945f14236cef7175cdd4083fccdfb64f42e04e9da55593349e2a33babe58667'}
sha = lambda raw: hashlib.sha256(raw).hexdigest()
load = lambda path: json.loads(path.read_bytes())


def main():
    command = [sys.executable, '-I', '-B', str(R / 'verify.py'), '--root', str(R)]
    for name, expected in ANCHORS.items():
        assert sha((R / name).read_bytes()) == expected
        command += ['--' + name.split('.')[0].lower() + '-sha256', expected]
    result = subprocess.run(command, cwd=P, capture_output=True, text=True)
    assert result.returncode == 0, result.stderr
    seal = json.loads(result.stdout)
    assert seal['files'] == 66 and seal['directories'] == 20 and not seal['mathematical_gate']
    snapshot = load(D / 'private/intake/root-before.json')
    found = set()
    for dr, dirs, files in os.walk(R, followlinks=False):
        assert all(not (Path(dr) / x).is_symlink() for x in dirs)
        for name in files:
            path = Path(dr) / name
            rel = str(path.relative_to(R))
            assert rel in snapshot and stat.S_ISREG(path.lstat().st_mode)
            raw = path.read_bytes()
            assert len(raw) == snapshot[rel]['bytes'] and sha(raw) == snapshot[rel]['sha256']
            assert path.stat().st_mode == snapshot[rel]['mode']
            found.add(rel)
    assert found == snapshot.keys() and len(found) == 70
    tree_raw = (P / 'sources/preprints-tree.json').read_bytes()
    assert sha(tree_raw) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree = json.loads(tree_raw)
    assert not tree['truncated'] and len(tree['tree']) == 13223 and len(tree_raw) == 4858136
    index = {x['path']: x for x in tree['tree']}
    canonical = load(R / 'packet/private/canonical-authentication.json')
    assert len(canonical) == 15
    for entry in canonical:
        raw = (P / entry['local']).read_bytes()
        path = index[entry['path']]
        blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        assert path['type'] == 'blob' and path['size'] == entry['bytes'] == len(raw)
        assert path['sha'] == entry['git_blob_sha1'] == blob
        assert entry['sha256'] == entry['local_reread_sha256'] == sha(raw)
    for entry in load(D / 'private/completed-direct-inputs.json'):
        path = P / entry['path']
        raw = path.read_bytes()
        assert sha(raw) == entry['sha256'] and len(raw) == entry['bytes']
        assert path.stat().st_mode == entry['mode']
    for path, expected in load(D / 'intake-baseline.json')['protected'].items():
        assert sha((P / path).read_bytes()) == expected
    controls = load(R / 'packet/private/copied-control-results.json')['controls']
    assert [x['returncode'] for x in controls] == [0, 1, 1]
    assert all(x['returncode'] == x['expected'] for x in controls)
    print(json.dumps({'result': 'MATCH', 'integrity_only': True,
        'manifested_files': 66, 'manifested_directories': 20,
        'directory_permissions_not_certified_by_manifest': True,
        'whole_root_files_unchanged': 70, 'canonical_blobs_matched': 15,
        'completed_direct_originals_unchanged': 5,
        'saved_copied_controls_checked_not_rerun': [0, 1, 1],
        'parent_source_primary_semantic_rereading_this_intake': False,
        'anchors': ANCHORS, 'mathematical_grade_assigned': False}, indent=2))


if __name__ == '__main__':
    main()
