#!/usr/bin/env python3
"""Read-only input authentication; no mathematical gate is assigned."""
from pathlib import Path
import hashlib
import json
import os
import stat
import subprocess
import sys

P = Path(__file__).resolve().parents[4]
D = Path(__file__).resolve().parent
R = P / 'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162z'
ANCHORS = {'FINAL.md': '08b798ed144caec80a4828e4f6da6dad4bf027e84c6fcadedd2523a77111a47f',
           'MANIFEST.json': 'f4ab790cc1ebcf82723eab3ff99ebbb2b6a2bda45535064109678d3af368a32f',
           'REPORT.md': '40ff7795c6c90fcb1bb2cc7261c22b11db7c6deff8c4571d7d67034a7354c43a'}
sha = lambda raw: hashlib.sha256(raw).hexdigest()
load = lambda path: json.loads(path.read_bytes())


def main():
    command = [sys.executable, '-I', '-B', str(R / 'verify_packet.py'), '--root', str(R)]
    for path, expected in ANCHORS.items():
        assert sha((R / path).read_bytes()) == expected
        command += ['--' + path.split('.')[0].lower() + '-sha256', expected]
    result = subprocess.run(command, cwd=P, capture_output=True, text=True)
    assert result.returncode == 0, result.stderr
    checked = json.loads(result.stdout)
    assert checked == {'artifact_integrity': 'PASS', 'files': 107, 'bytes': 6938502, 'mathematical_gate': False}
    snapshot = load(D / 'private/intake/root-before.json')
    found = set()
    for dr, dirs, files in os.walk(R, followlinks=False):
        assert all(not (Path(dr) / name).is_symlink() for name in dirs)
        for name in files:
            path = Path(dr) / name
            key = str(path.relative_to(R))
            assert key in snapshot and stat.S_ISREG(path.lstat().st_mode)
            raw = path.read_bytes()
            assert len(raw) == snapshot[key]['bytes'] and sha(raw) == snapshot[key]['sha256']
            assert path.stat().st_mode == snapshot[key]['mode']
            found.add(key)
    assert found == snapshot.keys() and len(found) == 116
    tree_raw = (P / 'sources/preprints-tree.json').read_bytes()
    assert sha(tree_raw) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree = json.loads(tree_raw)
    assert len(tree['tree']) == 13223 and len(tree_raw) == 4858136 and not tree['truncated']
    index = {entry['path']: entry for entry in tree['tree']}
    source = load(R / 'packet/private/source-authentication.json')
    assert len(source) == 75
    for entry in source:
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
    controls = load(R / 'controls/results.json')
    assert controls['copied_fixture_restored'] and not controls['mathematical_gate']
    assert [x['returncode'] for x in controls['controls']] == [0, 1, 1, 1]
    print(json.dumps({'result': 'MATCH', 'integrity_only': True, 'selection_files': 107,
        'selection_bytes': 6938502, 'whole_root_files_unchanged': 116,
        'canonical_blobs_matched': 75, 'completed_direct_originals_unchanged': 5,
        'saved_copied_controls_checked_not_rerun': [0, 1, 1, 1], 'anchors': ANCHORS,
        'manifest_does_not_check_file_modes_or_directory_membership': True,
        'separate_snapshot_checks_full_file_modes': True,
        'parent_source_primary_semantic_rereading_this_intake': False,
        'mathematical_grade_assigned': False}, indent=2))


if __name__ == '__main__':
    main()
