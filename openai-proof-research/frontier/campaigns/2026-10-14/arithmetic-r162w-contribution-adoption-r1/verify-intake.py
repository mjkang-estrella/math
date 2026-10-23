#!/usr/bin/env python3
"""Authenticate completed review inputs; integrity is not a mathematical gate."""
from pathlib import Path
import hashlib
import json
import os
import stat
import subprocess
import sys

P = Path(__file__).resolve().parents[4]
B = P / 'frontier/campaigns/2026-10-14'
D = Path(__file__).resolve().parent
R = B / 'arithmetic-r162w-contribution-r1'
A = B / 'fresh-arithmetic-discovery-r162w'
ANCHORS = {'FINAL.md': 'a0c3402cd930de8688fefaad4f90901fc379e9a25bc79fe60674d944dafd93a6',
           'MANIFEST.json': 'd93e271c78a402d1489db6237804dbc27e9f41287cca17b290ad51cc9dd608ea',
           'REPORT.md': '8443ea496f3a673a3381b1a250226f242b00d96df11924079e5041b8c00da9ac'}
sha = lambda raw: hashlib.sha256(raw).hexdigest()
load = lambda path: json.loads(path.read_bytes())


def match(path, expected):
    raw = path.read_bytes()
    assert path.is_file() and not path.is_symlink()
    assert len(raw) == expected['bytes'] and sha(raw) == expected['sha256'], path
    assert stat.S_IMODE(path.stat().st_mode) == stat.S_IMODE(expected['mode']), path


def snapshot(root, expected):
    found = set()
    for dr, dirs, files in os.walk(root, followlinks=False):
        assert all(not (Path(dr) / name).is_symlink() for name in dirs)
        for name in files:
            q = Path(dr) / name
            key = str(q.relative_to(root))
            assert key in expected
            match(q, expected[key])
            found.add(key)
    assert found == expected.keys()
    return len(found)


def main():
    cmd = [sys.executable, '-I', '-B', str(R / 'packet/notes/verify_packet.py'), '--root', str(R)]
    for name, value in ANCHORS.items():
        assert sha((R / name).read_bytes()) == value
        cmd += ['--' + name.split('.')[0].lower() + '-sha256', value]
    run = subprocess.run(cmd, cwd=P, capture_output=True, text=True)
    assert run.returncode == 0, run.stderr
    review_count = snapshot(R, load(D / 'private/review-before.json'))
    author_count = snapshot(A, load(D / 'private/author-before.json'))
    assert author_count == snapshot(A, load(B / 'discovery-arithmetic-r162w-parent/private/root-before.json')) == 152
    original = load(B / 'discovery-arithmetic-r162w-parent/private/review-inputs.json')
    assert original == load(R / 'packet/private/review-inputs.json')
    inputs = load(R / 'packet/private/input-baseline.json')
    checks = load(R / 'packet/private/completion-input-check.json')
    assert checks['all_127_author_files_and_three_original_history_extents_unchanged']
    assert len(inputs) == len(checks['checks']) == 130
    expected = {e['path']: e for e in original['entries']}
    assert set(expected) == {e['path'] for e in inputs[:127]}
    for i, entry in enumerate(inputs):
        check = checks['checks'][i]
        assert check['unchanged'] and check['selected_copy_bytes_and_mode_equal']
        assert check['path'] == entry['path']
        match(R / entry['selected'], entry)
        if i < 127:
            assert all(entry[k] == expected[entry['path']][k] for k in ('bytes', 'mode', 'sha256'))
            match(P / entry['path'], entry)
        else:
            start, end = check['byte_extent']
            with (P / entry['path']).open('rb') as stream:
                stream.seek(start)
                raw = stream.read(end - start)
            assert sha(raw) == entry['sha256'] and len(raw) == entry['bytes']
            assert (P / entry['path']).stat().st_mode == entry['mode']
    raw_tree = (P / 'sources/preprints-tree.json').read_bytes()
    assert sha(raw_tree) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree = json.loads(raw_tree)
    assert len(raw_tree) == 4858136 and len(tree['tree']) == 13223 and not tree['truncated']
    index = {e['path']: e for e in tree['tree']}
    canonical = load(R / 'packet/private/canonical-independent-authentication.json')
    assert len(canonical) == 55
    for entry in canonical:
        key = entry['path']
        source = index.get(key) or index.get(key.removeprefix('preprints/'))
        raw = (R / 'packet/private/inputs/packet/private/canonical' / key).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        assert source['type'] == 'blob' and source['size'] == len(raw) == entry['bytes']
        assert blob == entry['git_blob'] == source['sha'] and sha(raw) == entry['sha256']
    reading = load(R / 'packet/private/selected-reading-map.json')
    assert len(reading) == 127
    for entry in reading:
        match(R / entry['selected'], entry)
        last = 0
        for start, end in entry['semantic_byte_extents']:
            assert last <= start < end <= entry['bytes']
            last = end
        if entry['complete_text_read']:
            assert entry['semantic_byte_extents'] == [[0, entry['bytes']]]
    controls = load(R / 'packet/private/artifact-controls.json')['results']
    assert [x['actual_exit'] for x in controls] == [0, 1, 1]
    assert all(x['actual_exit'] == x['expected_exit'] and x['passed_expected_integrity_behavior'] for x in controls)
    for path, expected_hash in load(D / 'integration-baseline.json')['protected'].items():
        assert sha((P / path).read_bytes()) == expected_hash
    print(json.dumps({'result': 'MATCH', 'integrity_only': True,
        'payload_files': 160, 'payload_directories': 33,
        'whole_review_root_files_unchanged': review_count,
        'whole_author_root_files_unchanged': author_count,
        'admitted_author_originals_and_copies_matched': 127,
        'original_history_extents_matched': 3, 'canonical_bindings_matched': 55,
        'reading_map_records_authenticated': 127,
        'saved_copied_controls_checked_not_rerun': [0, 1, 1],
        'parent_source_primary_semantic_rereading_this_turn': False,
        'anchors': ANCHORS, 'verifier_output': run.stdout.strip()}, indent=2))


if __name__ == '__main__':
    main()
