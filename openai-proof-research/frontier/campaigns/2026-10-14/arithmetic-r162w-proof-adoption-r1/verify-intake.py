#!/usr/bin/env python3
"""Read-only verification of this completed review and its exact input selection.

This authenticates artifacts; it does not establish mathematical correctness.
All source-bearing output stays in the parent intake's private directory.
"""
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
R = B / 'arithmetic-r162w-proof-r1'
A = B / 'fresh-arithmetic-discovery-r162w'
PREVIOUS = B / 'discovery-arithmetic-r162w-parent'
ANCHORS = {
    'FINAL.md': 'd5ea00ae624c6077cda93619fe4a5e3316820a5318dadef723d5e5d0076181c2',
    'MANIFEST.json': '373ea3a6b5027ade2f990209e26e1974bf9a4afc7d5e6a46d8657ae85a8594ef',
    'REPORT.md': 'a38d4abc2f071242d3725ac15cdada64d07572f6dfe92f10cd0617480559c769',
}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def read_json(path):
    return json.loads(path.read_bytes())


def info(path):
    st = path.lstat()
    assert stat.S_ISREG(st.st_mode), path
    raw = path.read_bytes()
    return {'bytes': len(raw), 'mode': st.st_mode, 'sha256': sha(raw)}


def matches(path, expected):
    actual = info(path)
    assert actual['bytes'] == expected['bytes'], path
    assert actual['sha256'] == expected['sha256'], path
    assert stat.S_IMODE(actual['mode']) == stat.S_IMODE(expected['mode']), path


def check_snapshot(root, snapshot):
    found = set()
    for directory, dirs, files in os.walk(root, followlinks=False):
        for name in dirs:
            assert not (Path(directory) / name).is_symlink()
        for name in files:
            path = Path(directory) / name
            relative = str(path.relative_to(root))
            assert relative in snapshot, relative
            matches(path, snapshot[relative])
            found.add(relative)
    assert found == snapshot.keys()
    return len(found)


def main():
    for name, expected in ANCHORS.items():
        assert sha((R / name).read_bytes()) == expected
    command = [sys.executable, '-I', '-B', str(R / 'packet/notes/verify_packet.py'),
               '--root', str(R), '--final-sha256', ANCHORS['FINAL.md'],
               '--manifest-sha256', ANCHORS['MANIFEST.json'],
               '--report-sha256', ANCHORS['REPORT.md']]
    completed = subprocess.run(command, cwd=P, capture_output=True, text=True)
    assert completed.returncode == 0, completed.stderr
    review_files = check_snapshot(R, read_json(D / 'private/review-before.json'))
    author_files = check_snapshot(A, read_json(D / 'private/author-before.json'))
    assert author_files == check_snapshot(A, read_json(PREVIOUS / 'private/root-before.json')) == 152

    inputs = read_json(PREVIOUS / 'private/review-inputs.json')
    assert (PREVIOUS / 'private/review-inputs.json').read_bytes() == (R / 'packet/private/review-inputs.json').read_bytes()
    original = {e['path']: e for e in inputs['entries']}
    before = read_json(R / 'packet/private/author-before.json')
    after = read_json(R / 'packet/private/author-after.json')
    assert len(original) == len(before) == len(after['entries']) == 127
    assert original.keys() == {e['path'] for e in before} == {e['path'] for e in after['entries']}
    for entry in before:
        expected = original[entry['path']]
        matches(P / entry['path'], expected)
        matches(R / entry['selected_path'], expected)
    for entry in after['entries']:
        assert entry == original[entry['path']]

    tree_raw = (P / 'sources/preprints-tree.json').read_bytes()
    assert len(tree_raw) == 4858136
    assert sha(tree_raw) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree = json.loads(tree_raw)
    assert not tree['truncated'] and len(tree['tree']) == 13223
    tree_map = {e['path']: e for e in tree['tree']}
    canonical = read_json(R / 'packet/private/canonical-independent-authentication.json')['verified_blobs']
    assert len(canonical) == 55
    for entry in canonical:
        key = entry['path']
        source = tree_map.get(key) or tree_map.get(key.removeprefix('preprints/'))
        assert source and source['type'] == 'blob', key
        path = R / 'packet/private/admitted/packet/private/canonical' / key
        raw = path.read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        assert len(raw) == entry['bytes'] == source['size']
        assert blob == entry['git_blob'] == source['sha']
        assert sha(raw) == entry['sha256']

    history = after['original_history_extents']
    assert len(history) == 3
    expected_history = {e['path']: e for e in inputs['original_history_direct_extents']}
    for entry in history:
        expected = expected_history[entry['path']]
        start, end = entry['byte_extent_half_open']
        with (P / entry['path']).open('rb') as stream:
            stream.seek(start)
            raw = stream.read(end - start)
        assert len(raw) == entry['bytes'] == expected['bytes']
        assert sha(raw) == entry['sha256'] == expected['sha256']
        assert (P / entry['path']).stat().st_mode == entry['mode']

    extents = read_json(R / 'packet/private/independent-read-extents.json')
    extent_receipts = []
    for entry in extents:
        start, end = entry.get('bytes_half_open', entry.get('byte_extent_half_open'))
        assert 0 <= start <= end
        if entry['path'] in expected_history:
            with (P / entry['path']).open('rb') as stream:
                stream.seek(start)
                selected = stream.read(end - start)
            assert len(selected) == end - start
            assert sha(selected) == entry['sha256']
            extent_receipts.append({'path': entry['path'], 'hash_scope': 'authorized extent',
                                    'extent_sha256': sha(selected)})
            continue
        path = R / entry['path']
        raw = path.read_bytes()
        assert end <= len(raw), entry['path']
        selected = raw[start:end]
        scope = 'extent' if sha(selected) == entry['sha256'] else 'whole file'
        assert sha(selected) == entry['sha256'] or sha(raw) == entry['sha256'], entry['path']
        extent_receipts.append({'path': entry['path'], 'hash_scope': scope,
                                'extent_sha256': sha(selected)})
        if 'lines_inclusive' in entry:
            first, last = entry['lines_inclusive']
            lines = raw.splitlines(keepends=True)
            assert b''.join(lines[first - 1:last]) == selected, entry['path']
    visuals = read_json(R / 'packet/private/visual-inspections.json')
    for entry in visuals:
        assert sha((R / entry['path']).read_bytes()) == entry['sha256']
        if 'render' in entry:
            assert (R / entry['render']).is_file()

    controls = read_json(R / 'packet/notes/control-results.json')
    assert controls['source_unchanged']
    assert [x['actual_exit'] for x in controls['results']] == [0, 1, 1]
    assert all(x['actual_exit'] == x['expected_exit'] for x in controls['results'])
    baseline = read_json(D / 'integration-baseline.json')
    for path, expected in baseline['protected'].items():
        assert sha((P / path).read_bytes()) == expected
    (D / 'private/read-extent-authentication.json').write_text(
        json.dumps(extent_receipts, indent=2) + '\n')
    print(json.dumps({
        'result': 'MATCH', 'integrity_only': True,
        'review_payload_files': 158, 'review_payload_bytes': 5307484,
        'review_whole_root_files': review_files,
        'author_whole_root_files_unchanged': author_files,
        'admitted_author_originals_and_copies_unchanged': 127,
        'canonical_blobs_independently_matched': len(canonical),
        'original_history_extents_matched': len(history),
        'reviewer_read_extent_receipts_authenticated': len(extents),
        'read_extent_receipts_with_whole_file_hash': sum(
            x['hash_scope'] == 'whole file' for x in extent_receipts),
        'reviewer_visual_receipts_authenticated': len(visuals),
        'parent_semantically_reread_source_or_primary_bodies': False,
        'saved_copied_controls_checked_not_rerun': [0, 1, 1],
        'anchors': ANCHORS, 'verifier_output': completed.stdout.strip(),
        'directory_membership_not_claimed_by_file_manifest': True,
    }, indent=2))


if __name__ == '__main__':
    main()
