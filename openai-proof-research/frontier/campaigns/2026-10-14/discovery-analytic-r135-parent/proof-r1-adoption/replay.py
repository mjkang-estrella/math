#!/usr/bin/env python3
"""Parent correctness packet intake; byte evidence is not a proof verdict."""
import datetime
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

OUT = Path(__file__).resolve().parent
BASE = OUT.parent.parent
PROJECT = BASE.parents[2]
ROOT = BASE / 't373e135-proof-r1'
AUTHOR = BASE / 'fresh-analytic-discovery-r135'
HELPER = OUT.parent / 'contribution-r1-adoption/replay.py'
spec = importlib.util.spec_from_file_location('parent_byte_helpers', HELPER)
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
sha, snap = helper.sha, helper.snap
ANCHORS = {
    'FINAL.md': '5b307a1f08704fc13ffb531a83efaa8c05eceaf5a198edc49c1ccd1036743a1d',
    'packet/MANIFEST.json': '8edcac770742de9288dffe8fdc03c6f94eaa8b3fb24cb96c70fd601e496a0da0',
    'REPORT.md': '6957c164b2b63e185837b5bbc08c3504a56db0c1e98fb48b84b5b128b38e61c2',
}


def dump(name, value):
    (OUT / name).write_text(json.dumps(value, indent=2) + '\n')


def main():
    now = datetime.datetime.now(datetime.timezone.utc).isoformat()
    before, author_before = snap(ROOT), snap(AUTHOR)
    dump('observed-roots.json', {'observed_utc': now, 'review_root': before,
                                'author_root': author_before,
                                'limits': 'Current roots after prose/code reading;no historical whole-parent claim.'})
    assert all(sha(ROOT / p) == h for p, h in ANCHORS.items())
    assert sha(ROOT / 'packet/public/verify_packet.py') == '510eeaa4139e1d1d3e9319e18d65a0cafcc963ee82881a00674ff3bd12d9a24e'
    baseline = json.loads((ROOT / 'packet/private/author-current-baseline.json').read_text())['files']
    assert len(baseline) == 89
    assert {p: {k: e[k] for k in ['bytes', 'sha256', 'mode', 'nlink']}
            for p, e in author_before.items() if e['kind'] == 'file'} == baseline
    selected = []
    for e in json.loads((ROOT / 'packet/private/selected-originals-baseline.json').read_text())['files']:
        assert sha(ROOT / 'packet' / e['copy']) == e['sha256']
        current = sha(PROJECT / e['path'])
        if not e['mutable_observation']:
            assert current == e['sha256']
        selected.append(dict(e, current_sha256=current, unchanged_since_review_snapshot=current == e['sha256']))
    selected_before = {e['path']: e['current_sha256'] for e in selected}
    tree_path = PROJECT / 'sources/preprints-tree.json'
    assert sha(tree_path) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree = json.loads(tree_path.read_text())
    assert len(tree['tree']) == 13223 and tree['truncated'] is False
    index = {e['path']: e for e in tree['tree']}
    sources = json.loads((ROOT / 'packet/private/source-authentication.json').read_text())['sources']
    for e in sources:
        p = AUTHOR / 'packet/private/upstream' / e['path']
        b = p.read_bytes()
        blob = helper.hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        assert len(b) == e['size'] == index[e['path']]['size']
        assert blob == e['git_blob'] == index[e['path']]['sha'] and sha(p) == e['sha256']
        copied = ROOT / 'packet/private/source373' / e['path']
        if copied.exists():
            assert copied.read_bytes() == b
    primary_rows = json.loads((ROOT / 'packet/private/primary-authentication.json').read_text())
    for e in primary_rows:
        p = AUTHOR / 'packet/private/primary' / (e['name'] + '.pdf')
        assert sha(p) == e['sha256'] and p.stat().st_size == e['size']
        original = AUTHOR / 'packet/private/primary' / (e['name'] + '.txt')
        for suffix in ['.txt', '.regenerated.txt']:
            assert (ROOT / 'packet/private/primary' / (e['name'] + suffix)).read_bytes() == original.read_bytes()
    for e in json.loads((ROOT / 'packet/private/incoming-authentication.json').read_text()):
        assert sha(PROJECT / e['path']) == e['sha256']
        relative = Path(e['path']).relative_to(AUTHOR.relative_to(PROJECT))
        assert sha(ROOT / 'packet/private/incoming' / relative) == e['sha256']
    controls = []
    with tempfile.TemporaryDirectory(prefix='correctness-copy-', dir=OUT) as temp:
        copy = Path(temp) / 'review'
        shutil.copytree(ROOT, copy)
        args = [sys.executable, '-B', str(copy / 'packet/public/verify_packet.py'), str(copy),
                '--final-sha', ANCHORS['FINAL.md'], '--manifest-sha', ANCHORS['packet/MANIFEST.json'],
                '--report-sha', ANCHORS['REPORT.md']]

        def check(name, expected):
            state = snap(copy)
            p = subprocess.run(args, capture_output=True, text=True, timeout=30)
            assert (p.returncode == 0) == expected, (name, p.stdout, p.stderr)
            assert snap(copy) == state
            controls.append({'case': name, 'expected_pass': expected, 'returncode': p.returncode,
                             'fixture_unchanged': True, 'stdout': p.stdout.strip(), 'stderr': p.stderr.strip()})

        check('baseline', True)
        for n in ['packet/public/review.md', 'packet/MANIFEST.json', 'FINAL.md', 'REPORT.md']:
            p = copy / n
            b = p.read_bytes()
            p.write_bytes(b + b'\nCONTROL\n')
            check('altered_' + n, False)
            p.write_bytes(b)
        p = copy / 'packet/private/incoming/packet/public/FROZEN-SCOPE.md'
        b, mode = p.read_bytes(), p.stat().st_mode & 0o777
        p.unlink()
        check('missing_incoming_scope', False)
        p.write_bytes(b)
        p.chmod(mode)
        p = copy / 'packet/extra'
        p.write_text('control')
        check('extra_payload', False)
        p.unlink()
        p.symlink_to('public/review.md')
        check('symlink_payload', False)
        p.unlink()
        check('restored', True)
        assert snap(copy) == before
    assert snap(ROOT) == before and snap(AUTHOR) == author_before
    assert all(sha(PROJECT / p) == h for p, h in selected_before.items())
    dump('copied-controls.json', {'cases': controls, 'positive_cases': 2, 'negative_cases': 7,
                                 'original_review_and_author_roots_unchanged': True})
    dump('replay.json', {'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                         'external_handoff_anchors': ANCHORS, 'payload_files': 62, 'author_files': 89,
                         'pinned_source_blobs': len(sources), 'copied_source373_blobs': 11,
                         'primary_pdf_receipts': primary_rows, 'matching_regenerated_extracts': 7,
                         'late_selected_originals': selected, 'artifact_cases': 9, 'negative_cases': 7,
                         'review_and_author_roots_unchanged': True, 'selected_inputs_unchanged_during_replay': True,
                         'snapshot_helper_sha256': sha(HELPER),
                         'limits': 'Artifact/current named-original observations only; no mathematical, OS enforcement, historic whole-parent or priority certificate.'})
    print(json.dumps({'payload_files': 62, 'author_files': 89, 'pinned_source_blobs': len(sources),
                      'primary_pdfs': len(primary_rows), 'late_originals': len(selected),
                      'artifact_cases': 9, 'negative_cases': 7, 'roots_unchanged': True}))


if __name__ == '__main__':
    main()
