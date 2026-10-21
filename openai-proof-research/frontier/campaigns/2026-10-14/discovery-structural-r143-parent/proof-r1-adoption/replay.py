#!/usr/bin/env python3
"""Parent correctness packet evidence intake; no contribution or acceptance gate."""
import datetime
import hashlib
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
ROOT = BASE / 't177c143-proof-r1'
AUTHOR = BASE / 'fresh-structural-discovery-r143'
HELPER = BASE / 'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py'
spec = importlib.util.spec_from_file_location('snapshot_helpers', HELPER)
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
sha, snap = helper.sha, helper.snap
ANCHORS = {
    'FINAL.json': 'c05e15d53b9becec63ea9d02fec364b2bd5d111ff2a02b48e2cc9a2e8c51417d',
    'MANIFEST.json': 'b58f6503a3fd544141a580104672a43552f0abb32234e7a58acf2ff4bc069e6c',
    'REPORT.md': '02fcd0e3f7ff6daf4bf373e4ed5a530d30404fa89058b792c05fc066276f37db',
}
PROTECTED = {
    'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json': '6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9',
    'frontier/iterations/i31-nonconical-no-mcm.md': 'd606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a',
}


def dump(name, value):
    (OUT / name).write_text(json.dumps(value, indent=2) + '\n')


def main():
    now = datetime.datetime.now(datetime.timezone.utc).isoformat()
    assert not subprocess.check_output(['git', 'diff', '--cached', '--name-only'], cwd=PROJECT)
    assert all(sha(PROJECT / p) == h for p, h in PROTECTED.items())
    dump('integration-baseline.json', {'observed_utc': now,
         'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=PROJECT, text=True).strip(),
         'initial_index_empty': True, 'task_count': 477, 'task_index': 475,
         'protected_unrelated_sha256': PROTECTED})
    before, author_before = snap(ROOT), snap(AUTHOR)
    dump('observed-roots.json', {'observed_utc': now, 'review_root': before, 'author_root': author_before,
         'limits': 'Current actual roots after prose/code and named primary reads;no historical whole-parent claim.'})
    assert all(sha(ROOT / p) == h for p, h in ANCHORS.items())
    final = json.loads((ROOT / 'FINAL.json').read_text())
    for label in ['verifier']:
        assert sha(ROOT / final[label + '_path']) == final[label + '_sha256']
    assert final['reviewed_scope_sha256'] == sha(AUTHOR / 'packet/public/frozen-scope.md') == 'cc916afef1373c1b3c0abdee271a4c2769f887f664e8c9b2b16b1b381c0de221'
    recorded = {e['path']: e['sha256'] for e in json.loads((ROOT / 'packet/private/incoming-observation.json').read_text())['files']}
    assert len(recorded) == 89
    assert {p: e['sha256'] for p, e in author_before.items() if e['kind'] == 'file'} == recorded
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
    for e in manifest['files']:
        p = ROOT / e['path']
        assert sha(p) == e['sha256'] and p.stat().st_size == e['bytes']
    treepath = PROJECT / 'sources/preprints-tree.json'
    assert sha(treepath) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree = json.loads(treepath.read_text())
    assert len(tree['tree']) == 13223 and tree['truncated'] is False
    index = {e['path']: e for e in tree['tree']}
    sources = json.loads((ROOT / 'packet/private/source-authentication.json').read_text())['files']
    for e in sources:
        p = ROOT / 'packet/private/reacquired-upstream' / e['path']
        b = p.read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        assert blob == e['git_blob'] == index[e['path']]['sha']
        assert len(b) == e['tree_size'] == index[e['path']]['size'] and sha(p) == e['sha256']
        assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in e['url']
    incoming = ROOT / 'packet/private/incoming-author'
    incoming_manifest = json.loads((incoming / 'MANIFEST.json').read_text())
    assert sha(incoming / 'MANIFEST.json') == '91c271ce12b36624b6123bc9f652c42f0a58ff55dfb9190c94f5330cca2704a6'
    for e in incoming_manifest['files']:
        p = incoming / e['path']
        assert sha(p) == e['sha256'] and p.stat().st_size == e['bytes']
    primary_rows = json.loads((ROOT / 'packet/private/primary-authentication.json').read_text())
    for e in primary_rows:
        if 'failure' not in e:
            p = incoming / 'packet/private/primary' / (e['name'] + '.pdf')
            assert sha(p) == e['sha256'] and p.stat().st_size == e['size']
    extra = json.loads((ROOT / 'packet/private/primary-extra/acquisition.json').read_text())
    p = ROOT / 'packet/private/primary-extra/frt-journal.pdf'
    assert sha(p) == extra['sha256'] and p.stat().st_size == extra['bytes']
    primary_rows.append(dict(extra, local_pdf='frt-journal.pdf'))
    current = []
    for e in json.loads((ROOT / 'packet/private/current-originals-observation.json').read_text())['files']:
        assert sha(ROOT / e['copy']) == e['sha256']
        h = sha(PROJECT / e['original'])
        mutable = e['original'] == 'frontier/NEW-TEN-2026-10-14.md'
        if not mutable:
            assert h == e['sha256']
        current.append(dict(e, parent_current_sha256=h, parent_matches_late_copy=h == e['sha256'], mutable_observation=mutable))
    controls = []
    with tempfile.TemporaryDirectory(prefix='correctness-copy-', dir=OUT) as temp:
        copy = Path(temp) / 'review'
        shutil.copytree(ROOT, copy)
        args = ['--final-sha256', ANCHORS['FINAL.json'], '--manifest-sha256', ANCHORS['MANIFEST.json'], '--report-sha256', ANCHORS['REPORT.md']]

        def check(label, expected, custom=None):
            state = snap(copy)
            proc = subprocess.run([sys.executable, '-B', str(copy / 'packet/public/verify.py'), str(copy), *(custom or args)], capture_output=True, text=True, timeout=30)
            assert (proc.returncode == 0) == expected, (label, proc.stdout, proc.stderr)
            assert snap(copy) == state
            controls.append({'case': label, 'expected_pass': expected, 'returncode': proc.returncode,
                             'fixture_unchanged': True, 'stdout': proc.stdout.strip(), 'stderr': proc.stderr.strip()})

        check('baseline', True)
        p = copy / 'packet/public/review.md'
        b = p.read_bytes()
        p.write_bytes(b + b'\nCONTROL\n')
        check('modified_review', False)
        p.unlink()
        check('missing_review', False)
        p.write_bytes(b)
        p = copy / 'extra-control'
        p.write_text('control')
        check('extra_payload', False)
        p.unlink()
        wrong = args.copy()
        wrong[1] = '0' * 64
        check('wrong_detached_final', False, wrong)
        check('restored', True)
        assert snap(copy) == before
    assert snap(ROOT) == before and snap(AUTHOR) == author_before
    assert all(sha(PROJECT / e['original']) == e['parent_current_sha256'] for e in current)
    assert all(sha(PROJECT / p) == h for p, h in PROTECTED.items())
    dump('copied-controls.json', {'cases': controls, 'positive_cases': 2, 'negative_cases': 4,
         'copy_removed': True, 'review_and_author_roots_unchanged': True,
         'limits': 'Original synthetic-control writer read,not executed against its original root;artifact evidence only.'})
    dump('replay.json', {'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'external_handoff_anchors': ANCHORS, 'payload_files': len(manifest['files']),
         'review_root_files': sum(e['kind'] == 'file' for e in before.values()), 'author_files': 89,
         'author_root_matches_review_snapshot': True, 'pinned_source_blobs': len(sources),
         'primary_receipts': primary_rows, 'primary_pdfs_checked': 9, 'incoming_primary_pdfs_included': 8,
         'incoming_payload_files_rechecked': len(incoming_manifest['files']),
         'late_named_originals': current, 'stable_inputs': 20, 'mutable_observations': 1,
         'artifact_cases': 6, 'negative_cases': 4, 'review_and_author_roots_unchanged': True,
         'current_named_originals_unchanged_over_execution': True, 'protected_unrelated_files_unchanged': True,
         'snapshot_helper_sha256': sha(HELPER),
         'limits': 'Byte/metadata observations only;no new correctness,acceptance,whole-primary/history read,OS confinement,historical whole-parent or priority gate.'})
    print(json.dumps({'payload_files': len(manifest['files']), 'author_files': 89, 'source_blobs': len(sources),
                      'primary_pdfs': 9, 'incoming_pdfs_included': 8, 'late_originals': len(current),
                      'artifact_cases': 6, 'negative_cases': 4, 'roots_and_named_originals_unchanged': True}))


if __name__ == '__main__':
    main()
