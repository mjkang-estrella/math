#!/usr/bin/env python3
"""Parent archive authentication only; no mathematical gates."""
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
BASE = OUT.parent
PROJECT = BASE.parents[2]
ROOT = BASE / 'fresh-analytic-discovery-r136'
HELPER = BASE / 'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py'
spec = importlib.util.spec_from_file_location('archive_snapshot_helpers', HELPER)
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
sha, snap = helper.sha, helper.snap
ANCHORS = {
    'FINAL.md': '8d8fa0ec742ce9627c862733333ae312a70db273962e62321c694420fd4ed949',
    'MANIFEST.json': '17703a2f93af16950d48c6b5e3a9221868d9a6799b0460824c6555ad70015aff',
    'REPORT.md': '79f1cd1b5d31ebf37f9fe4807fac0fe0bee84e043baeb6a5d9134936200584cd',
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
         'initial_index_empty': True, 'task_count': 473, 'task_index': 471,
         'protected_unrelated_sha256': PROTECTED})
    before = snap(ROOT)
    dump('observed-root.json', {'observed_utc': now, 'root': before,
                              'limits': 'Present actual root after prose/code reads,before copied execution;not historical whole-parent preservation.'})
    assert all(sha(ROOT / p) == h for p, h in ANCHORS.items())
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
    assert manifest['schema'] == 'r136-exact-artifact-manifest-v1'
    for e in manifest['files']:
        assert sha(ROOT / e['path']) == e['sha256'] and (ROOT / e['path']).stat().st_size == e['size']
    tree = json.loads((PROJECT / 'sources/preprints-tree.json').read_text())
    assert len(tree['tree']) == 13223 and tree['truncated'] is False
    assert sha(PROJECT / 'sources/preprints-tree.json') == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    index = {e['path']: e for e in tree['tree']}
    sources = json.loads((ROOT / 'source-ledger.json').read_text())
    for e in sources:
        b = (ROOT / e['local_path']).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        assert blob == e['git_blob'] == index[e['canonical_path']]['sha']
        assert len(b) == e['size'] == index[e['canonical_path']]['size']
        assert sha(ROOT / e['local_path']) == e['sha256']
        assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in e['url']
    primaries = json.loads((ROOT / 'primary-ledger.json').read_text())
    for e in primaries:
        if 'error' in e:
            continue
        p = ROOT / 'private/primary' / e['id'] / 'source.download'
        assert sha(p) == e['sha256'] and p.stat().st_size == e['size']
        for row in e['files']:
            p = ROOT / row['path']
            assert sha(p) == row['sha256'] and p.stat().st_size == row['size']
    originals = json.loads((ROOT / 'current-original-checks.json').read_text())
    current = []
    for e in originals:
        assert sha(ROOT / e['copy_path']) == e['copy_sha256']
        h = sha(PROJECT / e['original_path'])
        if not e['mutable_campaign_ledger']:
            assert h == e['copy_sha256']
        current.append(dict(e, parent_current_sha256=h, parent_matches_copy=h == e['copy_sha256']))
    controls = []
    with tempfile.TemporaryDirectory(prefix='analytic136-copy-', dir=OUT) as temp:
        copy = Path(temp) / 'project/frontier/campaigns/2026-10-14/fresh-analytic-discovery-r136'
        shutil.copytree(ROOT, copy)
        args = ['--final-sha', ANCHORS['FINAL.md'], '--manifest-sha', ANCHORS['MANIFEST.json'], '--report-sha', ANCHORS['REPORT.md']]

        def check(label, expected, custom=None):
            state = snap(copy)
            p = subprocess.run([sys.executable, '-B', str(copy / 'verify.py'), *(custom or args)],
                               capture_output=True, text=True, timeout=30)
            assert (p.returncode == 0) == expected, (label, p.stdout, p.stderr)
            assert snap(copy) == state
            controls.append({'case': label, 'expected_pass': expected, 'returncode': p.returncode,
                             'fixture_unchanged': True, 'stdout': p.stdout.strip(), 'stderr': p.stderr.strip()})

        check('baseline', True)
        p = copy / 'DERIVATION.md'
        b = p.read_bytes()
        p.write_bytes(b + b'\nCONTROL\n')
        check('modified_payload', False)
        p.unlink()
        check('missing_payload', False)
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
    assert snap(ROOT) == before
    assert all(sha(PROJECT / e['original_path']) == e['parent_current_sha256'] for e in current)
    assert all(sha(PROJECT / p) == h for p, h in PROTECTED.items())
    dump('copied-controls.json', {'cases': controls, 'positive_cases': 2, 'negative_cases': 4,
         'copy_removed': True, 'actual_root_unchanged': True,
         'limits': 'Verifier current-original paths resolve inside disposable project and report missing inputs without gating;parent separately checks actual named originals.'})
    dump('replay.json', {'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'external_handoff_anchors': ANCHORS, 'verifier_sha256': sha(ROOT / 'verify.py'),
         'payload_files': len(manifest['files']), 'whole_root_files': sum(e['kind'] == 'file' for e in before.values()),
         'pinned_source_blobs': len(sources), 'primary_acquired_versions': 3, 'primary_failed_versions': 1,
         'primary_ledger': primaries, 'current_named_originals': current, 'stable_inputs': 6, 'mutable_observations': 1,
         'artifact_cases': 6, 'negative_cases': 4, 'actual_root_unchanged': True,
         'current_named_originals_unchanged_over_execution': True, 'protected_unrelated_files_unchanged': True,
         'snapshot_helper_sha256': sha(HELPER), 'diagnostic_execution': 'NOT_RERUN_FLOATING_POINT_FAILURE_PROBE',
         'limits': 'Artifact/current selected-input evidence only;no independent mathematics,contribution,whole-primary read,OS enforcement,history clearance or priority gate.'})
    print(json.dumps({'payload_files': len(manifest['files']), 'source_blobs': len(sources),
                      'primary_versions': 3, 'artifact_cases': 6, 'negative_cases': 4,
                      'actual_root_and_named_originals_unchanged': True}))


if __name__ == '__main__':
    main()
