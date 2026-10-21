#!/usr/bin/env python3
"""Parent archive authentication only; no mathematical or contribution gate."""
import datetime
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
ROOT = BASE / 'fresh-arithmetic-discovery-r108'
HELPER = BASE / 'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py'
spec = importlib.util.spec_from_file_location('archive_snapshot_helpers', HELPER)
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
sha, snap = helper.sha, helper.snap
ANCHORS = {
    'FINAL.md': '1c5dbc6d7fa5a3e356926ba813fd33dee459558415ef3fb76220d837b1b46226',
    'MANIFEST.json': 'bca4f70a8528b9666b756a8a2363544e0b3bfa0d3bdff5c499d445a9a5721154',
    'REPORT.md': '56c37a1137d3fd8331bf7f436c752dc3d3793c7055e2db1e69f1a4e1772be31d',
}
PROTECTED = {
    'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json': '6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9',
    'frontier/iterations/i31-nonconical-no-mcm.md': 'd606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a',
}


def dump(name, value):
    (OUT / name).write_text(json.dumps(value, indent=2) + '\n')


def main():
    assert not subprocess.check_output(['git', 'diff', '--cached', '--name-only'], cwd=PROJECT)
    assert all(sha(PROJECT / p) == h for p, h in PROTECTED.items())
    now = datetime.datetime.now(datetime.timezone.utc).isoformat()
    dump('integration-baseline.json', {'observed_utc': now,
         'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=PROJECT, text=True).strip(),
         'initial_index_empty': True, 'task_count': 479, 'task_index': 477,
         'protected_unrelated_sha256': PROTECTED,
         'tasks_sha256': sha(BASE / 'tasks.json'),
         'journal_sha256': sha(PROJECT / 'frontier/NEW-TEN-2026-10-14.md')})
    before = snap(ROOT)
    dump('observed-root.json', {'observed_utc': now, 'root': before,
         'limits': 'Current whole actual root including omitted copied fixtures; no historical whole-parent or OS claim.'})
    assert all(sha(ROOT / p) == h for p, h in ANCHORS.items())
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
    assert manifest['format'] == 'r108-exact-v1' and len(manifest['files']) == 121
    assert manifest['omitted_subtree'] == 'scratch/copied-controls'
    for p, e in manifest['files'].items():
        assert sha(ROOT / p) == e['sha256'] and (ROOT / p).stat().st_size == e['bytes']
    expected = set(manifest['files']) | set(manifest['outside_files'])
    assert {p for p, e in before.items() if e['kind'] == 'file' and not p.startswith('scratch/copied-controls/')} == expected
    selected = json.loads((ROOT / 'private/input-authentication.json').read_text())['current_originals']
    for e in selected:
        assert sha(PROJECT / e['path']) == e['sha256'], e['path']
    primary = json.loads((ROOT / 'private/primary-metadata.json').read_text())
    for e in primary:
        assert (ROOT / 'private/primary' / (e['name'] + '.pdf')).stat().st_size == e['bytes']
    walsh = json.loads((ROOT / 'private/walsh-metadata.json').read_text())
    assert (ROOT / 'private/primary/walsh2014v2.pdf').stat().st_size == walsh['bytes']
    cases = []
    with tempfile.TemporaryDirectory(prefix='arithmetic108-copy-', dir=OUT) as temp:
        copy = Path(temp) / 'packet'
        for p in sorted(expected):
            dst = copy / p
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / p, dst)
        pristine = snap(copy)
        args = ['--root', str(copy), '--final-sha', ANCHORS['FINAL.md'],
                '--manifest-sha', ANCHORS['MANIFEST.json'], '--report-sha', ANCHORS['REPORT.md']]

        def check(label, expected_pass, custom=None):
            state = snap(copy)
            result = subprocess.run([sys.executable, '-B', str(copy / 'controls/verify.py'), *(custom or args)],
                                    capture_output=True, text=True, timeout=30)
            assert (result.returncode == 0) == expected_pass, (label, result.stdout, result.stderr)
            assert snap(copy) == state
            cases.append(dict(case=label, expected_pass=expected_pass, returncode=result.returncode,
                              fixture_unchanged=True, stdout=result.stdout.strip(), stderr=result.stderr.strip()))

        check('baseline_full_declared_packet', True)
        auth = subprocess.run([sys.executable, '-B', str(copy / 'controls/authenticate_inputs.py'),
                               '--root', str(copy), '--project', str(PROJECT)],
                              capture_output=True, text=True, timeout=30)
        assert auth.returncode == 0, (auth.stdout, auth.stderr)
        authentication = json.loads(auth.stdout)
        assert authentication['authenticated_source_files'] == 67
        assert authentication['authenticated_primary_pdf_text_pairs'] == 4
        assert len(authentication['current_originals']) == 15
        assert snap(copy) == pristine
        diag = subprocess.run([sys.executable, '-B', str(copy / 'controls/check_capacities.py')],
                              capture_output=True, text=True, timeout=30)
        assert diag.returncode == 0, (diag.stdout, diag.stderr)
        assert json.loads(diag.stdout) == json.loads((ROOT / 'notes/capacity-diagnostics.json').read_text())
        assert snap(copy) == pristine
        p = copy / 'notes/visibility-feasibility.md'
        b = p.read_bytes()
        p.write_bytes(b + b'\nCONTROL\n')
        check('modified_payload', False)
        p.unlink()
        check('missing_payload', False)
        p.write_bytes(b)
        p = copy / 'private/.extra-control.json'
        p.write_text('{}')
        check('extra_hidden_payload', False)
        p.unlink()
        wrong = args.copy()
        wrong[3] = '0' * 64
        check('wrong_external_final_anchor', False, wrong)
        check('restored', True)
        assert snap(copy) == pristine
    assert snap(ROOT) == before
    assert all(sha(PROJECT / e['path']) == e['sha256'] for e in selected)
    assert all(sha(PROJECT / p) == h for p, h in PROTECTED.items())
    dump('copied-controls.json', {'cases': cases, 'positive_cases': 2, 'negative_cases': 4,
         'copy_removed': True, 'whole_actual_root_unchanged': True,
         'limits': 'Copied packet contains all declared payloads and five envelopes; author disposable subtree intentionally omitted. Not a mathematical gate.'})
    dump('input-authentication.json', authentication)
    dump('capacity-diagnostic-replay.json', json.loads(diag.stdout))
    dump('replay.json', {'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'external_handoff_anchors': ANCHORS, 'verifier_sha256': sha(ROOT / 'controls/verify.py'),
         'payload_files': len(manifest['files']), 'whole_root_files': sum(e['kind'] == 'file' for e in before.values()),
         'pinned_source_blobs': 67, 'primary_pdf_text_pairs': 4,
         'current_named_originals': selected, 'early_controls': 3, 'late_stable_snapshots': 12,
         'missing_capture': 'Wrong r19/checkpoint path retained as missing; correct payload/checkpoint separately captured.',
         'artifact_cases': 6, 'negative_cases': 4, 'finite_capacity_cases': 80, 'explicit_crt_witnesses': 3,
         'whole_actual_root_unchanged': True, 'named_originals_unchanged_over_execution': True,
         'protected_unrelated_files_unchanged': True, 'snapshot_helper_sha256': sha(HELPER),
         'limits': 'Current bytes and bounded diagnostics only; no independent proof/contribution gate, whole-primary/history reading, historical isolation or priority claim.'})
    print(json.dumps({'payload_files': 121, 'source_blobs': 67, 'primary_pairs': 4,
                      'stable_inputs': 15, 'artifact_cases': 6, 'negative_cases': 4,
                      'finite_capacity_cases': 80, 'whole_root_unchanged': True}))


if __name__ == '__main__':
    main()
