#!/usr/bin/env python3
"""Parent byte/finite-diagnostic intake; not an independent mathematical gate."""
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
ROOT = BASE / 'fresh-structural-discovery-r143'
HELPER = BASE / 'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py'
spec = importlib.util.spec_from_file_location('snapshot_helpers', HELPER)
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
sha, snap = helper.sha, helper.snap
ANCHORS = {
    'FINAL.json': '9288d77635bae71c1f046d6372286db9785a9370bbc16cface9f9d8e532b1502',
    'MANIFEST.json': '91c271ce12b36624b6123bc9f652c42f0a58ff55dfb9190c94f5330cca2704a6',
    'REPORT.md': 'd553e9507b900c6251c33faf75c24bcb670518b8402547fe32a073feabc2ac2b',
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
         'initial_index_empty': True, 'task_count': 474, 'task_index': 470,
         'protected_unrelated_sha256': PROTECTED})
    before = snap(ROOT)
    dump('observed-root.json', {'observed_utc': now, 'root': before,
         'limits': 'Present actual root after prose/code/source reads,before copied execution;not historical whole-parent preservation.'})
    assert all(sha(ROOT / p) == h for p, h in ANCHORS.items())
    final = json.loads((ROOT / 'FINAL.json').read_text())
    assert sha(ROOT / final['verifier_path']) == final['verifier_sha256']
    assert sha(ROOT / final['frozen_scope_path']) == final['frozen_scope_sha256']
    assert sha(ROOT / 'packet/public/author-proof.md') == '10e6dda7b9824e629922e3cf6f42de1b2bc194803ace97eb774c7dd85858792a'
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
    for e in manifest['files']:
        assert sha(ROOT / e['path']) == e['sha256'] and (ROOT / e['path']).stat().st_size == e['bytes']
    treepath = PROJECT / 'sources/preprints-tree.json'
    assert sha(treepath) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree = json.loads(treepath.read_text())
    assert len(tree['tree']) == 13223 and tree['truncated'] is False
    index = {e['path']: e for e in tree['tree']}
    sources = json.loads((ROOT / 'packet/private/upstream-acquisition.json').read_text())
    for e in sources:
        p = ROOT / 'packet/private/upstream' / e['path']
        b = p.read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        assert blob == e['git_blob'] == index[e['path']]['sha']
        assert len(b) == e['size'] == index[e['path']]['size'] and sha(p) == e['sha256']
        assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in e['url']
    primaries = json.loads((ROOT / 'packet/private/primary/acquisition.json').read_text())
    for e in primaries:
        if 'failure' in e:
            continue
        p = ROOT / 'packet/private/primary' / (e['name'] + '.pdf')
        assert sha(p) == e['sha256'] and p.stat().st_size == e['size']
    originals = json.loads((ROOT / 'packet/private/current-originals-receipt.json').read_text())['files']
    current = []
    for e in originals:
        assert sha(ROOT / e['copy']) == e['sha256']
        h = sha(PROJECT / e['original'])
        mutable = e['original'] == 'frontier/NEW-TEN-2026-10-14.md'
        if not mutable:
            assert h == e['sha256']
        current.append(dict(e, parent_current_sha256=h, parent_matches_late_copy=h == e['sha256'], mutable_observation=mutable))
    controls = []
    with tempfile.TemporaryDirectory(prefix='structural143-copy-', dir=OUT) as temp:
        copy = Path(temp) / 'r143'
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
        p = copy / 'packet/public/author-proof.md'
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
        proc = subprocess.run([sys.executable, '-B', str(copy / 'packet/public/check_coherent.py')], capture_output=True, text=True, timeout=90)
        assert proc.returncode == 0, (proc.stdout, proc.stderr)
        diagnostic = json.loads(proc.stdout)
        assert diagnostic == json.loads((ROOT / 'packet/private/diagnostics-final.json').read_text())
        assert snap(copy) == before
        dump('copied-diagnostic.json', diagnostic)
    assert snap(ROOT) == before
    assert all(sha(PROJECT / e['original']) == e['parent_current_sha256'] for e in current)
    assert all(sha(PROJECT / p) == h for p, h in PROTECTED.items())
    dump('copied-controls.json', {'cases': controls, 'positive_cases': 2, 'negative_cases': 4,
         'copy_removed': True, 'actual_root_unchanged': True, 'limits': 'Artifact evidence only;original synthetic control writer was read,not run against original fixture.'})
    dump('replay.json', {'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'external_handoff_anchors': ANCHORS, 'verifier_sha256': final['verifier_sha256'],
         'scope_sha256': final['frozen_scope_sha256'], 'proof_sha256': sha(ROOT / 'packet/public/author-proof.md'),
         'payload_files': len(manifest['files']), 'whole_root_files': sum(e['kind'] == 'file' for e in before.values()),
         'pinned_source_blobs': len(sources), 'primary_pdf_receipts': primaries,
         'successful_primary_captures': 8, 'failed_primary_requests': 2,
         'late_named_originals': current, 'stable_inputs': 17, 'mutable_observations': 1,
         'artifact_cases': 6, 'negative_cases': 4, 'nonlinear_sampled_sections': 19,
         'pair_Fourier_checks': 157, 'upper_construction_inputs': 168,
         'actual_root_unchanged': True, 'current_named_originals_unchanged_over_execution': True,
         'protected_unrelated_files_unchanged': True, 'snapshot_helper_sha256': sha(HELPER),
         'limits': 'Byte/finite diagnostics only. No independent correctness,contribution,whole-primary/history read,OS confinement,historical whole-parent or priority gate.'})
    print(json.dumps({'payload_files': len(manifest['files']), 'source_blobs': len(sources),
                      'primary_pdfs': 8, 'late_originals': len(current), 'artifact_cases': 6,
                      'negative_cases': 4, 'sampled_sections': 19, 'Fourier_checks': 157,
                      'upper_inputs': 168, 'actual_root_and_named_originals_unchanged': True}))


if __name__ == '__main__':
    main()
