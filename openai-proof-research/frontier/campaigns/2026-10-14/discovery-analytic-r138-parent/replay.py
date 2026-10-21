#!/usr/bin/env python3
"""Parent H138 author-proof intake; byte evidence only."""
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
ROOT = BASE / 'fresh-analytic-discovery-r138'
spec = importlib.util.spec_from_file_location('snapshot_helpers', BASE / 'discovery-structural-r144-parent/replay.py')
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
sha, snap = helper.sha, helper.snap
ANCHORS = {'FINAL.json': 'a68c6359d92b71b9758765b5a1bc8bb5d160e5969e4498dd1f15ad0cb73d5a85',
           'MANIFEST.json': '6fd9009523d53e032fa1e7ad77421cb26a36f8f618a1106c29cc447da66dee50',
           'REPORT.md': '55182bd2a37581e2ada1938db32d51a279d9f59940e805b5d97728c4fe4889e2'}
SCOPE = '82e7f37c36205cc62e52fc6ad037072706405efb7302dafa395747a2c5b2ff53'
PROOF = 'fc1228c5dc20b373fcba3b176ccb6b26e30bc099647e4dc8d5762a3833355258'
DERIVATION = '948045c339782a0d46f1cd86eba05df10fef5c6f106e98b64393412fbe868a31'


def dump(n, v):
    (OUT / n).write_text(json.dumps(v, indent=2) + '\n')


def main():
    assert not subprocess.check_output(['git', 'diff', '--cached', '--name-only'], cwd=PROJECT)
    assert all(sha(PROJECT / p) == h for p, h in helper.PROTECTED.items())
    now = datetime.datetime.now(datetime.timezone.utc).isoformat()
    dump('integration-baseline.json', {'observed_utc': now,
         'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=PROJECT, text=True).strip(),
         'initial_index_empty': True, 'task_count': 482, 'task_index': 478,
         'protected_unrelated_sha256': helper.PROTECTED})
    before = snap(ROOT)
    dump('observed-root.json', {'observed_utc': now, 'root': before,
         'limits': 'Current complete actual root after prose/code reads; not historical whole-parent/OS evidence.'})
    assert all(sha(ROOT / p) == h for p, h in ANCHORS.items())
    assert sha(ROOT / 'H-SCOPE.md') == SCOPE and sha(ROOT / 'AUTHOR-PROOF.md') == PROOF
    assert sha(ROOT / 'DERIVATION.md') == DERIVATION
    m = json.loads((ROOT / 'MANIFEST.json').read_text())
    assert m['schema'] == 1
    assert {p for p, e in before.items() if e['kind'] == 'file'} == set(m['files']) | set(ANCHORS)
    assert {p for p, e in before.items() if e['kind'] == 'directory'} == set(m['directories'])
    for p, e in m['files'].items():
        assert sha(ROOT / p) == e['sha256'] and (ROOT / p).stat().st_size == e['size']
    tp = PROJECT / 'sources/preprints-tree.json'
    assert sha(tp) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree = json.loads(tp.read_text())
    assert len(tree['tree']) == 13223 and tree['truncated'] is False
    entries = {e['path']: e for e in tree['tree']}
    sources = json.loads((ROOT / 'source-ledger.json').read_text())
    for e in sources:
        b = (ROOT / e['local_path']).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        assert blob == e['git_blob'] == entries[e['canonical_path']]['sha']
        assert len(b) == e['size'] == entries[e['canonical_path']]['size']
        assert sha(ROOT / e['local_path']) == e['sha256']
        assert e['url'] == 'https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' + e['canonical_path']
    primaries = json.loads((ROOT / 'primary-ledger.json').read_text())
    for e in primaries:
        assert e['url'] == 'https://arxiv.org/src/' + e['id']
        assert sha(ROOT / e['local_path']) == e['sha256'] and (ROOT / e['local_path']).stat().st_size == e['size']
        for v in e['extracts']:
            assert sha(ROOT / v['path']) == v['sha256'] and (ROOT / v['path']).stat().st_size == v['size']
    originals = []
    for e in json.loads((ROOT / 'original-ledger.json').read_text()):
        assert sha(ROOT / e['local_snapshot']) == e['sha256']
        h = sha(PROJECT / e['canonical_project_path'])
        mutable = e['canonical_project_path'] == 'frontier/NEW-TEN-2026-10-14.md'
        if not mutable:
            assert h == e['sha256'], e['canonical_project_path']
        originals.append(dict(e, parent_current_sha256=h, mutable_observation=mutable,
                              parent_matches_late_snapshot=h == e['sha256']))
    cases = []
    with tempfile.TemporaryDirectory(prefix='h138-author-copy-', dir=OUT) as temp:
        copy = Path(temp) / 'packet'
        shutil.copytree(ROOT, copy)
        args = ['--root', str(copy), '--manifest-sha256', ANCHORS['MANIFEST.json'],
                '--final-sha256', ANCHORS['FINAL.json'], '--report-sha256', ANCHORS['REPORT.md']]

        def check(label, expected, custom=None):
            state = snap(copy)
            r = subprocess.run([sys.executable, '-B', str(copy / 'verify.py'), *(custom or args)],
                               capture_output=True, text=True, timeout=30)
            assert (r.returncode == 0) == expected, (label, r.stdout, r.stderr)
            assert snap(copy) == state
            cases.append(dict(case=label, expected_pass=expected, returncode=r.returncode,
                              fixture_unchanged=True, stdout=r.stdout.strip(), stderr=r.stderr.strip()))

        check('baseline', True)
        p = copy / 'AUTHOR-PROOF.md'
        b = p.read_bytes()
        p.write_bytes(b + b'\nCONTROL\n')
        check('modified_proof_payload', False)
        p.unlink()
        check('missing_proof_payload', False)
        p.write_bytes(b)
        p = copy / '.extra-control.json'
        p.write_text('{}')
        check('extra_hidden_payload', False)
        p.unlink()
        wrong = args.copy()
        wrong[5] = '0' * 64
        check('wrong_external_final_anchor', False, wrong)
        check('restored', True)
        assert snap(copy) == before
    assert snap(ROOT) == before
    assert all(sha(PROJECT / e['canonical_project_path']) == e['parent_current_sha256'] for e in originals)
    assert all(sha(PROJECT / p) == h for p, h in helper.PROTECTED.items())
    dump('copied-controls.json', {'cases': cases, 'positive_cases': 2, 'negative_cases': 4,
         'copy_removed': True, 'actual_root_unchanged': True, 'limits': 'Byte/membership checks only, no mathematical gate.'})
    dump('replay.json', {'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'external_handoff_anchors': ANCHORS, 'frozen_scope_sha256': SCOPE, 'author_proof_sha256': PROOF,
         'prefreeze_derivation_sha256': DERIVATION, 'payload_files': len(m['files']),
         'whole_root_files': sum(e['kind'] == 'file' for e in before.values()),
         'pinned_source_blobs': len(sources), 'primary_raw_versions': len(primaries),
         'current_named_originals': originals, 'late_stable_inputs': 12, 'mutable_observations': 1,
         'artifact_cases': 6, 'negative_cases': 4, 'actual_root_unchanged': True,
         'selected_originals_unchanged_over_execution': True, 'protected_unrelated_files_unchanged': True,
         'limits': 'Parent current artifact/selected-input evidence only; no independent correctness/contribution, historical whole-parent/OS, full primary/history reading or priority certificate.'})
    print(json.dumps({'payload_files': len(m['files']), 'source_blobs': len(sources),
                      'primary_versions': len(primaries), 'stable_inputs': 12, 'mutable_observations': 1,
                      'artifact_cases': 6, 'negative_cases': 4, 'whole_root_unchanged': True}))


if __name__ == '__main__':
    main()
