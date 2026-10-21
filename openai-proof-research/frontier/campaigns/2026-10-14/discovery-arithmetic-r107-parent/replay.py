#!/usr/bin/env python3
"""Parent archive checks; retained question is unproved and ungraded."""
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
ROOT = BASE / 'fresh-arithmetic-discovery-r107'
HELPER = BASE / 'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py'
spec = importlib.util.spec_from_file_location('byte_helpers', HELPER)
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
sha, snap = helper.sha, helper.snap
ANCHORS = {
    'FINAL.md': 'f0b186944d9bc4938fe53c96adb15b3fd12b2415a4272c2c01924583f1a5835b',
    'MANIFEST.json': '55d83c42b0136170851cf5d109b67e0f25ca6312bd979df9df8e61e9d8eb6659',
    'REPORT.md': 'a5ed3c176dc148a2aa4798f227a452059c327724e3998f5c4198cc2053a802d2',
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
         'initial_index_empty': True, 'task_count': 475, 'task_index': 472,
         'protected_unrelated_sha256': PROTECTED})
    before = snap(ROOT)
    dump('observed-root.json', {'observed_utc': now, 'root': before,
         'limits': 'Current actual root after prose/code reads,before copied execution;no historical whole-parent claim.'})
    assert all(sha(ROOT / p) == h for p, h in ANCHORS.items())
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
    assert manifest['format'] == 'r107-exact-payload-v1'
    for e in manifest['files']:
        assert sha(ROOT / e['path']) == e['sha256'] and (ROOT / e['path']).stat().st_size == e['size']
    original = (ROOT / 'controls/verify.py').read_text()
    old = "    assert names==sorted(set(names)), 'duplicates or order'\n    assert names==inventory(root), 'exact inventory mismatch'"
    new = "    assert len(names)==len(set(names)), 'duplicates'\n    assert sorted(names)==inventory(root), 'exact inventory mismatch'"
    assert original.count(old) == 1
    corrected = original.replace(old, new)
    assert corrected.encode() == (ROOT / 'scratch/verify-order-corrected.py').read_bytes()
    assert sha(ROOT / 'scratch/verify-order-corrected.py') == '169883df28fba59e92c783e67000fb2b000012f6a95a4e4abbebffb24bcc2516'
    treepath = PROJECT / 'sources/preprints-tree.json'
    assert sha(treepath) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree = json.loads(treepath.read_text())
    assert len(tree['tree']) == 13223 and tree['truncated'] is False
    index = {e['path']: e for e in tree['tree']}
    sources = json.loads((ROOT / 'private/source-metadata.json').read_text())
    for e in sources:
        p = ROOT / e['local']
        b = p.read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        assert blob == e['gitblob'] == index[e['path']]['sha']
        assert len(b) == e['size'] == index[e['path']]['size'] and sha(p) == e['sha256']
        assert '/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' in e['url']
    primaries = []
    special = {'primary-conlon-metadata.json': 'conlon-et-al', 'primary-cfp-metadata.json': 'conlon-fox-pham', 'primary-bg-metadata.json': 'bourgain-garaev-v1'}
    for name in ['primary-metadata.json', 'primary-more-metadata.json', *special]:
        rows = json.loads((ROOT / 'private' / name).read_text())
        if isinstance(rows, dict):
            rows = [dict(rows, name=special[name])]
        for e in rows:
            if e['status'] == 'acquired':
                p = ROOT / 'private/primary' / (e['name'] + '.pdf')
                assert sha(p) == e['sha256'] and p.stat().st_size == e['size']
            primaries.append(e)
    current = []
    for e in json.loads((ROOT / 'private/original-checks.json').read_text())['files']:
        assert sha(ROOT / e['local']) == e['sha256']
        h = sha(PROJECT / e['original'])
        mutable = e['original'] == 'frontier/NEW-TEN-2026-10-14.md'
        if not mutable:
            assert h == e['sha256']
        current.append(dict(e, parent_current_sha256=h, parent_matches_late_copy=h == e['sha256'], mutable_observation=mutable))
    controls = []
    with tempfile.TemporaryDirectory(prefix='arithmetic107-copy-', dir=OUT) as temp:
        copy = Path(temp) / 'r107'
        shutil.copytree(ROOT, copy)
        args = ['--root', str(copy), '--final-sha', ANCHORS['FINAL.md'], '--manifest-sha', ANCHORS['MANIFEST.json'], '--report-sha', ANCHORS['REPORT.md']]

        def check(label, expected, verifier='scratch/verify-order-corrected.py', custom=None):
            state = snap(copy)
            proc = subprocess.run([sys.executable, '-B', str(copy / verifier), *(custom or args)], capture_output=True, text=True, timeout=30)
            assert (proc.returncode == 0) == expected, (label, proc.stdout, proc.stderr)
            assert snap(copy) == state
            controls.append({'case': label, 'expected_pass': expected, 'verifier': verifier, 'returncode': proc.returncode,
                             'fixture_unchanged': True, 'stdout': proc.stdout.strip(), 'stderr': proc.stderr.strip()})

        check('original_ordering_defect_on_valid_payload', False, 'controls/verify.py')
        assert 'duplicates or order' in controls[-1]['stderr']
        check('corrected_baseline', True)
        p = copy / 'notes/squarefree-feasibility.md'
        b = p.read_bytes()
        p.write_bytes(b + b'\nCONTROL\n')
        check('modified_payload', False)
        p.unlink()
        check('missing_payload', False)
        p.write_bytes(b)
        p = copy / 'private/extra-control'
        p.write_text('control')
        check('extra_declared_payload', False)
        p.unlink()
        wrong = args.copy()
        wrong[3] = '0' * 64
        check('wrong_detached_final', False, custom=wrong)
        p = copy / 'scratch/unlisted-control'
        p.write_text('outside declared manifest scope')
        check('scratch_excluded_by_declared_contract', True)
        p.unlink()
        check('restored', True)
        assert snap(copy) == before
    assert snap(ROOT) == before
    assert all(sha(PROJECT / e['original']) == e['parent_current_sha256'] for e in current)
    assert all(sha(PROJECT / p) == h for p, h in PROTECTED.items())
    dump('copied-controls.json', {'cases': controls, 'corrected_verifier_cases': 7,
         'corrected_corruption_negative_cases': 4, 'corrected_positive_cases': 3,
         'original_order_defect_reproduced': True, 'scratch_exclusion_demonstrated': True,
         'copy_removed': True, 'actual_root_unchanged': True})
    dump('replay.json', {'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'external_handoff_anchors': ANCHORS, 'payload_files': len(manifest['files']),
         'whole_root_files': sum(e['kind'] == 'file' for e in before.values()),
         'sealed_verifier_sha256': sha(ROOT / 'controls/verify.py'),
         'corrected_verifier_sha256': sha(ROOT / 'scratch/verify-order-corrected.py'),
         'correction_authentication': 'Exact two-assertion substitution from independently anchored sealed original;outside SHA256SUMS is convenience,not an external trust root.',
         'pinned_source_blobs': len(sources), 'primary_receipts': primaries,
         'successful_primary_pdfs': 8, 'failed_primary_requests': 1,
         'late_named_originals': current, 'artifact_cases': 8, 'corrected_verifier_cases': 7,
         'corrected_corruption_negative_cases': 4, 'original_order_defect_reproduced': True,
         'scratch_exclusion_demonstrated': True, 'actual_root_unchanged': True,
         'current_named_originals_unchanged_over_execution': True, 'protected_unrelated_files_unchanged': True,
         'snapshot_helper_sha256': sha(HELPER),
         'limits': 'Declared-payload byte checks only;corrected verifier,scratch,SHA256SUMS and outer artifact-controls are outside payload. Parent whole-root snapshot is separate current evidence,not mathematics,whole-primary/history reading,OS confinement,historical whole-parent preservation or priority.'})
    print(json.dumps({'payload_files': len(manifest['files']), 'source_blobs': len(sources),
                      'primary_pdfs': 8, 'late_originals': len(current), 'artifact_cases': 8,
                      'corruption_negatives': 4, 'order_defect_reproduced': True,
                      'exact_derived_correction_verified': True, 'actual_root_and_named_originals_unchanged': True}))


if __name__ == '__main__':
    main()
