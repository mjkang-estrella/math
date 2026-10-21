#!/usr/bin/env python3
"""Parent archive checks; byte evidence only, no mathematical gates."""
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
ROOT = BASE / 'fresh-analytic-discovery-r137'
HELPER = BASE / 'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py'
spec = importlib.util.spec_from_file_location('archive_snapshot_helpers', HELPER)
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
sha, snap = helper.sha, helper.snap
ANCHORS = {
    'FINAL.md': 'ffde20519cc5067c68069085ab281e0d60b21ab38d0ba8c8c30a48a080e7e312',
    'MANIFEST.json': 'f1b62968c423ab6fe0e20bda13a96c1346229b0f14d8766a31c21c5d23da3e90',
    'REPORT.md': 'a415aa53735d61e8438ce0eed1a885a47280242a001df8de64a6ebc1cbcd2096',
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
    dump('integration-baseline.json', {
        'observed_utc': now,
        'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=PROJECT, text=True).strip(),
        'initial_index_empty': True, 'task_count': 478, 'task_index': 473,
        'protected_unrelated_sha256': PROTECTED,
        'tasks_sha256': sha(BASE / 'tasks.json'),
        'journal_sha256': sha(PROJECT / 'frontier/NEW-TEN-2026-10-14.md'),
    })
    before = snap(ROOT)
    dump('observed-root.json', {'observed_utc': now, 'root': before,
        'limits': 'Present actual root after prose/code reads, before copied execution; not historical whole-parent preservation.'})
    assert all(sha(ROOT / p) == h for p, h in ANCHORS.items())
    m = json.loads((ROOT / 'MANIFEST.json').read_text())
    assert m['schema'] == 'r137-artifact-v1'
    envelopes = {'FINAL.md', 'MANIFEST.json', 'REPORT.md', 'DETACHED-SHA256.json'}
    assert set(m['excluded_envelopes']) == envelopes
    assert {p for p, e in before.items() if e['kind'] == 'file'} - envelopes == {e['path'] for e in m['files']}
    for e in m['files']:
        assert sha(ROOT / e['path']) == e['sha256'] and (ROOT / e['path']).stat().st_size == e['size']
    tree_path = PROJECT / 'sources/preprints-tree.json'
    assert sha(tree_path) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree = json.loads(tree_path.read_text())
    assert len(tree['tree']) == 13223 and tree['truncated'] is False
    index = {e['path']: e for e in tree['tree']}
    sources = json.loads((ROOT / 'source-ledger.json').read_text())
    for e in sources:
        b = (ROOT / e['local']).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        assert blob == e['gitblob'] == index[e['path']]['sha']
        assert len(b) == e['size'] == index[e['path']]['size']
        assert sha(ROOT / e['local']) == e['sha256']
        assert e['url'] == 'https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' + e['path']
    primaries = json.loads((ROOT / 'primary-ledger.json').read_text())
    for e in primaries:
        assert e['url'] == 'https://arxiv.org/src/' + e['id']
        assert sha(ROOT / e['raw_local']) == e['sha256']
        assert (ROOT / e['raw_local']).stat().st_size == e['size']
        for v in e['members']:
            assert sha(ROOT / v['path']) == v['sha256']
            assert (ROOT / v['path']).stat().st_size == v['size']
    originals = []
    for e in json.loads((ROOT / 'original-ledger.json').read_text()):
        assert sha(ROOT / e['local']) == e['sha256']
        assert (ROOT / e['local']).stat().st_size == e['size']
        h = sha(PROJECT / e['path'])
        mutable = e['path'] == 'frontier/NEW-TEN-2026-10-14.md'
        if not mutable:
            assert h == e['sha256'], e['path']
        originals.append(dict(path=e['path'], snapshot_sha256=e['sha256'],
                              current_sha256=h, mutable_observation=mutable,
                              matches_late_snapshot=h == e['sha256']))
    cases = []
    with tempfile.TemporaryDirectory(prefix='analytic137-copy-', dir=OUT) as temp:
        copy = Path(temp) / 'packet'
        shutil.copytree(ROOT, copy)
        args = ['--root', str(copy), '--final-sha256', ANCHORS['FINAL.md'],
                '--manifest-sha256', ANCHORS['MANIFEST.json'], '--report-sha256', ANCHORS['REPORT.md']]

        def check(label, expected, custom=None):
            state = snap(copy)
            result = subprocess.run([sys.executable, '-B', str(copy / 'verify_readonly.py'), *(custom or args)],
                                    capture_output=True, text=True, timeout=30)
            assert (result.returncode == 0) == expected, (label, result.stdout, result.stderr)
            assert snap(copy) == state
            cases.append(dict(case=label, expected_pass=expected, returncode=result.returncode,
                              fixture_unchanged=True, stdout=result.stdout.strip(), stderr=result.stderr.strip()))

        check('baseline_full_packet', True)
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
        wrong[3] = '0' * 64
        check('wrong_external_final_anchor', False, wrong)
        p = copy / 'symlink-control'
        p.symlink_to('DERIVATION.md')
        check('symlink_member', False)
        p.unlink()
        check('restored', True)
        assert snap(copy) == before
    assert snap(ROOT) == before
    assert all(sha(PROJECT / e['path']) == e['current_sha256'] for e in originals)
    assert all(sha(PROJECT / p) == h for p, h in PROTECTED.items())
    dump('copied-controls.json', {'cases': cases, 'positive_cases': 2, 'negative_cases': 5,
         'copy_removed': True, 'actual_root_unchanged': True,
         'limits': 'Full packet byte/manifest/source-authentication branch checked; corruption controls are not mathematical gates.'})
    dump('replay.json', {'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'external_handoff_anchors': ANCHORS, 'verifier_sha256': sha(ROOT / 'verify_readonly.py'),
         'payload_files': len(m['files']), 'whole_root_files': sum(e['kind'] == 'file' for e in before.values()),
         'pinned_source_blobs': len(sources), 'primary_versions': len(primaries),
         'primary_parser_recovery': '1603.06037v2 initial tar parse failed; recovered gzip single TeX, not failed acquisition.',
         'current_named_originals': originals, 'stable_inputs': 15, 'mutable_observations': 1,
         'artifact_cases': 7, 'negative_cases': 5, 'actual_root_unchanged': True,
         'named_originals_unchanged_over_execution': True, 'protected_unrelated_files_unchanged': True,
         'snapshot_helper_sha256': sha(HELPER),
         'limits': 'Current artifact and selected-input observations only; no independent mathematics, contribution, full primary/history reading, OS isolation, historical clearance or priority gate.'})
    print(json.dumps({'payload_files': len(m['files']), 'pinned_source_blobs': len(sources),
                      'primary_versions': len(primaries), 'artifact_cases': 7, 'negative_cases': 5,
                      'whole_root_and_named_originals_unchanged': True}))


if __name__ == '__main__':
    main()
