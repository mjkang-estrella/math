#!/usr/bin/env python3
"""Parent intake byte observations, not mathematical gates."""
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
ROOT = BASE / 'fresh-structural-discovery-r144'
HELPER = BASE / 'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py'
spec = importlib.util.spec_from_file_location('snapshot_helpers', HELPER)
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
sha, snap = helper.sha, helper.snap
ANCHORS = {
    'FINAL.md': '8e82f7d32d54f0cbf82a72bc1d9f251b26fc102e4f1593bfae55c8e2411d1ca5',
    'MANIFEST.json': 'f1b911ece259e2486f017b685f3d4d7f7f71ba34e2b8c44f7bab9d59c6ada908',
    'REPORT.md': '9bb2536ba7739455cc4521569eb827bd6dbc7de51aea6b5637724059917382e9',
}
SCOPE = '98d8a82c64798cfeeb033fe73f708b1cea643159b8b334b4174528269d15882f'
PROOF = '9a40c540418cb946d941e2764d03e5d89e50df126eada2953ac05024199a23f2'
PROTECTED = {
    'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json': '6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9',
    'frontier/iterations/i31-nonconical-no-mcm.md': 'd606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a',
}


def dump(name, value):
    (OUT / name).write_text(json.dumps(value, indent=2) + '\n')


def main():
    assert not subprocess.check_output(['git', 'diff', '--cached', '--name-only'], cwd=PROJECT)
    now = datetime.datetime.now(datetime.timezone.utc).isoformat()
    assert all(sha(PROJECT / p) == h for p, h in PROTECTED.items())
    dump('integration-baseline.json', {'observed_utc': now,
         'head': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=PROJECT, text=True).strip(),
         'initial_index_empty': True, 'task_count': 480, 'task_index': 476,
         'protected_unrelated_sha256': PROTECTED,
         'tasks_sha256': sha(BASE / 'tasks.json'), 'journal_sha256': sha(PROJECT / 'frontier/NEW-TEN-2026-10-14.md')})
    before = snap(ROOT)
    dump('observed-root.json', {'observed_utc': now, 'root': before,
         'limits': 'Current complete actual root after reading; no historical whole-parent/OS certificate.'})
    assert all(sha(ROOT / p) == h for p, h in ANCHORS.items())
    assert sha(ROOT / 'notes/03-frozen-scope.md') == SCOPE
    assert sha(ROOT / 'notes/04-author-proof.md') == PROOF
    assert sha(ROOT / 'tools/verify.py') == '8e9ecb128188556a08e2ab4977e1d017020822fcfe35b0d841607685facfe3fd'
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
    assert manifest['schema'] == 'r144-exact-payload-v1'
    assert {p for p, e in before.items() if e['kind'] == 'file'} == {e['path'] for e in manifest['files']} | set(manifest['outer_files'])
    assert {p for p, e in before.items() if e['kind'] == 'directory'} == set(manifest['directories'])
    for e in manifest['files']:
        assert sha(ROOT / e['path']) == e['sha256'] and (ROOT / e['path']).stat().st_size == e['bytes']
    tree_path = PROJECT / 'sources/preprints-tree.json'
    assert sha(tree_path) == 'eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
    tree = json.loads(tree_path.read_text())
    assert len(tree['tree']) == 13223 and tree['truncated'] is False
    entries = {e['path']: e for e in tree['tree']}
    sources = json.loads((ROOT / 'private/sources/receipts.json').read_text())
    for e in sources:
        b = (ROOT / e['local']).read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
        assert len(b) == e['tree_size'] == entries[e['canonical_path']]['size']
        assert blob == e['git_blob'] == entries[e['canonical_path']]['sha']
        assert sha(ROOT / e['local']) == e['sha256']
        assert e['url'] == 'https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/' + e['canonical_path']
    primary = json.loads((ROOT / 'private/primary/receipts.json').read_text())
    for e in primary:
        p = ROOT / 'private/primary' / (e['name'] + '.pdf')
        assert sha(p) == e['sha256'] and p.stat().st_size == e['bytes']
    originals = []
    for e in json.loads((ROOT / 'private/controls/current-originals.json').read_text())['files']:
        assert sha(ROOT / e['local']) == e['copied_sha256']
        h = sha(PROJECT / e['original'])
        mutable = e['original'] == 'frontier/NEW-TEN-2026-10-14.md'
        if not mutable:
            assert h == e['copied_sha256'], e['original']
        originals.append(dict(e, parent_current_sha256=h, mutable_observation=mutable,
                              parent_matches_retained_copy=h == e['copied_sha256']))
    cases = []
    with tempfile.TemporaryDirectory(prefix='structural144-copy-', dir=OUT) as temp:
        copy = Path(temp) / 'packet'
        shutil.copytree(ROOT, copy)
        args = [str(copy), '--manifest-sha256', ANCHORS['MANIFEST.json'],
                '--final-sha256', ANCHORS['FINAL.md'], '--report-sha256', ANCHORS['REPORT.md']]

        def check(label, expected, custom=None):
            state = snap(copy)
            result = subprocess.run([sys.executable, '-B', str(copy / 'tools/verify.py'), *(custom or args)],
                                    capture_output=True, text=True, timeout=30)
            assert (result.returncode == 0) == expected, (label, result.stdout, result.stderr)
            assert snap(copy) == state
            cases.append(dict(case=label, expected_pass=expected, returncode=result.returncode,
                              fixture_unchanged=True, stdout=result.stdout.strip(), stderr=result.stderr.strip()))

        check('baseline', True)
        p = copy / 'notes/04-author-proof.md'
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
        wrong[4] = '0' * 64
        check('wrong_external_final_anchor', False, wrong)
        check('restored', True)
        assert snap(copy) == before
    assert snap(ROOT) == before
    assert all(sha(PROJECT / e['original']) == e['parent_current_sha256'] for e in originals)
    assert all(sha(PROJECT / p) == h for p, h in PROTECTED.items())
    dump('copied-controls.json', {'cases': cases, 'positive_cases': 2, 'negative_cases': 4,
         'copy_removed': True, 'whole_actual_root_unchanged': True,
         'limits': 'Current complete copied packet byte/membership checks, not mathematical gates.'})
    dump('replay.json', {'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'external_handoff_anchors': ANCHORS, 'frozen_scope_sha256': SCOPE, 'author_proof_sha256': PROOF,
         'payload_files': len(manifest['files']), 'whole_root_files': sum(e['kind'] == 'file' for e in before.values()),
         'pinned_source_blobs': len(sources), 'primary_pdf_versions': len(primary),
         'current_named_originals': originals, 'stable_inputs': 14, 'mutable_observations': 1,
         'artifact_cases': 6, 'negative_cases': 4, 'whole_actual_root_unchanged': True,
         'selected_originals_unchanged_over_execution': True, 'protected_unrelated_files_unchanged': True,
         'snapshot_helper_sha256': sha(HELPER),
         'limits': 'Artifact observations only; no independent correctness/contribution, historical full-parent/OS, semantic whole-primary/history or priority gate.'})
    print(json.dumps({'payload_files': len(manifest['files']), 'source_blobs': len(sources),
                      'primary_versions': len(primary), 'stable_inputs': 14, 'mutable_observations': 1,
                      'artifact_cases': 6, 'negative_cases': 4, 'whole_root_unchanged': True}))


if __name__ == '__main__':
    main()
