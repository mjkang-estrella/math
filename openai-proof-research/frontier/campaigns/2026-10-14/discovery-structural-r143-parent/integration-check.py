#!/usr/bin/env python3
"""Check the exact T177C143 intake and review-dispatch integration."""
import datetime
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

OUT = Path(__file__).resolve().parent
BASE = OUT.parent
PROJECT = BASE.parents[2]
spec = importlib.util.spec_from_file_location('intake_helpers', OUT / 'replay.py')
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
sha, snap = helper.sha, helper.snap


def git(*args):
    return subprocess.check_output(['git', *args], cwd=PROJECT)


def check(mode):
    baseline = json.loads((OUT / 'integration-baseline.json').read_text())
    prefix = git('rev-parse', '--show-prefix').decode().strip()
    assert prefix == 'openai-proof-research/'
    head = baseline['head']
    if mode != 'committed':
        assert git('rev-parse', 'HEAD').decode().strip() == head
    taskpath = str((BASE / 'tasks.json').relative_to(PROJECT))
    old = json.loads(git('show', head + ':' + prefix + taskpath))
    new = json.loads((BASE / 'tasks.json').read_text())
    assert len(old['tasks']) == 474 and len(new['tasks']) == 475
    assert [i for i in range(474) if old['tasks'][i] != new['tasks'][i]] == [470]
    assert {k for k in old if old[k] != new[k]} == {'tasks', 'last_parent_progress', 'current_work_snapshot'}
    assert new['newAccepted'] == 19 and new['remaining'] == 1 and new['target'] == 20
    assert new['latestAcceptance'] == old['latestAcceptance'] == 'R041'
    s0, s = old['current_work_snapshot'], new['current_work_snapshot']
    assert {k for k in s0 if s0[k] != s[k]} == {
        'observed_utc', 'note', 'status_note', 'fresh_discovery_current',
        't3_current_confirmed_running', 't3_dispatch_observations'}
    assert set(s) - set(s0) == {'structural_r143_intake', 't177c143_reviews', 't177c143_prospective_isolation'}
    assert s['t3_dispatch_observations'][:-1] == s0['t3_dispatch_observations']
    assert s['t3_last_polled_running'] == []
    assert new['tasks'][470]['status'] == 'completed' and new['tasks'][470]['candidate'] == 'T177C143'
    assert new['tasks'][474]['status'] == 'running' and new['tasks'][474]['model'] == 'gpt-6.1-sol'
    assert s['t3_current_confirmed_running'] == [new['tasks'][i]['taskId'] for i in [472, 473, 474]]
    assert sha(BASE / new['tasks'][474]['brief']) == new['tasks'][474]['brief_sha256'] == '9744259ca9944ebc9aadab2712d5fad363ff7e93153233cf91260f3adad96658'
    assert sha(OUT / 'proof-r1-brief.txt') == s['t177c143_reviews']['proof_brief_sha256'] == 'd2ed3ab0fb02bb50a8b9c963f918becc4380220b98023759cab759ee0c75b0d1'
    assert s['t177c143_reviews']['proof'] is None
    assert s['t177c143_reviews']['proof_status'] == 'PREPARED_NOT_DISPATCHED_CAPACITY'
    for n in ['analytic137-review-isolation.json', 'arithmetic107-review-isolation.json']:
        receipt = json.loads((OUT / n).read_text())['structuredContent']
        assert receipt['delivery'] == 'steered' and receipt['status'] == 'running'
    journal = PROJECT / 'frontier/NEW-TEN-2026-10-14.md'
    assert journal.read_bytes().startswith(git('show', head + ':' + prefix + 'frontier/NEW-TEN-2026-10-14.md'))
    root = BASE / 'fresh-structural-discovery-r143'
    assert snap(root) == json.loads((OUT / 'observed-root.json').read_text())['root']
    assert sha(root / 'packet/public/frozen-scope.md') == 'cc916afef1373c1b3c0abdee271a4c2769f887f664e8c9b2b16b1b381c0de221'
    assert sha(root / 'packet/public/author-proof.md') == '10e6dda7b9824e629922e3cf6f42de1b2bc194803ace97eb774c7dd85858792a'
    for e in json.loads((OUT / 'replay.json').read_text())['late_named_originals']:
        if not e['mutable_observation']:
            assert sha(PROJECT / e['original']) == e['sha256']
    assert all(sha(PROJECT / p) == h for p, h in baseline['protected_unrelated_sha256'].items())
    files = json.loads((OUT / 'staging-allowlist.json').read_text())['files']
    expected = {prefix + p for p in files}
    protected = {prefix + p for p in baseline['protected_unrelated_sha256']}
    if mode == 'prestage':
        assert not git('diff', '--cached', '--name-only')
        assert set(git('diff', '--name-only').decode().splitlines()) == protected | {
            prefix + taskpath, prefix + 'frontier/NEW-TEN-2026-10-14.md'}
        (OUT / 'integration-validation.json').write_text(json.dumps({
            'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'baseline_head': head, 'prestage_index_empty': True,
            'changed_existing_task_indices': [470], 'new_task_indices': [474],
            'other_tasks_and_unrelated_snapshot_fields_unchanged': True,
            'journal_prefix_and_actual_artifact_root_unchanged': True,
            'frozen_scope_proof_and_both_review_briefs_unchanged': True,
            'stable_named_originals_and_protected_unrelated_files_unchanged': True,
            'prospective_isolation_receipts_verified': True, 'correctness_dispatched': False,
            'explicit_allowed_paths': len(files), 'newAccepted': 19, 'remaining': 1,
            'publication': 'STOPPED', 'independent_mathematical_or_contribution_gate_assigned': False,
        }, indent=2) + '\n')
    else:
        if mode == 'staged':
            actual = set(git('diff', '--cached', '--name-only').decode().splitlines())
            obj = ':'
            subprocess.run(['git', 'diff', '--cached', '--check'], cwd=PROJECT, check=True)
        else:
            assert not git('diff', '--cached', '--name-only')
            assert git('rev-parse', 'HEAD^').decode().strip() == head
            actual = set(git('diff-tree', '--no-commit-id', '--name-only', '-r', 'HEAD').decode().splitlines())
            obj = 'HEAD:'
        assert actual == expected, (actual - expected, expected - actual)
        assert all(git('show', obj + prefix + p) == (PROJECT / p).read_bytes() for p in files)
        assert set(git('diff', '--name-only').decode().splitlines()) == protected
    print(json.dumps({'phase': mode, 'files': len(files), 'tasks': len(new['tasks']),
                      'count': 19, 'remaining': 1, 'sealed_root_and_stable_inputs_unchanged': True}))


if __name__ == '__main__':
    check(sys.argv[1])
