#!/usr/bin/env python3
"""Verify this full-scope contribution adoption and distinct research dispatch."""
import datetime
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

OUT = Path(__file__).resolve().parent
BASE = OUT.parent.parent
PROJECT = BASE.parents[2]
spec = importlib.util.spec_from_file_location('adoption_helpers', OUT / 'replay.py')
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
    assert len(old['tasks']) == 476 and len(new['tasks']) == 477
    assert [i for i in range(476) if old['tasks'][i] != new['tasks'][i]] == [474]
    assert {k for k in old if old[k] != new[k]} == {'tasks', 'last_parent_progress', 'current_work_snapshot'}
    assert new['newAccepted'] == 19 and new['remaining'] == 1 and new['target'] == 20
    assert new['latestAcceptance'] == old['latestAcceptance'] == 'R041'
    s0, s = old['current_work_snapshot'], new['current_work_snapshot']
    assert {k for k in s0 if s0[k] != s[k]} == {
        'observed_utc', 'note', 'status_note', 'fresh_discovery_current',
        't3_current_confirmed_running', 't3_dispatch_observations',
        'structural_r143_intake', 't177c143_reviews'}
    assert set(s) - set(s0) == {'structural144_prospective_isolation'}
    assert s['t3_dispatch_observations'][:-1] == s0['t3_dispatch_observations']
    assert s['t3_last_polled_running'] == []
    assert new['tasks'][474]['status'] == 'completed' and not new['tasks'][474]['accepted']
    assert new['tasks'][476]['status'] == 'running' and new['tasks'][476]['output'] == 'fresh-structural-discovery-r144'
    assert s['t3_current_confirmed_running'] == [new['tasks'][i]['taskId'] for i in [473, 475, 476]]
    assert s['fresh_discovery_current'] == ['fresh-analytic-discovery-r137', 'fresh-structural-discovery-r144']
    assert sha(BASE / new['tasks'][476]['brief']) == new['tasks'][476]['brief_sha256']
    v0, v = s0['t177c143_reviews'], s['t177c143_reviews']
    assert {k for k in v0 if v0[k] != v[k]} == {'contribution_status', 'parent_record'}
    assert set(v) - set(v0) == {'contribution_adoption', 'contribution_manifest_sha256', 'conditional_on_correctness', 'contribution_scope'}
    assert v['proof_status'] == 'R1_RUNNING_AT_ACTUAL_DISPATCH' and v['conditional_on_correctness'] is True
    adoption = json.loads((OUT / 'adoption.json').read_text())
    assert adoption['status'] == 'TECHNICAL_CONDITIONAL_ON_CORRECTNESS_ADOPTED_FULL_UNCHANGED_SCOPE'
    assert not adoption['accepted'] and adoption['count_change'] == 0
    for name in ['proof-structural144-isolation.json', 'analytic137-structural144-isolation.json']:
        r = json.loads((OUT / name).read_text())['structuredContent']
        assert r['delivery'] == 'steered' and r['status'] == 'running'
    journal = PROJECT / 'frontier/NEW-TEN-2026-10-14.md'
    assert journal.read_bytes().startswith(git('show', head + ':' + prefix + 'frontier/NEW-TEN-2026-10-14.md'))
    observed = json.loads((OUT / 'observed-roots.json').read_text())
    assert snap(BASE / 't177c143-contribution-r1') == observed['review_root']
    assert snap(BASE / 'fresh-structural-discovery-r143') == observed['author_root']
    for e in json.loads((OUT / 'replay.json').read_text())['late_named_originals']:
        if not e['mutable_observation']:
            assert sha(PROJECT / e['original']) == e['sha256']
    assert all(sha(PROJECT / p) == h for p, h in baseline['protected_unrelated_sha256'].items())
    parent = OUT.parent
    for name in ['assessment.md', 'intake.json', 'replay.py', 'replay.json', 'review-dispatch.json', 'proof-r1-routing.json', 'proof-r1-brief.txt', 'contribution-r1-brief.txt']:
        rel = str((parent / name).relative_to(PROJECT))
        assert (parent / name).read_bytes() == git('show', head + ':' + prefix + rel)
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
            'changed_existing_task_indices': [474], 'new_task_indices': [476],
            'other_tasks_and_unrelated_snapshot_fields_unchanged': True,
            'journal_prefix_and_sealed_reviewer_author_roots_unchanged': True,
            'scope_proof_review_briefs_and_historical_parent_records_unchanged': True,
            'stable_named_originals_and_protected_unrelated_files_unchanged': True,
            'prospective_isolation_receipts_verified': True,
            'correctness_status_or_body_not_polled': True, 'correctness_condition_discharged': False,
            'explicit_allowed_paths': len(files), 'newAccepted': 19, 'remaining': 1,
            'publication': 'STOPPED', 'contribution': 'TECHNICAL_FULL_SCOPE_CONDITIONAL_ON_CORRECTNESS',
            'new_correctness_acceptance_or_downstream_gate_assigned': False,
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
                      'count': 19, 'remaining': 1, 'sealed_roots_and_stable_inputs_unchanged': True}))


if __name__ == '__main__':
    check(sys.argv[1])
