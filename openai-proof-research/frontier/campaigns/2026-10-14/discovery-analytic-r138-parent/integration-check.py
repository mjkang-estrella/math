#!/usr/bin/env python3
"""Check H author intake, two actual review dispatches and exact Git scope."""
import datetime
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

OUT = Path(__file__).resolve().parent
BASE = OUT.parent
PROJECT = BASE.parents[2]
spec = importlib.util.spec_from_file_location('intake', OUT / 'replay.py')
helper = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helper)
sha, snap = helper.sha, helper.snap


def git(*args):
    return subprocess.check_output(['git', *args], cwd=PROJECT)


def check(mode):
    b = json.loads((OUT / 'integration-baseline.json').read_text())
    h = b['head']
    prefix = git('rev-parse', '--show-prefix').decode().strip()
    assert prefix == 'openai-proof-research/'
    if mode != 'committed':
        assert git('rev-parse', 'HEAD').decode().strip() == h
    tp = 'frontier/campaigns/2026-10-14/tasks.json'
    old = json.loads(git('show', h + ':' + prefix + tp))
    new = json.loads((PROJECT / tp).read_text())
    assert len(old['tasks']) == 482 and len(new['tasks']) == 484
    assert [i for i in range(482) if old['tasks'][i] != new['tasks'][i]] == [478, 479]
    assert {k for k in old if old[k] != new[k]} == {'tasks', 'last_parent_progress', 'current_work_snapshot'}
    assert new['newAccepted'] == 19 and new['remaining'] == 1 and new['target'] == 20
    assert new['latestAcceptance'] == old['latestAcceptance'] == 'R041'
    s0, s = old['current_work_snapshot'], new['current_work_snapshot']
    assert {k for k in s0.keys() & s.keys() if s0[k] != s[k]} == {
        'observed_utc', 'note', 'status_note', 'fresh_discovery_current',
        't3_current_confirmed_running', 't3_dispatch_observations', 't185r144_reviews'}
    assert set(s) - set(s0) == {'analytic_r138_intake', 'h138_reviews', 'arithmetic109_pending_intake', 'h138_prospective_isolation'}
    assert set(s0) - set(s) == {'analytic138_pending_intake'}
    assert s['t3_dispatch_observations'][:-2] == s0['t3_dispatch_observations']
    assert s['t3_last_polled_running'] == [] and s['fresh_discovery_current'] == []
    assert s['t3_current_confirmed_running'] == [new['tasks'][i]['taskId'] for i in [482, 483]]
    assert s['t185r144_reviews']['proof_status'] == 'COMPLETION_NOTIFICATION_RECEIVED_STATUS_READ_PENDING'
    assert {k: v for k, v in s['t185r144_reviews'].items() if k != 'proof_status'} == {
        k: v for k, v in s0['t185r144_reviews'].items() if k != 'proof_status'}
    for i, name in [(478, 'task-status.json'), (479, 'arithmetic109-notification-status.json'),
                    (482, 'contribution-r1-dispatch.json'), (483, 'proof-r1-dispatch.json')]:
        r = json.loads((OUT / name).read_text())['structuredContent']
        assert all(new['tasks'][i][k] == v for k, v in r.items())
    assert new['tasks'][478]['nominee'] == 'H138' and new['tasks'][478]['scope_unchanged']
    for i in [482, 483]:
        assert sha(BASE / new['tasks'][i]['brief']) == new['tasks'][i]['brief_sha256']
        assert new['tasks'][i]['frozen_scope_sha256'] == helper.SCOPE
        assert new['tasks'][i]['author_proof_sha256'] == helper.PROOF
    assert snap(BASE / 'fresh-analytic-discovery-r138') == json.loads((OUT / 'observed-root.json').read_text())['root']
    for e in json.loads((OUT / 'replay.json').read_text())['current_named_originals']:
        if not e['mutable_observation']:
            assert sha(PROJECT / e['canonical_project_path']) == e['parent_current_sha256'] == e['sha256']
    assert sha(OUT / 'assessment.md') == json.loads((OUT / 'intake.json').read_text())['assessment_sha256']
    assert all(sha(PROJECT / p) == v for p, v in b['protected_unrelated_sha256'].items())
    jp = 'frontier/NEW-TEN-2026-10-14.md'
    assert (PROJECT / jp).read_bytes().startswith(git('show', h + ':' + prefix + jp))
    files = json.loads((OUT / 'staging-allowlist.json').read_text())['files']
    assert len(files) == len(set(files)) and not any('/private/' in p or '/h138-' in p for p in files)
    expected = {prefix + p for p in files}
    protected = {prefix + p for p in b['protected_unrelated_sha256']}
    if mode == 'prestage':
        assert not git('diff', '--cached', '--name-only')
        assert set(git('diff', '--name-only').decode().splitlines()) == protected | {prefix + tp, prefix + jp}
        (OUT / 'integration-validation.json').write_text(json.dumps({
            'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'baseline_head': h,
            'changed_existing_task_indices': [478, 479], 'new_task_indices': [482, 483],
            'unrelated_tasks_and_snapshot_fields_preserved': True, 'sealed_root_and_stable_inputs_preserved': True,
            'journal_prefix_preserved': True, 'prestage_index_empty': True, 'explicit_allowed_paths': len(files),
            'newAccepted': 19, 'remaining': 1, 'publication': 'STOPPED', 'mathematical_gates_assigned': False}, indent=2) + '\n')
    else:
        if mode == 'staged':
            actual = set(git('diff', '--cached', '--name-only').decode().splitlines())
            obj = ':'
            subprocess.run(['git', 'diff', '--cached', '--check'], cwd=PROJECT, check=True)
        else:
            assert mode == 'committed' and not git('diff', '--cached', '--name-only')
            assert git('rev-parse', 'HEAD^').decode().strip() == h
            actual = set(git('diff-tree', '--no-commit-id', '--name-only', '-r', 'HEAD').decode().splitlines())
            obj = 'HEAD:'
        assert actual == expected, (actual - expected, expected - actual)
        assert all(git('show', obj + prefix + p) == (PROJECT / p).read_bytes() for p in files)
        assert set(git('diff', '--name-only').decode().splitlines()) == protected
    print(json.dumps({'phase': mode, 'files': len(files), 'tasks': 484, 'count': 19, 'remaining': 1,
                      'sealed_author_root_and_stable_inputs_unchanged': True}))


if __name__ == '__main__':
    check(sys.argv[1])
