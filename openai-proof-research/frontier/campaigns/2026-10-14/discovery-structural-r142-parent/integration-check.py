#!/usr/bin/env python3
"""Check this integration's explicit Git paths and unchanged original bytes."""
import datetime
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

OUT = Path(__file__).resolve().parent
BASE = OUT.parent
PROJECT = BASE.parents[2]
spec = importlib.util.spec_from_file_location('snapshot_helpers', BASE / 'discovery-analytic-r135-parent/contribution-r1-adoption/replay.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
sha, snap = helpers.sha, helpers.snap


def git(*args):
    return subprocess.check_output(['git', *args], cwd=PROJECT)


def check(mode):
    baseline = json.loads((OUT / 'integration-baseline.json').read_text())
    head = baseline['head']
    prefix = git('rev-parse', '--show-prefix').decode().strip()
    assert prefix == 'openai-proof-research/'
    if mode != 'committed':
        assert git('rev-parse', 'HEAD').decode().strip() == head
    old = json.loads(git('show', head + ':' + prefix + str((BASE / 'tasks.json').relative_to(PROJECT))))
    new = json.loads((BASE / 'tasks.json').read_text())
    assert len(old['tasks']) == 470 and len(new['tasks']) == 473
    assert [i for i in range(470) if old['tasks'][i] != new['tasks'][i]] == [467, 468, 469]
    assert {k for k in old if old[k] != new[k]} == {'tasks', 'last_parent_progress', 'current_work_snapshot'}
    assert new['newAccepted'] == 19 and new['remaining'] == 1 and new['target'] == 20
    assert new['latestAcceptance'] == old['latestAcceptance'] == 'R041'
    s0, s = old['current_work_snapshot'], new['current_work_snapshot']
    changed = {'observed_utc', 'note', 'status_note', 'fresh_discovery_current',
               't3_current_confirmed_running', 't3_dispatch_observations',
               'analytic_r135_intake', 't373e135_reviews'}
    assert {k for k in s0 if s0[k] != s[k]} == changed
    assert set(s) - set(s0) == {'structural_r142_archive', 't373e135_structural143_isolation', 'research_mutual_isolation_after_t373'}
    assert s['t3_dispatch_observations'][:-3] == s0['t3_dispatch_observations']
    assert s['t3_last_polled_running'] == []
    assert s['t3_current_confirmed_running'] == [r['taskId'] for r in new['tasks'][-3:]]
    assert all(new['tasks'][i]['status'] == 'completed' for i in [467, 468, 469])
    assert all(r['status'] == 'running' and r['count_change'] == 0 and not r['accepted'] for r in new['tasks'][-3:])
    for r in new['tasks'][-3:]:
        assert sha(BASE / r['brief']) == r['brief_sha256']
    journal = PROJECT / 'frontier/NEW-TEN-2026-10-14.md'
    assert journal.read_bytes().startswith(git('show', head + ':' + prefix + 'frontier/NEW-TEN-2026-10-14.md'))
    assert all(sha(PROJECT / p) == h for p, h in baseline['protected_unrelated_sha256'].items())
    observed = json.loads((OUT / 'observed-root.json').read_text())['root']
    assert snap(BASE / 'fresh-structural-discovery-r142') == observed
    for e in json.loads((BASE / 'fresh-structural-discovery-r142/packet/private/current-originals.json').read_text())['files']:
        assert sha(PROJECT / e['path']) == e['sha256']
    parent = BASE / 'discovery-analytic-r135-parent'
    for role in ['contribution', 'proof']:
        p = parent / (role + '-r1-adoption')
        observed = json.loads((p / 'observed-roots.json').read_text())
        assert snap(BASE / ('t373e135-' + role + '-r1')) == observed['review_root']
        assert snap(BASE / 'fresh-analytic-discovery-r135') == observed['author_root']
        replay = json.loads((p / 'replay.json').read_text())
        rows = replay.get('selected_project_inputs', replay.get('late_selected_originals'))
        for e in rows:
            if not e['mutable_observation']:
                assert sha(PROJECT / e['path']) == e.get('review_snapshot_sha256', e.get('sha256'))
    allow = json.loads((OUT / 'staging-allowlist.json').read_text())['files']
    expected = {prefix + p for p in allow}
    protected = {prefix + p for p in baseline['protected_unrelated_sha256']}
    if mode == 'prestage':
        assert not git('diff', '--cached', '--name-only')
        assert set(git('diff', '--name-only').decode().splitlines()) == protected | {
            prefix + 'frontier/NEW-TEN-2026-10-14.md', prefix + str((BASE / 'tasks.json').relative_to(PROJECT))}
        result = {'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  'baseline_head': head, 'prestage_index_empty': True,
                  'changed_existing_task_indices': [467, 468, 469], 'new_task_indices': [470, 471, 472],
                  'all_other_tasks_and_untouched_snapshot_fields_unchanged': True,
                  'historical_journal_prefix_unchanged': True, 'sealed_review_and_author_roots_unchanged': True,
                  'named_stable_originals_and_protected_unrelated_files_unchanged': True,
                  'allowed_paths': len(allow), 'newAccepted': 19, 'remaining': 1,
                  'publication': 'STOPPED', 'artifact_tests_are_not_mathematical_gates': True}
        (OUT / 'integration-validation.json').write_text(json.dumps(result, indent=2) + '\n')
    else:
        if mode == 'staged':
            actual = set(git('diff', '--cached', '--name-only').decode().splitlines())
            object_prefix = ':'
            subprocess.run(['git', 'diff', '--cached', '--check'], cwd=PROJECT, check=True)
        else:
            assert not git('diff', '--cached', '--name-only')
            assert git('rev-parse', 'HEAD^').decode().strip() == head
            actual = set(git('diff-tree', '--no-commit-id', '--name-only', '-r', 'HEAD').decode().splitlines())
            object_prefix = 'HEAD:'
        assert actual == expected, (sorted(actual - expected), sorted(expected - actual))
        for p in allow:
            assert git('show', object_prefix + prefix + p) == (PROJECT / p).read_bytes(), p
        assert set(git('diff', '--name-only').decode().splitlines()) == protected
    print(json.dumps({'phase': mode, 'allowlist_files': len(allow), 'tasks': len(new['tasks']),
                      'sealed_roots_and_stable_originals_unchanged': True,
                      'count': 19, 'remaining': 1, 'publication': 'STOPPED'}))


if __name__ == '__main__':
    check(sys.argv[1])
