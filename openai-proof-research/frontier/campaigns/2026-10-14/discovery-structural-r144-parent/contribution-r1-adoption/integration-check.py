#!/usr/bin/env python3
"""Check conditional adoption, dispatch, pending notification and exact Git scope."""
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
    head = baseline['head']
    prefix = git('rev-parse', '--show-prefix').decode().strip()
    assert prefix == 'openai-proof-research/'
    if mode != 'committed':
        assert git('rev-parse', 'HEAD').decode().strip() == head
    taskpath = 'frontier/campaigns/2026-10-14/tasks.json'
    old = json.loads(git('show', head + ':' + prefix + taskpath))
    new = json.loads((PROJECT / taskpath).read_text())
    assert len(old['tasks']) == 481 and len(new['tasks']) == 482
    assert [i for i in range(481) if old['tasks'][i] != new['tasks'][i]] == [478, 480]
    assert {k for k in old if old[k] != new[k]} == {'tasks', 'last_parent_progress', 'current_work_snapshot'}
    assert new['newAccepted'] == 19 and new['remaining'] == 1 and new['target'] == 20
    assert old['latestAcceptance'] == new['latestAcceptance'] == 'R041'
    s0, s = old['current_work_snapshot'], new['current_work_snapshot']
    assert {k for k in s0 if s0[k] != s[k]} == {
        'observed_utc', 'note', 'status_note', 'fresh_discovery_current',
        't3_current_confirmed_running', 't3_dispatch_observations', 'structural_r144_intake', 't185r144_reviews'}
    assert set(s) - set(s0) == {'t185r144_contribution_adoption', 'analytic138_pending_intake'}
    assert s['t3_dispatch_observations'][:-1] == s0['t3_dispatch_observations']
    assert s['t3_last_polled_running'] == []
    for index, name in [(480, 'task-status.json'), (478, 'analytic138-notification-status.json'), (481, 'proof-r1-dispatch.json')]:
        r = json.loads((OUT / name).read_text())['structuredContent']
        assert all(new['tasks'][index][k] == v for k, v in r.items())
    assert new['tasks'][480]['conditional_on_correctness'] is True
    assert new['tasks'][480]['correctness_condition_discharged'] is False
    assert new['tasks'][478]['parent_disposition'] == 'TERMINAL_RESULT_RECEIVED_INTAKE_PENDING'
    assert s['t3_current_confirmed_running'] == [new['tasks'][i]['taskId'] for i in [479, 481]]
    assert s['fresh_discovery_current'] == [new['tasks'][479]['output']]
    assert sha(BASE / new['tasks'][481]['brief']) == new['tasks'][481]['brief_sha256']
    adoption = json.loads((OUT / 'adoption.json').read_text())
    assert adoption['conditional_on_correctness'] and not adoption['correctness_condition_discharged']
    assert sha(OUT.parent / 'contribution-r1-disposition.md') == adoption['parent_record_sha256']
    observed = json.loads((OUT / 'observed-roots.json').read_text())
    assert snap(BASE / 't185r144-contribution-r1') == observed['review_root']
    assert snap(BASE / 'fresh-structural-discovery-r144') == observed['author_root']
    for e in json.loads((OUT / 'replay.json').read_text())['selected_current_originals']:
        assert sha(PROJECT / e['original']) == e['current_sha256']
    assert all(sha(PROJECT / p) == h for p, h in baseline['protected_unrelated_sha256'].items())
    journal = PROJECT / 'frontier/NEW-TEN-2026-10-14.md'
    assert journal.read_bytes().startswith(git('show', head + ':' + prefix + str(journal.relative_to(PROJECT))))
    receipt = json.loads((OUT / 'arithmetic109-h138-isolation.json').read_text())['structuredContent']
    assert receipt['delivery'] == 'steered' and receipt['runId'].endswith(':ordinal:1')
    files = json.loads((OUT / 'staging-allowlist.json').read_text())['files']
    metadata = {'controls/current-originals.json', 'controls/incoming-authentication.json',
                'controls/source-authentication.json', 'controls/integrity/results.json',
                'primary/axioms-receipt.json', 'primary/reuse-receipts.json', 'history/receipts.json'}
    assert {p for p in files if '/private/' in p} == {
        str((BASE / 't185r144-contribution-r1/private' / n).relative_to(PROJECT)) for n in metadata}
    assert not any('/t185r144-proof-r1/' in p or '/h138-' in p or '/fresh-analytic-discovery-r138/' in p for p in files)
    assert len(files) == len(set(files))
    expected = {prefix + p for p in files}
    protected = {prefix + p for p in baseline['protected_unrelated_sha256']}
    if mode == 'prestage':
        assert not git('diff', '--cached', '--name-only')
        assert set(git('diff', '--name-only').decode().splitlines()) == protected | {prefix + taskpath, prefix + 'frontier/NEW-TEN-2026-10-14.md'}
        (OUT / 'integration-validation.json').write_text(json.dumps({
            'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'baseline_head': head,
            'changed_existing_task_indices': [478, 480], 'new_task_indices': [481],
            'prestage_index_empty': True, 'other_tasks_and_unrelated_snapshot_fields_unchanged': True,
            'author_reviewer_selected_originals_and_protected_files_unchanged': True,
            'journal_prefix_preserved': True, 'explicit_allowed_paths': len(files),
            'contribution': 'TECHNICAL_CONDITIONAL_ON_CORRECTNESS', 'correctness': 'UNREVIEWED_REVIEW_DISPATCHED',
            'newAccepted': 19, 'remaining': 1, 'publication': 'STOPPED'}, indent=2) + '\n')
    else:
        if mode == 'staged':
            actual = set(git('diff', '--cached', '--name-only').decode().splitlines())
            obj = ':'
            subprocess.run(['git', 'diff', '--cached', '--check'], cwd=PROJECT, check=True)
        else:
            assert mode == 'committed' and not git('diff', '--cached', '--name-only')
            assert git('rev-parse', 'HEAD^').decode().strip() == head
            actual = set(git('diff-tree', '--no-commit-id', '--name-only', '-r', 'HEAD').decode().splitlines())
            obj = 'HEAD:'
        assert actual == expected, (actual - expected, expected - actual)
        assert all(git('show', obj + prefix + p) == (PROJECT / p).read_bytes() for p in files)
        assert set(git('diff', '--name-only').decode().splitlines()) == protected
    print(json.dumps({'phase': mode, 'files': len(files), 'tasks': 482, 'count': 19,
                      'remaining': 1, 'full_author_reviewer_roots_and_selected_originals_unchanged': True}))


if __name__ == '__main__':
    check(sys.argv[1])
