#!/usr/bin/env python3
"""Check this archive integration, unchanged inputs and exact staging scope."""
import datetime
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

OUT = Path(__file__).resolve().parent
BASE = OUT.parent
PROJECT = BASE.parents[2]
spec = importlib.util.spec_from_file_location('archive_helpers', OUT / 'replay.py')
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
    assert len(old['tasks'])==515 and len(new['tasks'])==517
    assert [i for i in range(515) if old['tasks'][i]!=new['tasks'][i]]==[512]
    assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'}
    assert new['newAccepted']==19 and new['remaining']==1 and new['target']==20
    assert new['latestAcceptance']==old['latestAcceptance']=='R041'
    s0,s=old['current_work_snapshot'],new['current_work_snapshot']
    assert {k for k in s0 if k in s and s0[k]!=s[k]}=={'observed_utc','note','status_note','t3_current_confirmed_running','t3_dispatch_observations'}
    assert set(s)-set(s0)=={'analytic_r147_intake','t360s147_reviews','t360s147_prospective_isolation'}
    assert set(s0)-set(s)=={'analytic_r147_pending_intake'}
    assert s['t3_dispatch_observations'][:-2]==s0['t3_dispatch_observations'] and s['t3_last_polled_running']==[]
    for i,name in [(512,'task-status.json'),(515,'proof-r1-dispatch.json'),(516,'contribution-r1-dispatch.json')]:
        d=json.loads((OUT/name).read_text())['structuredContent'];assert all(new['tasks'][i][k]==v for k,v in d.items())
    assert new['tasks'][512]['parent_disposition']=='FULL_AUTHOR_PROOF_NOMINEE' and new['tasks'][512]['scope_frozen'] and new['tasks'][512]['nominee']=='T360S147'
    assert 'parent_intake_pending' not in new['tasks'][512]
    assert new['tasks'][512]['correctness']==new['tasks'][512]['contribution']=='UNREVIEWED' and not new['tasks'][512]['accepted'] and new['tasks'][512]['count_change']==0
    assert s['t3_current_confirmed_running']==[new['tasks'][i]['taskId'] for i in [514,515,516]]
    assert s['fresh_discovery_current']==s0['fresh_discovery_current']==[new['tasks'][514]['output']]
    assert not (BASE/'expanded-target-2026-10-17/fresh-arithmetic-r119-brief.txt').exists() and not (BASE/'fresh-arithmetic-discovery-r119').exists()
    assert not (BASE/'expanded-target-2026-10-17/fresh-analytic-r148-brief.txt').exists()
    original=(BASE/old['tasks'][512]['brief']).read_text()
    for i,role in [(515,'proof'),(516,'contribution')]:
        task=new['tasks'][i];text=(BASE/task['brief']).read_text()
        assert task['providerInstanceId']=='codex' and task['model']=='gpt-6.1-sol'
        assert {e['id']:e['value'] for e in task['options']}=={'reasoningEffort':'high','serviceTier':'default'}
        assert task['review_role']==role and task['round']==1 and sha(BASE/task['brief'])==task['brief_sha256']
        assert text.split('--- COMPLETE ORIGINAL RESEARCH BRIEF (HISTORICAL CONTEXT ONLY) ---\n')[1]==original
        assert (BASE/'fresh-analytic-discovery-r147/STATEMENT.md').read_text() in text and (BASE/'fresh-analytic-discovery-r147/CONTRIBUTION.md').read_text() in text
        assert all(x in text for x in ['*structural*r153*','*arithmetic*r119*','*analytic*r148*'])
        assert ('*t360s147*contribution*' if role=='proof' else '*t360s147*proof*') in text
    pre=json.loads((OUT/'structural153-before-reviews-status.json').read_text())['structuredContent'];steer=json.loads((OUT/'structural153-isolation-steer.json').read_text())['structuredContent'];receipt=json.loads((OUT/'prospective-isolation.json').read_text())
    assert pre['taskId']==old['tasks'][514]['taskId'] and pre['status']=='running' and not pre['hasPendingChildRuns']
    assert steer['delivery']=='steered' and steer['threadId']==pre['childThreadId'] and steer['runId']==pre['childRunId']
    assert not steer.get('taskId') or steer['taskId']==pre['taskId']
    assert receipt['before_t360s147_review_briefs_and_roots'] and '*t360s147*' in receipt['message']
    journal = PROJECT / 'frontier/NEW-TEN-2026-10-14.md'
    assert journal.read_bytes().startswith(git('show', head + ':' + prefix + 'frontier/NEW-TEN-2026-10-14.md'))
    assert snap(BASE / 'fresh-analytic-discovery-r147') == json.loads((OUT / 'observed-root.json').read_text())['root']
    for e in json.loads((OUT / 'replay.json').read_text())['stable_named_originals']:
        assert sha(PROJECT / e['path']) == e['sha256']
    assert sha(OUT / 'assessment.md') == json.loads((OUT / 'intake.json').read_text())['assessment_sha256']
    assert all(sha(PROJECT / p) == h for p, h in baseline['protected_unrelated_sha256'].items())
    files = json.loads((OUT / 'staging-allowlist.json').read_text())['files']
    assert len(files) == len(set(files))
    private_metadata=json.loads((OUT/'staging-allowlist.json').read_text())['private_metadata_only']
    assert {p for p in files if '/private/' in p}=={str((BASE/'fresh-analytic-discovery-r147'/n).relative_to(PROJECT)) for n in private_metadata}
    assert not any('/fresh-arithmetic-discovery-r119/' in p or '/fresh-structural-discovery-r153/' in p or '/t360s147-proof-r1/' in p or '/t360s147-contribution-r1/' in p for p in files)
    assert private_metadata==[]
    assert not any('/private/' in p for p in files)
    assert all(p.endswith('.py') for p in files if '/scratch/' in p)
    expected = {prefix + p for p in files}
    protected = {prefix + p for p in baseline['protected_unrelated_sha256']}
    if mode == 'prestage':
        assert not git('diff', '--cached', '--name-only')
        assert set(git('diff', '--name-only').decode().splitlines()) == protected | {
            prefix + taskpath, prefix + 'frontier/NEW-TEN-2026-10-14.md'}
        (OUT / 'integration-validation.json').write_text(json.dumps({
            'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'baseline_head': head, 'prestage_index_empty': True,
            'changed_existing_task_indices': [512], 'new_task_indices': [515,516],
            'other_tasks_and_unrelated_snapshot_fields_unchanged': True,
            'journal_prefix_and_actual_artifact_root_unchanged': True,
            'stable_named_originals_and_protected_unrelated_files_unchanged': True,
            'two_actual_fresh_review_dispatches': True,
            'prospective_original_turn_isolation_steer_verified': True,
            'complete_original_briefs_and_frozen_statement_preserved': True,
            'explicit_allowed_paths': len(files), 'newAccepted': 19, 'remaining': 1,
            'publication': 'STOPPED', 'mathematical_or_contribution_gate_assigned': False,
        }, indent=2) + '\n')
    else:
        if mode == 'staged':
            actual = set(git('diff', '--cached', '--name-only').decode().splitlines())
            obj = ':'
            subprocess.run(['git', 'diff', '--cached', '--check'], cwd=PROJECT, check=True)
        else:
            assert mode == 'committed'
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
