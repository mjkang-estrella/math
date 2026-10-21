#!/usr/bin/env python3
"""Check H138 full contribution adoption, condition discharge and new research dispatches."""
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
    assert len(old['tasks'])==485 and len(new['tasks'])==487
    assert [i for i in range(485) if old['tasks'][i]!=new['tasks'][i]]==[482]
    assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'}
    assert new['newAccepted']==19 and new['remaining']==1 and new['target']==20
    assert old['latestAcceptance']==new['latestAcceptance']=='R041'
    s0,s=old['current_work_snapshot'],new['current_work_snapshot']
    assert {k for k in s0 if s0[k]!=s[k]}=={'observed_utc','note','status_note','analytic_r138_intake','h138_reviews','t3_current_confirmed_running','fresh_discovery_current','t3_dispatch_observations'}
    assert set(s)-set(s0)=={'h138_contribution_adoption','fresh139145_prospective_isolation'} and not set(s0)-set(s)
    assert s['t3_last_polled_running']==[]
    r=json.loads((OUT/'task-status.json').read_text())['structuredContent']
    assert all(new['tasks'][482][k]==v for k,v in r.items())
    assert new['tasks'][482]['contribution']=='TECHNICAL' and not new['tasks'][482]['accepted']
    assert not new['tasks'][482]['conditional_on_correctness'] and new['tasks'][482]['correctness_condition_discharged']
    assert s['t3_current_confirmed_running']==[new['tasks'][i]['taskId'] for i in [484,485,486]]
    assert s['fresh_discovery_current']==[new['tasks'][i]['output'] for i in [484,485,486]]
    assert s['h138_reviews']['proof_status']==s0['h138_reviews']['proof_status']=='PASS_FULL_UNCHANGED_SCOPE_ADOPTED'
    assert s['analytic_r138_intake']['independent_correctness']=='PASS_FULL_UNCHANGED_SCOPE_ADOPTED'
    assert s['t3_dispatch_observations'][:-2]==s0['t3_dispatch_observations']
    adoption=json.loads((OUT/'adoption.json').read_text())
    assert adoption['contribution']=='TECHNICAL_FULL_UNCHANGED_FROZEN_SCOPE'
    assert adoption['reviewer_correctness']=='UNREVIEWED' and adoption['reviewer_conditional_on_correctness']
    assert not adoption['conditional_on_correctness'] and adoption['correctness_condition_discharged']
    assert not adoption['accepted'] and adoption['count_change']==0
    assert sha(OUT.parent/'contribution-r1-disposition.md')==adoption['parent_record_sha256']
    assert sha(BASE/adoption['correctness_adoption'])==adoption['correctness_adoption_sha256']
    observed=json.loads((OUT/'observed-roots.json').read_text())
    assert snap(BASE/'h138-contribution-r1')==observed['review_root']
    assert snap(BASE/'fresh-analytic-discovery-r138')==observed['author_root']
    historical=json.loads((OUT/'historical-proof-observation.json').read_text())
    assert snap(BASE/'h138-proof-r1')==historical['review_root']
    assert snap(OUT.parent/'proof-r1-adoption')==historical['adoption_root']
    assert sha(OUT.parent/'proof-r1-disposition.md')==historical['proof_disposition_sha256']
    for e in json.loads((OUT/'input-authentication.json').read_text())['selected_members']:
        assert sha(PROJECT/e['original'])==e['sha256']
    marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
    standing=(BASE/'expanded-target-2026-10-17/fresh-arithmetic-r110-brief.txt').read_text().split(marker)[1]
    for i,name in [(485,'structural145'),(486,'analytic139')]:
        d=json.loads((OUT/(name+'-dispatch.json')).read_text())['structuredContent']
        assert all(new['tasks'][i][k]==v for k,v in d.items())
        brief=BASE/new['tasks'][i]['brief'];text=brief.read_text()
        assert sha(brief)==new['tasks'][i]['brief_sha256'] and text.split(marker)[1]==standing
        assert '*arithmetic*r110*' in text and '*analytic*r139*' in text and '*structural*r145*' in text
        assert new['tasks'][i]['target']=={'providerInstanceId':'codex','model':'gpt-6-astra','options':{'reasoningEffort':'high','serviceTier':'default'}}
    receipt=json.loads((OUT/'arithmetic110-future-isolation.json').read_text())['structuredContent']
    assert receipt['delivery']=='steered' and receipt['status']=='running' and receipt['runId'].endswith(':ordinal:1')
    prospect=json.loads((OUT/'prospective-isolation.json').read_text())
    assert all(e['root_absent_before_brief_creation'] and e['mutual_exclusions_in_initial_brief'] for e in prospect['new_roles'].values())
    assert all(sha(PROJECT/p)==h for p,h in baseline['protected_unrelated_sha256'].items())
    journal=PROJECT/'frontier/NEW-TEN-2026-10-14.md'
    assert journal.read_bytes().startswith(git('show',head+':'+prefix+str(journal.relative_to(PROJECT))))
    files = json.loads((OUT / 'staging-allowlist.json').read_text())['files']
    assert not any('/private/' in p or '/h138-proof-r1/' in p or '/fresh-arithmetic-discovery-r110/' in p or '/proof-r1-adoption/' in p for p in files)
    assert len(files) == len(set(files))
    expected = {prefix + p for p in files}
    protected = {prefix + p for p in baseline['protected_unrelated_sha256']}
    if mode == 'prestage':
        assert not git('diff', '--cached', '--name-only')
        assert set(git('diff', '--name-only').decode().splitlines()) == protected | {prefix + taskpath, prefix + 'frontier/NEW-TEN-2026-10-14.md'}
        (OUT / 'integration-validation.json').write_text(json.dumps({
            'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'baseline_head': head,
            'changed_existing_task_indices': [482], 'new_task_indices': [485,486],
            'prestage_index_empty': True, 'other_tasks_and_unrelated_snapshot_fields_unchanged': True,
            'author_reviewer_selected_originals_and_protected_files_unchanged': True,
            'journal_prefix_preserved': True, 'explicit_allowed_paths': len(files),
            'contribution': 'TECHNICAL_FULL_UNCHANGED_SCOPE', 'correctness': 'PASS_FULL_UNCHANGED_SCOPE_ALREADY_ADOPTED', 'correctness_condition_discharged': True,
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
    print(json.dumps({'phase': mode, 'files': len(files), 'tasks': 487, 'count': 19,
                      'remaining': 1, 'full_author_reviewer_roots_and_selected_originals_unchanged': True}))


if __name__ == '__main__':
    check(sys.argv[1])
