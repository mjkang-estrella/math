#!/usr/bin/env python3
"""Check full correctness adoption, historical condition preservation and exact Git scope."""
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
    assert len(old['tasks'])==len(new['tasks'])==485
    assert [i for i in range(485) if old['tasks'][i]!=new['tasks'][i]]==[480,481]
    assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'}
    assert new['newAccepted']==19 and new['remaining']==1 and new['target']==20
    assert old['latestAcceptance']==new['latestAcceptance']=='R041'
    s0,s=old['current_work_snapshot'],new['current_work_snapshot']
    assert {k for k in s0 if s0[k]!=s[k]}=={'observed_utc','note','status_note','structural_r144_intake','t185r144_reviews'}
    assert set(s)-set(s0)=={'t185r144_proof_adoption'} and not set(s0)-set(s)
    assert s['t3_last_polled_running']==[]
    r=json.loads((OUT/'task-status.json').read_text())['structuredContent']
    assert all(new['tasks'][481][k]==v for k,v in r.items())
    assert new['tasks'][481]['correctness']=='PASS' and not new['tasks'][481]['accepted']
    assert new['tasks'][480]['conditional_on_correctness'] is False and new['tasks'][480]['correctness_condition_discharged'] is True
    assert {k for k in old['tasks'][480] if old['tasks'][480][k]!=new['tasks'][480][k]}=={'conditional_on_correctness','correctness_condition_discharged'}
    assert set(new['tasks'][480])-set(old['tasks'][480])=={'correctness_condition_discharged_utc','correctness_discharge_record'}
    assert s['t3_current_confirmed_running']==[new['tasks'][i]['taskId'] for i in [482,483,484]]
    adoption=json.loads((OUT/'adoption.json').read_text())
    assert not adoption['conditional_on_correctness'] and adoption['correctness_condition_discharged']
    assert adoption['correctness']=='PASS_FULL_UNCHANGED_FROZEN_SCOPE' and adoption['contribution']=='TECHNICAL_FULL_UNCHANGED_SCOPE'
    assert not adoption['needed_repairs'] and not adoption['unresolved_correctness_objections'] and not adoption['accepted'] and adoption['count_change']==0
    assert sha(OUT.parent/'proof-r1-disposition.md')==adoption['parent_record_sha256']
    historical=json.loads((OUT.parent/'contribution-r1-adoption/adoption.json').read_text())
    assert historical['conditional_on_correctness'] is True and historical['correctness_condition_discharged'] is False
    observed=json.loads((OUT/'observed-roots.json').read_text())
    assert snap(BASE/'t185r144-proof-r1')==observed['review_root']
    assert snap(BASE/'fresh-structural-discovery-r144')==observed['author_root']
    assert snap(BASE/'t185r144-contribution-r1')==observed['contribution_root']
    assert snap(OUT.parent/'contribution-r1-adoption')==observed['historical_contribution_adoption_root']
    assert sha(OUT.parent/'contribution-r1-disposition.md')==observed['historical_contribution_disposition_sha256']
    for e in json.loads((OUT/'replay.json').read_text())['selected_current_originals']:
        assert sha(PROJECT/e['original'])==e['sha256']
    assert all(sha(PROJECT/p)==h for p,h in baseline['protected_unrelated_sha256'].items())
    journal=PROJECT/'frontier/NEW-TEN-2026-10-14.md'
    assert journal.read_bytes().startswith(git('show',head+':'+prefix+str(journal.relative_to(PROJECT))))
    files = json.loads((OUT / 'staging-allowlist.json').read_text())['files']
    metadata=json.loads((OUT/'staging-allowlist.json').read_text())['private_metadata_only']
    assert {p for p in files if '/private/' in p}=={str((BASE/'t185r144-proof-r1'/n).relative_to(PROJECT)) for n in metadata}
    assert not any('/h138-' in p or '/fresh-arithmetic-discovery-r110/' in p or '/contribution-r1-adoption/' in p for p in files)
    assert len(files) == len(set(files))
    expected = {prefix + p for p in files}
    protected = {prefix + p for p in baseline['protected_unrelated_sha256']}
    if mode == 'prestage':
        assert not git('diff', '--cached', '--name-only')
        assert set(git('diff', '--name-only').decode().splitlines()) == protected | {prefix + taskpath, prefix + 'frontier/NEW-TEN-2026-10-14.md'}
        (OUT / 'integration-validation.json').write_text(json.dumps({
            'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'baseline_head': head,
            'changed_existing_task_indices': [480, 481], 'new_task_indices': [],
            'prestage_index_empty': True, 'other_tasks_and_unrelated_snapshot_fields_unchanged': True,
            'author_reviewer_selected_originals_and_protected_files_unchanged': True,
            'journal_prefix_preserved': True, 'explicit_allowed_paths': len(files),
            'contribution': 'TECHNICAL_UNCHANGED', 'correctness': 'PASS_FULL_UNCHANGED_SCOPE', 'correctness_condition_discharged': True,
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
    print(json.dumps({'phase': mode, 'files': len(files), 'tasks': 485, 'count': 19,
                      'remaining': 1, 'full_author_reviewer_roots_and_selected_originals_unchanged': True}))


if __name__ == '__main__':
    check(sys.argv[1])
