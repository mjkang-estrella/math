#!/usr/bin/env python3
"""Check H138 correctness-only adoption and exact Git scope."""
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
    assert [i for i in range(485) if old['tasks'][i]!=new['tasks'][i]]==[483]
    assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'}
    assert new['newAccepted']==19 and new['remaining']==1 and new['target']==20
    assert old['latestAcceptance']==new['latestAcceptance']=='R041'
    s0,s=old['current_work_snapshot'],new['current_work_snapshot']
    assert {k for k in s0 if s0[k]!=s[k]}=={'observed_utc','note','status_note','analytic_r138_intake','h138_reviews','t3_current_confirmed_running'}
    assert set(s)-set(s0)=={'h138_proof_adoption'} and not set(s0)-set(s)
    assert s['t3_last_polled_running']==[]
    r=json.loads((OUT/'task-status.json').read_text())['structuredContent']
    assert all(new['tasks'][483][k]==v for k,v in r.items())
    assert new['tasks'][483]['correctness']=='PASS' and not new['tasks'][483]['accepted']
    assert s['t3_current_confirmed_running']==[new['tasks'][i]['taskId'] for i in [482,484]]
    assert s['h138_reviews']['contribution_status']==s0['h138_reviews']['contribution_status']=='RUNNING_AT_ACTUAL_DISPATCH'
    assert s['analytic_r138_intake']['independent_contribution']=='UNREVIEWED_RUNNING'
    adoption=json.loads((OUT/'adoption.json').read_text())
    assert adoption['correctness']=='PASS_FULL_UNCHANGED_FROZEN_SCOPE' and adoption['contribution']=='UNREVIEWED_SEPARATE_REVIEW_DISPATCHED'
    assert not adoption['needed_repairs'] and not adoption['unresolved_correctness_objections'] and not adoption['accepted'] and adoption['count_change']==0
    assert adoption['coverage']==['C'+str(i) for i in range(1,10)] and not adoption['new_local_uniformity_axioms']
    assert sha(OUT.parent/'proof-r1-disposition.md')==adoption['parent_record_sha256']
    observed=json.loads((OUT/'observed-roots.json').read_text())
    assert snap(BASE/'h138-proof-r1')==observed['review_root']
    assert snap(BASE/'fresh-analytic-discovery-r138')==observed['author_root']
    auth=json.loads((OUT/'input-authentication.json').read_text())
    for e in auth['selected_members']:assert sha(Path(e['origin']))==e['sha256']
    for e in auth['additional_original_context_observations']:
        if not e['mutable_journal_not_stability_input']:assert sha(Path(e['origin']))==e['observed_sha256']==e['retained_metadata_sha256']
    assert all(sha(PROJECT/p)==h for p,h in baseline['protected_unrelated_sha256'].items())
    journal=PROJECT/'frontier/NEW-TEN-2026-10-14.md'
    assert journal.read_bytes().startswith(git('show',head+':'+prefix+str(journal.relative_to(PROJECT))))
    files = json.loads((OUT / 'staging-allowlist.json').read_text())['files']
    metadata=json.loads((OUT/'staging-allowlist.json').read_text())['private_metadata_only']
    assert {p for p in files if '/private/' in p}=={str((BASE/'h138-proof-r1'/n).relative_to(PROJECT)) for n in metadata}
    assert not any('/h138-contribution-' in p or '/fresh-arithmetic-discovery-r110/' in p or '/contribution-r1-adoption/' in p for p in files)
    assert len(files) == len(set(files))
    expected = {prefix + p for p in files}
    protected = {prefix + p for p in baseline['protected_unrelated_sha256']}
    if mode == 'prestage':
        assert not git('diff', '--cached', '--name-only')
        assert set(git('diff', '--name-only').decode().splitlines()) == protected | {prefix + taskpath, prefix + 'frontier/NEW-TEN-2026-10-14.md'}
        (OUT / 'integration-validation.json').write_text(json.dumps({
            'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'baseline_head': head,
            'changed_existing_task_indices': [483], 'new_task_indices': [],
            'prestage_index_empty': True, 'other_tasks_and_unrelated_snapshot_fields_unchanged': True,
            'author_reviewer_selected_originals_and_protected_files_unchanged': True,
            'journal_prefix_preserved': True, 'explicit_allowed_paths': len(files),
            'contribution': 'UNREVIEWED_SEPARATE_GATE_PENDING', 'correctness': 'PASS_FULL_UNCHANGED_SCOPE',
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
