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
    assert len(old['tasks'])==503 and len(new['tasks'])==504
    assert [i for i in range(503) if old['tasks'][i]!=new['tasks'][i]]==[499]
    assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'}
    assert new['newAccepted']==19 and new['remaining']==1 and new['target']==20
    assert new['latestAcceptance']==old['latestAcceptance']=='R041'
    s0,s=old['current_work_snapshot'],new['current_work_snapshot']
    assert {k for k in s0 if k in s and s0[k]!=s[k]}=={'observed_utc','note','status_note','fresh_discovery_current','t3_current_confirmed_running','t3_dispatch_observations'}
    assert set(s)-set(s0)=={'arithmetic_r113_archive','arithmetic114_prospective_isolation'} and set(s0)-set(s)=={'arithmetic113_terminal_pending_archive'}
    assert s['t3_dispatch_observations'][:-1]==s0['t3_dispatch_observations'] and s['t3_last_polled_running']==[]
    for i,name in [(499,'task-status.json'),(503,'r114-dispatch.json')]:
        d=json.loads((OUT/name).read_text())['structuredContent'];assert all(new['tasks'][i][k]==v for k,v in d.items())
    assert new['tasks'][499]['parent_disposition']=='PREFREEZE_NO_NOMINEE' and not new['tasks'][499]['scope_frozen'] and new['tasks'][499]['nominee'] is None
    assert 'arithmetic113_terminal_pending_archive' not in s
    assert {x['id']:x['value'] for x in new['tasks'][503]['options']}=={'reasoningEffort':'high','serviceTier':'default'}
    assert new['tasks'][503]['providerInstanceId']=='codex' and new['tasks'][503]['model']=='gpt-6-astra'
    assert s['t3_current_confirmed_running']==[new['tasks'][i]['taskId'] for i in [501,502,503]]
    assert s['fresh_discovery_current']==[new['tasks'][i]['output'] for i in [501,502,503]]
    assert sha(BASE/new['tasks'][503]['brief'])==new['tasks'][503]['brief_sha256']
    marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
    text=(BASE/new['tasks'][503]['brief']).read_text()
    assert text.split(marker)[1]==(BASE/old['tasks'][495]['brief']).read_text().split(marker)[1]
    assert all(x in text for x in ['*structural*r149*','*analytic*r144*','*structural*r150*','*analytic*r145*'])
    receipt=json.loads((OUT/'prospective-isolation.json').read_text())
    assert receipt['before_new114_brief_or_root'] and len(receipt['both_active_initial_briefs'])==2
    for e,i in zip(receipt['both_active_initial_briefs'],[501,502]):
        assert e['brief']==old['tasks'][i]['brief'] and sha(BASE/e['brief'])==e['sha256']==old['tasks'][i]['brief_sha256']
        assert '*arithmetic*r114*' in (BASE/e['brief']).read_text()
    journal = PROJECT / 'frontier/NEW-TEN-2026-10-14.md'
    assert journal.read_bytes().startswith(git('show', head + ':' + prefix + 'frontier/NEW-TEN-2026-10-14.md'))
    assert snap(BASE / 'fresh-arithmetic-discovery-r113') == json.loads((OUT / 'observed-root.json').read_text())['root']
    for e in json.loads((OUT / 'replay.json').read_text())['stable_named_originals']:
        assert sha(PROJECT / e['path']) == e['sha256']
    assert sha(OUT / 'assessment.md') == json.loads((OUT / 'intake.json').read_text())['assessment_sha256']
    assert all(sha(PROJECT / p) == h for p, h in baseline['protected_unrelated_sha256'].items())
    files = json.loads((OUT / 'staging-allowlist.json').read_text())['files']
    assert len(files) == len(set(files))
    private_metadata=json.loads((OUT/'staging-allowlist.json').read_text())['private_metadata_only']
    assert {p for p in files if '/private/' in p}=={str((BASE/'fresh-arithmetic-discovery-r113'/n).relative_to(PROJECT)) for n in private_metadata}
    assert not any('/fresh-arithmetic-discovery-r114/' in p or '/fresh-structural-discovery-r149/' in p or '/fresh-analytic-discovery-r144/' in p for p in files)
    assert len(private_metadata)==4 and not any('/scratch/' in p for p in files)
    expected = {prefix + p for p in files}
    protected = {prefix + p for p in baseline['protected_unrelated_sha256']}
    if mode == 'prestage':
        assert not git('diff', '--cached', '--name-only')
        assert set(git('diff', '--name-only').decode().splitlines()) == protected | {
            prefix + taskpath, prefix + 'frontier/NEW-TEN-2026-10-14.md'}
        (OUT / 'integration-validation.json').write_text(json.dumps({
            'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'baseline_head': head, 'prestage_index_empty': True,
            'changed_existing_task_indices': [499], 'new_task_indices': [503],
            'other_tasks_and_unrelated_snapshot_fields_unchanged': True,
            'journal_prefix_and_actual_artifact_root_unchanged': True,
            'stable_named_originals_and_protected_unrelated_files_unchanged': True,
            'prospective_isolation_receipts_verified': True,
            'original_standing_brief_preserved': True,
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
