#!/usr/bin/env python3
"""Validate one archive and actual restart chains without rereading active bodies."""
import datetime, importlib.util, json, subprocess, sys
from pathlib import Path
O=Path(__file__).resolve().parent; B=O.parent; P=B.parents[2]; R=B/'server-restart-2026-10-20-parent'
spec=importlib.util.spec_from_file_location('s148_helpers',O/'replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
def read(p):return json.loads(p.read_text())
def result(p):return read(p)['structuredContent']
def git(*args):return subprocess.check_output(['git',*args],cwd=P)
def check(mode):
    baseline=read(O/'integration-baseline.json'); head=baseline['head']; prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
    if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
    taskpath=str((B/'tasks.json').relative_to(P));old=json.loads(git('show',head+':'+prefix+taskpath));new=read(B/'tasks.json')
    assert len(old['tasks'])==497 and len(new['tasks'])==502
    assert [i for i in range(497) if old['tasks'][i]!=new['tasks'][i]]==[494,495,496]
    assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'}
    assert new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
    s0,s=old['current_work_snapshot'],new['current_work_snapshot']
    assert {k for k in s0 if s0[k]!=s[k]}=={'observed_utc','note','status_note','fresh_discovery_current','t3_current_confirmed_running','t3_dispatch_observations'}
    assert set(s)-set(s0)=={'structural_r148_archive','server_restart_recovery_20261020','structural149_prospective_isolation'} and not set(s0)-set(s)
    assert s['t3_dispatch_observations'][:-5]==s0['t3_dispatch_observations'] and s['t3_last_polled_running']==[]
    records=[(494,O/'task-status.json'),(495,R/'arithmetic113-cancelled.json'),(496,R/'analytic143-cancelled.json'),(497,R/'arithmetic113-r2-interrupted.json'),(498,R/'analytic143-r2-interrupted.json'),(499,R/'arithmetic113-recovery-r3-dispatch.json'),(500,R/'analytic143-recovery-r3-dispatch.json'),(501,O/'r149-dispatch.json')]
    for i,p in records:
        d=result(p);assert all(new['tasks'][i][k]==v for k,v in d.items())
    assert new['tasks'][494]['parent_disposition']=='PREFREEZE_NO_NOMINEE' and not new['tasks'][494]['scope_frozen'] and new['tasks'][494]['nominee'] is None
    assert [new['tasks'][i]['status'] for i in range(494,502)]==['completed','cancelled','cancelled','interrupted','interrupted','running','running','running']
    assert s['t3_current_confirmed_running']==[new['tasks'][i]['taskId'] for i in [499,500,501]]
    assert s['fresh_discovery_current']==[new['tasks'][i]['output'] for i in [499,500,501]]
    for i in range(497,502):
        e=new['tasks'][i];assert h.sha(B/e['brief'])==e['brief_sha256'] and e['accepted'] is False and e['count_change']==0 and e['publication']=='STOPPED'
        assert e['providerInstanceId']=='codex' and e['model']=='gpt-6-astra'
        assert {x['id']:x['value'] for x in e['options']}=={'reasoningEffort':'high','serviceTier':'default'}
    for old_i,r2_i,r3_i,lane,n in [(495,497,499,'arithmetic',113),(496,498,500,'analytic',143)]:
        assert new['tasks'][old_i]['recovery_taskId']==new['tasks'][r2_i]['taskId']
        assert new['tasks'][r2_i]['recovery_taskId']==new['tasks'][r3_i]['taskId'] and new['tasks'][r3_i]['previous_interrupted_taskId']==new['tasks'][r2_i]['taskId']
        r1=(B/old['tasks'][old_i]['brief']).read_text();r2=(B/new['tasks'][r2_i]['brief']).read_text();r3=(B/new['tasks'][r3_i]['brief']).read_text()
        assert r2.split('--- COMPLETE ORIGINAL r1 BRIEF, preserved byte-for-byte below ---\n')[1]==r1
        assert r3.split('--- COMPLETE r2 RECOVERY BRIEF INCLUDING COMPLETE ORIGINAL r1 AND STANDING BRIEF, preserved byte-for-byte below ---\n')[1]==r2
        assert result(R/f'{lane}{n}-r2-interrupted.json')['summary'] in r3
        assert '*structural*r149*' in r2 and '*structural*r149*' in r3
        assert new['tasks'][old_i]['output']==new['tasks'][r2_i]['output']==new['tasks'][r3_i]['output']
    marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
    text=(B/new['tasks'][501]['brief']).read_text();assert text.split(marker)[1]==(B/old['tasks'][494]['brief']).read_text().split(marker)[1]
    assert all(x in text for x in ['*arithmetic*r113*','*analytic*r143*','*arithmetic*r114*','*analytic*r144*'])
    receipt=read(O/'prospective-isolation.json');assert receipt['before_new149_brief_or_root'] and len(receipt['both_active_initial_briefs'])==2
    for e,i in zip(receipt['both_active_initial_briefs'],[499,500]):
        assert e['brief']==new['tasks'][i]['brief'] and h.sha(B/e['brief'])==e['sha256']==new['tasks'][i]['brief_sha256']
    journal=P/'frontier/NEW-TEN-2026-10-14.md';assert journal.read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
    assert h.snap(B/'fresh-structural-discovery-r148')==read(O/'observed-root.json')['root']
    for e in read(O/'replay.json')['stable_named_originals']:assert h.sha(P/e['path'])==e['sha256']
    assert h.sha(O/'assessment.md')==read(O/'intake.json')['assessment_sha256']
    assert all(h.sha(P/p)==v for p,v in baseline['protected_unrelated_sha256'].items())
    a=read(O/'staging-allowlist.json');files=a['files'];assert len(files)==len(set(files))
    assert {p for p in files if '/private/' in p}=={str((B/'fresh-structural-discovery-r148'/n).relative_to(P)) for n in a['private_metadata_only']}
    assert not any(any('/'+root+'/' in p for root in ['fresh-arithmetic-discovery-r113','fresh-analytic-discovery-r143','fresh-structural-discovery-r149']) for p in files)
    assert not any('/scratch/' in p or '/private/history_scan_initial.py' in p for p in files)
    expected={prefix+p for p in files};protected={prefix+p for p in baseline['protected_unrelated_sha256']}
    if mode=='prestage':
        assert not git('diff','--cached','--name-only')
        assert set(git('diff','--name-only').decode().splitlines())==protected|{prefix+taskpath,prefix+'frontier/NEW-TEN-2026-10-14.md'}
        (O/'integration-validation.json').write_text(json.dumps({'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_head':head,'prestage_index_empty':True,'changed_existing_task_indices':[494,495,496],'new_task_indices':[497,498,499,500,501],'other_tasks_and_unrelated_snapshot_fields_unchanged':True,'journal_prefix_and_actual_sealed_root_unchanged':True,'stable_named_originals_and_protected_unrelated_files_unchanged':True,'original_complete_briefs_preserved':True,'actual_cancelled_interrupted_and_distinct_recovery_records_preserved':True,'active_recovery_root_bodies_not_used_as_stability_inputs':True,'prospective_isolation_receipts_verified':True,'explicit_allowed_paths':len(files),'newAccepted':19,'remaining':1,'publication':'STOPPED','mathematical_or_contribution_gate_assigned':False},indent=2)+'\n')
    else:
        if mode=='staged':
            actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
        else:
            assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head
            actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
        assert actual==expected,(actual-expected,expected-actual)
        assert all(git('show',obj+prefix+p)==(P/p).read_bytes() for p in files)
        assert set(git('diff','--name-only').decode().splitlines())==protected
    print(json.dumps({'phase':mode,'files':len(files),'tasks':len(new['tasks']),'count':19,'remaining':1,'sealed_root_and_stable_inputs_unchanged':True,'no_live_recovery_body_check':True}))
if __name__=='__main__':check(sys.argv[1])
