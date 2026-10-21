#!/usr/bin/env python3
"""Narrow first author-response archive and newly notified nominee queue."""
import datetime, importlib.util, json, stat, subprocess, sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parents[1];P=B.parents[2]
sp=importlib.util.spec_from_file_location('replay',O/'replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
def read(p):return json.loads(p.read_text())
def git(*args):return subprocess.check_output(['git',*args],cwd=P)
def main(mode):
    base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
    if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
    rel=(B/'tasks.json').relative_to(P).as_posix();old=json.loads(git('show',head+':'+prefix+rel));new=read(B/'tasks.json');assert len(old['tasks'])==len(new['tasks'])==582 and [i for i in range(582)if old['tasks'][i]!=new['tasks'][i]]==[571,579,580]
    assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'} and new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']=='R041'
    s0=old['current_work_snapshot'];s=new['current_work_snapshot'];assert {k for k in s0 if s0[k]!=s[k]}=={'observed_utc','note','status_note','t3_current_confirmed_running','fresh_discovery_current','pending_terminal_intakes_20261021','arithmetic_r136_repair'} and set(s)-set(s0)=={'arithmetic_r136_repair_adoption','arithmetic137_preparation_deferred'} and not set(s0)-set(s)
    for i,n in [(579,'task-status.json'),(580,'analytic-r166-notified-terminal.json')]:assert all(new['tasks'][i][k]==v for k,v in read(O/n)['structuredContent'].items())
    a=read(O/'adoption.json');assert s['arithmetic_r136_repair_adoption']==a and a['response_disposition']=='UNRESOLVED_FULL_SCOPE_REPAIR' and not a['review_retry'] and not a['accepted'] and a['count_change']==0 and h.sha(O/'assessment.md')==a['parent_assessment_sha256'] and a['correctness']=='NEEDS_REPAIR' and a['contribution']=='INCOMPLETE' and a['correctness_condition']=='NOT_DISCHARGED_CORRECTNESS_NEEDS_REPAIR'
    assert new['tasks'][571]['correctness']=='NEEDS_REPAIR' and new['tasks'][571]['contribution']=='INCOMPLETE' and new['tasks'][579]['parent_disposition']=='UNRESOLVED_FULL_SCOPE_REPAIR' and s['pending_terminal_intakes_20261021']==[a['pending_terminal_intake']] and s['t3_current_confirmed_running']==[new['tasks'][581]['taskId']] and s['fresh_discovery_current']==['fresh-structural-discovery-r174']
    assert not (B/'fresh-arithmetic-discovery-r137').exists() and not (B/'expanded-target-2026-10-17/fresh-arithmetic-r137-brief.txt').exists()
    root=B/'arithmetic-r136-repair-r1';observed=read(O/'observed-root.json');assert h.snap(root)==observed['root'] and stat.S_IMODE(root.stat().st_mode)==observed['root_mode'] and h.sha(root/'FROZEN.md')==a['frozen_scope_sha256']
    ar=B/'discovery-arithmetic-r136-parent';an=B/'discovery-analytic-r161-parent'
    for r,p in [('fresh-arithmetic-discovery-r136',ar),('arithmetic-r136-proof-r1',ar/'proof-r1-adoption'),('arithmetic-r136-contribution-r1',ar/'contribution-r1-adoption'),('fresh-analytic-discovery-r161',an),('analytic-r161-proof-r1',an/'proof-r1-adoption'),('analytic-r161-contribution-r1',an/'contribution-r1-adoption')]:assert h.snap(B/r)==read(p/'observed-root.json')['root']
    assert all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items()) and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
    files=read(O/'staging-allowlist.json')['files'];assert len(files)==len(set(files))==21 and len([p for p in files if '/arithmetic-r136-repair-r1/'in p])==9 and not any('/private/'in p or '/controls/'in p or '/fresh-analytic-discovery-r166/'in p or p.endswith(('/observed-root.json','/replay.json'))for p in files)
    expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
    if mode=='prestage':
        assert not git('diff','--cached','--name-only') and set(git('diff','--name-only').decode().splitlines())==protected|{prefix+rel,prefix+'frontier/NEW-TEN-2026-10-14.md'}
        (O/'integration-validation.json').write_text(json.dumps({'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_head':head,'changed_existing_task_indices':[571,579,580],'new_tasks':0,'other_tasks_and_snapshot_fields_unchanged':True,'exact_response_archive':'UNRESOLVED_FULL_SCOPE_REPAIR','correctness':'NEEDS_REPAIR','contribution':'INCOMPLETE','no_review_retry_or_downstream_gates':True,'fixed_B22_does_not_refute_eventual_B0_theorem':True,'analytic166_notified_nominee_queued_for_separate_intake':True,'arithmetic137_not_dispatched':True,'sealed_author_review_closed_roots_and_protected_unrelated_files_unchanged':True,'private_protected_bodies_identity_metadata_local_unstaged':True,'explicit_allowed_paths':21,'newAccepted':19,'remaining':1,'publication':'STOPPED'},indent=2)+'\n')
    else:
        if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
        else:assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
        assert actual==expected,(actual-expected,expected-actual);assert all(git('show',obj+prefix+p)==(P/p).read_bytes()for p in files) and set(git('diff','--name-only').decode().splitlines())==protected
    print(json.dumps({'phase':mode,'files':21,'tasks':582,'count':19,'sealed_roots_unchanged':True}))
if __name__=='__main__':main(sys.argv[1])
