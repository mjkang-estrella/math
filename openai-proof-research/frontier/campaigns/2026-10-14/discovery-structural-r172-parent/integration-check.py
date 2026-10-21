#!/usr/bin/env python3
"""Bounded Structural172 archive integration; no new launch or mathematical grade."""
import datetime, importlib.util, json, stat, subprocess, sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2]
sp=importlib.util.spec_from_file_location('replay',O/'replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
def read(f):return json.loads(f.read_text())
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
def main(mode):
    base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
    if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
    path=str((B/'tasks.json').relative_to(P));old=json.loads(git('show',head+':'+prefix+path));new=read(B/'tasks.json')
    assert len(old['tasks'])==len(new['tasks'])==578 and [i for i in range(578)if old['tasks'][i]!=new['tasks'][i]]==[574]
    assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'} and new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
    s0,s=old['current_work_snapshot'],new['current_work_snapshot'];assert {k for k in s0 if s0[k]!=s[k]}=={'observed_utc','note','status_note','pending_terminal_intakes_20261021'} and set(s)-set(s0)=={'structural_r172_archive'} and not set(s0)-set(s)
    assert not s['pending_terminal_intakes_20261021'] and not s['t3_last_polled_running'] and s['fresh_discovery_current']==['fresh-analytic-discovery-r165'] and s['t3_current_confirmed_running']==[new['tasks'][i]['taskId']for i in [575,576,577]]
    t=new['tasks'][574];assert all(t[k]==v for k,v in read(O/'task-status.json')['structuredContent'].items()) and t['parent_disposition']=='PREFREEZE_NO_NOMINEE' and not t['scope_frozen'] and t['nominee'] is None and t['correctness']==t['contribution']=='UNREVIEWED' and not t['accepted'] and t['count_change']==0
    intake=read(O/'intake.json');assert s['structural_r172_archive']==intake and h.sha(O/'assessment.md')==intake['assessment_sha256'] and intake['new_discovery']=='DEFERRED_CAPACITY_USED_BY_ANALYTIC165'
    observed=read(O/'observed-root.json');root=B/'fresh-structural-discovery-r172';assert h.snap(root)==observed['root'] and stat.S_IMODE(root.stat().st_mode)==observed['root_mode'] and all(h.sha(P/e['path'])==e['sha256']for e in read(O/'replay.json')['stable_named_originals'])
    for r,p in [('fresh-arithmetic-discovery-r136',B/'discovery-arithmetic-r136-parent'),('fresh-analytic-discovery-r164',B/'discovery-analytic-r164-parent')]:assert h.snap(B/r)==read(p/'observed-root.json')['root']
    a=B/'discovery-analytic-r161-parent'
    for r,p in [('fresh-analytic-discovery-r161',a),('analytic-r161-proof-r1',a/'proof-r1-adoption'),('analytic-r161-contribution-r1',a/'contribution-r1-adoption')]:assert h.snap(B/r)==read(p/'observed-root.json')['root']
    assert all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items()) and(P/'frontier/NEW-TEN-2026-10-14.md').read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
    files=read(O/'staging-allowlist.json')['files'];assert len(files)==len(set(files))==14 and len([p for p in files if'/fresh-structural-discovery-r172/'in p])==4 and not any('/private/'in p or'/controls/'in p or'/fresh-analytic-discovery-r165/'in p or'/arithmetic-r136-proof-r1/'in p or'/arithmetic-r136-contribution-r1/'in p or p.endswith(('/observed-root.json','/replay.json'))for p in files)
    expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
    if mode=='prestage':
        assert not git('diff','--cached','--name-only') and set(git('diff','--name-only').decode().splitlines())==protected|{prefix+path,prefix+'frontier/NEW-TEN-2026-10-14.md'}
        (O/'integration-validation.json').write_text(json.dumps({'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_head':head,'changed_existing_task_indices':[574],'new_task_indices':[],'other_tasks_and_snapshot_fields_unchanged':True,'sealed_archive_and_arithmetic136_analytic164_and_closed_analytic161_roots_unchanged':True,'private_bodies_nested_seals_and_identity_replay_metadata_local_unstaged':True,'journal_prefix_and_protected_unrelated_files_unchanged':True,'explicit_allowed_paths':14,'newAccepted':19,'remaining':1,'publication':'STOPPED','mathematical_gate_assigned':False},indent=2)+'\n')
    else:
        if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
        else:assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
        assert actual==expected,(actual-expected,expected-actual);assert all(git('show',obj+prefix+p)==(P/p).read_bytes()for p in files) and set(git('diff','--name-only').decode().splitlines())==protected
    print(json.dumps({'phase':mode,'files':14,'tasks':578,'count':19,'sealed_roots_unchanged':True}))
if __name__=='__main__':main(sys.argv[1])
