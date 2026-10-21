#!/usr/bin/env python3
"""Arithmetic133 no-nominee archive with no new dispatch or gate."""
import datetime,importlib.util,json,stat,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2]
sp=importlib.util.spec_from_file_location('replay',O/'replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
def read(p):return json.loads(p.read_text())
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
def main(mode):
 base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
 if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
 path=str((B/'tasks.json').relative_to(P));old=json.loads(git('show',head+':'+prefix+path));new=read(B/'tasks.json');assert len(old['tasks'])==len(new['tasks'])==564 and [i for i in range(564) if old['tasks'][i]!=new['tasks'][i]]==[561]
 assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'} and new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
 s0,s=old['current_work_snapshot'],new['current_work_snapshot'];assert {k for k in s0 if s0[k]!=s[k]}=={'observed_utc','note','status_note','pending_terminal_intakes_20261021'} and set(s)-set(s0)=={'arithmetic_r133_archive'} and not set(s0)-set(s)
 assert s['t3_dispatch_observations']==s0['t3_dispatch_observations'] and s['t3_last_polled_running']==[] and s['fresh_discovery_current']==[] and s['t3_current_confirmed_running']==[new['tasks'][i]['taskId'] for i in [562,563]] and not s['pending_terminal_intakes_20261021'] and [e['task_index'] for e in s0['pending_terminal_intakes_20261021']]==[561]
 t=new['tasks'][561];raw=read(O/'task-status.json')['structuredContent'];assert all(t[k]==v for k,v in raw.items()) and t['parent_disposition']=='PREFREEZE_NO_NOMINEE' and not t['pending_parent_intake'] and not t['scope_frozen'] and t['nominee'] is None and t['correctness']==t['contribution']=='UNREVIEWED' and not t['accepted'] and t['count_change']==0
 observed=read(O/'observed-root.json');root=B/'fresh-arithmetic-discovery-r133';assert h.snap(root)==observed['root'] and stat.S_IMODE(root.stat().st_mode)==observed['root_mode'] and all(h.sha(P/e['path'])==e['sha256'] for e in read(O/'replay.json')['stable_named_originals']) and h.sha(O/'assessment.md')==read(O/'intake.json')['assessment_sha256']
 for name,parent in [('fresh-analytic-discovery-r161','discovery-analytic-r161-parent'),('fresh-structural-discovery-r167','discovery-structural-r167-parent')]:
  assert h.snap(B/name)==read(B/parent/'observed-root.json')['root'] and h.sha(B/parent/'assessment.md')==read(B/parent/'intake.json')['assessment_sha256']
 assert all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items()) and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
 files=read(O/'staging-allowlist.json')['files'];assert len(files)==len(set(files))==26 and len([p for p in files if '/fresh-arithmetic-discovery-r133/' in p])==16 and not any('/private/' in p or '/evidence/' in p or '/analytic-r161-proof-r1/' in p or '/analytic-r161-contribution-r1/' in p or p.endswith(('/observed-root.json','/replay.json')) for p in files)
 expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
 if mode=='prestage':
  assert not git('diff','--cached','--name-only') and set(git('diff','--name-only').decode().splitlines())==protected|{prefix+path,prefix+'frontier/NEW-TEN-2026-10-14.md'}
  (O/'integration-validation.json').write_text(json.dumps({'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_head':head,'changed_existing_task_indices':[561],'new_task_indices':[],'other_tasks_and_snapshot_fields_unchanged':True,'all_notified_terminal_intakes_resolved':True,'existing_two_independent_reviews_unchanged_no_polling':True,'three_sealed_author_roots_and_assessments_unchanged':True,'protected_identity_inventories_replay_local_unstaged':True,'journal_prefix_and_protected_unrelated_files_unchanged':True,'explicit_allowed_paths':len(files),'newAccepted':19,'remaining':1,'publication':'STOPPED','mathematical_gate_assigned':False},indent=2)+'\n')
 else:
  if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
  else:
   assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
  assert actual==expected,(actual-expected,expected-actual);assert all(git('show',obj+prefix+p)==(P/p).read_bytes() for p in files) and set(git('diff','--name-only').decode().splitlines())==protected
 print(json.dumps({'phase':mode,'files':26,'tasks':564,'count':19,'remaining':1,'author_roots_unchanged':True}))
if __name__=='__main__':main(sys.argv[1])
