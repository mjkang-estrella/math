#!/usr/bin/env python3
"""Structural167 archive and actual independent Analytic161 contribution dispatch."""
import datetime,importlib.util,json,stat,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2]
sp=importlib.util.spec_from_file_location('replay',O/'replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
def read(p):return json.loads(p.read_text())
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
def main(mode):
 base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
 if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
 path=str((B/'tasks.json').relative_to(P));old=json.loads(git('show',head+':'+prefix+path));new=read(B/'tasks.json');assert len(old['tasks'])==563 and len(new['tasks'])==564 and [i for i in range(563) if old['tasks'][i]!=new['tasks'][i]]==[559,560,561]
 assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'} and new['newAccepted']==19 and new['remaining']==1 and new['latestAcceptance']==old['latestAcceptance']=='R041'
 assert {k for k in old['tasks'][559] if old['tasks'][559][k]!=new['tasks'][559][k]}=={'independent_contribution_taskId','independent_contribution_status'}
 s0,s=old['current_work_snapshot'],new['current_work_snapshot'];assert {k for k in s0 if s0[k]!=s[k]}=={'observed_utc','note','status_note','fresh_discovery_current','t3_current_confirmed_running','t3_dispatch_observations','pending_terminal_intakes_20261021','analytic_r161_reviews'} and set(s)-set(s0)=={'structural_r167_archive','analytic_r161_contribution_launch'} and not set(s0)-set(s)
 assert s['t3_dispatch_observations'][:-1]==s0['t3_dispatch_observations'] and s['t3_last_polled_running']==[] and s['fresh_discovery_current']==[] and s['t3_current_confirmed_running']==[new['tasks'][i]['taskId'] for i in [562,563]] and [e['task_index'] for e in s['pending_terminal_intakes_20261021']]==[561]
 for i,n in [(560,'task-status.json'),(561,'arithmetic133-terminal-status.json'),(563,'contribution-r1-dispatch.json')]:
  raw=read(O/n)['structuredContent'];assert all(new['tasks'][i][k]==v for k,v in raw.items())
 t=new['tasks'][560];assert t['parent_disposition']=='PREFREEZE_NO_NOMINEE' and not t['pending_parent_intake'] and not t['scope_frozen'] and t['nominee'] is None and t['correctness']==t['contribution']=='UNREVIEWED' and not t['accepted'] and t['count_change']==0
 assert new['tasks'][561]['pending_parent_intake'] and new['tasks'][561]['parent_disposition']=='PENDING_PARENT_INTAKE'
 t=new['tasks'][563];assert t['providerInstanceId']=='codex' and t['model']=='gpt-6-astra' and {e['id']:e['value'] for e in t['options']}=={'reasoningEffort':'high','serviceTier':'default'} and t['status']=='running' and not t['hasPendingChildRuns'] and not t['hasPendingQuestion'] and t['pendingApproval'] is None and t['review_kind']=='substantial-contribution'
 receipt=read(O/'prospective-isolation.json');q=B/receipt['original_correctness_initial_brief'];assert h.sha(q)==receipt['sha256']==old['tasks'][562]['brief_sha256'] and receipt['literal_exclusion'] in q.read_text() and receipt['before_contribution_root_creation_and_dispatch'] and receipt['no_correctness_body_status_or_activity_read'] and receipt['no_initial_brief_change']
 q=B/t['brief'];assert h.sha(q)==t['brief_sha256']==receipt['contribution_brief_sha256']==s0['analytic_r161_reviews']['contribution']['brief_sha256'] and receipt['reciprocal_literal_exclusion'] in q.read_text() and q.read_bytes()==git('show',head+':'+prefix+str(q.relative_to(P)))
 assert s['analytic_r161_reviews']['correctness']==s0['analytic_r161_reviews']['correctness'] and new['tasks'][559]['independent_contribution_taskId']==t['taskId'] and new['tasks'][559]['independent_contribution_status']=='running'
 observed=read(O/'observed-root.json');root=B/'fresh-structural-discovery-r167';assert h.snap(root)==observed['root'] and stat.S_IMODE(root.stat().st_mode)==observed['root_mode'] and all(h.sha(P/e['path'])==e['sha256'] for e in read(O/'replay.json')['stable_named_originals']) and h.sha(O/'assessment.md')==read(O/'intake.json')['assessment_sha256']
 author=B/'fresh-analytic-discovery-r161';authorobs=read(B/'discovery-analytic-r161-parent/observed-root.json');assert h.snap(author)==authorobs['root'] and h.sha(B/'discovery-analytic-r161-parent/assessment.md')==read(B/'discovery-analytic-r161-parent/intake.json')['assessment_sha256']
 assert all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items()) and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
 files=read(O/'staging-allowlist.json')['files'];assert len(files)==len(set(files)) and len([p for p in files if '/fresh-structural-discovery-r167/' in p])==11 and not any('/private/' in p or '/analytic-r161-proof-r1/' in p or '/analytic-r161-contribution-r1/' in p or '/fresh-arithmetic-discovery-r133/' in p or p.endswith(('/observed-root.json','/replay.json')) for p in files)
 expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
 if mode=='prestage':
  assert not git('diff','--cached','--name-only') and set(git('diff','--name-only').decode().splitlines())==protected|{prefix+path,prefix+'frontier/NEW-TEN-2026-10-14.md'}
  (O/'integration-validation.json').write_text(json.dumps({'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_head':head,'changed_existing_task_indices':[559,560,561],'new_task_indices':[563],'other_tasks_and_snapshot_fields_unchanged':True,'correctness_initial_prompt_reciprocally_excludes_contribution':True,'prepared_contribution_brief_unchanged_and_actually_dispatched':True,'arithmetic133_honestly_pending_separate_intake':True,'sealed_structural_and_analytic_author_roots_and_assessments_unchanged':True,'protected_identity_inventories_replay_local_unstaged':True,'journal_prefix_and_protected_unrelated_files_unchanged':True,'explicit_allowed_paths':len(files),'newAccepted':19,'remaining':1,'publication':'STOPPED','mathematical_gate_assigned':False},indent=2)+'\n')
 else:
  if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
  else:
   assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
  assert actual==expected,(actual-expected,expected-actual);assert all(git('show',obj+prefix+p)==(P/p).read_bytes() for p in files) and set(git('diff','--name-only').decode().splitlines())==protected
 print(json.dumps({'phase':mode,'files':len(files),'tasks':564,'count':19,'remaining':1,'author_roots_unchanged':True}))
if __name__=='__main__':main(sys.argv[1])
