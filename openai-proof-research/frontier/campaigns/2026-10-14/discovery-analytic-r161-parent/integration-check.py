#!/usr/bin/env python3
"""Analytic161 immutable nominee intake and one actual independent-review dispatch."""
import datetime, importlib.util, json, stat, subprocess, sys
from pathlib import Path
O=Path(__file__).resolve().parent; B=O.parent; P=B.parents[2]
sp=importlib.util.spec_from_file_location('replay',O/'replay.py'); h=importlib.util.module_from_spec(sp); sp.loader.exec_module(h)
def read(p):return json.loads(p.read_text())
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
def main(mode):
 base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
 if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
 path=str((B/'tasks.json').relative_to(P));old=json.loads(git('show',head+':'+prefix+path));new=read(B/'tasks.json');assert len(old['tasks'])==562 and len(new['tasks'])==563 and [i for i in range(562) if old['tasks'][i]!=new['tasks'][i]]==[559]
 assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'} and new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
 s0,s=old['current_work_snapshot'],new['current_work_snapshot'];assert {k for k in s0 if s0[k]!=s[k]}=={'observed_utc','note','status_note','fresh_discovery_current','t3_current_confirmed_running','t3_dispatch_observations'} and set(s)-set(s0)=={'analytic_r161_intake','analytic_r161_reviews','analytic_r161_prospective_isolation'} and not set(s0)-set(s)
 assert s['t3_dispatch_observations'][:-1]==s0['t3_dispatch_observations'] and s['t3_last_polled_running']==[] and s['pending_terminal_intakes_20261021']==[]
 for i,n in [(559,'task-status.json'),(562,'proof-r1-dispatch.json')]:
  raw=read(O/n)['structuredContent'];assert all(new['tasks'][i][k]==v for k,v in raw.items())
 t=new['tasks'][559];intake=read(O/'intake.json');assert t['parent_disposition']==intake['parent_disposition']=='FULL_AUTHOR_PROOF_NOMINEE_PENDING_INDEPENDENT_REVIEWS' and t['correctness']==t['contribution']=='UNREVIEWED' and t['scope_frozen'] and t['nominee']=='T337A161' and not t['accepted'] and t['count_change']==0 and not t['pending_parent_intake']
 assert all(t[k]=='NOT_OPENED' for k in ['formalization','manuscript','local_release']) and t['independent_contribution_taskId'] is None and t['independent_contribution_status']=='PENDING_CAPACITY'
 t=new['tasks'][562];assert t['providerInstanceId']=='codex' and t['model']=='gpt-6-astra' and {e['id']:e['value'] for e in t['options']}=={'reasoningEffort':'high','serviceTier':'default'} and t['status']=='running' and not t['hasPendingChildRuns'] and not t['hasPendingQuestion'] and t['pendingApproval'] is None and t['review_kind']=='correctness'
 assert s['fresh_discovery_current']==[new['tasks'][i]['output'] for i in [560,561]] and s['t3_current_confirmed_running']==[new['tasks'][i]['taskId'] for i in [560,561,562]]
 receipt=read(O/'prospective-isolation.json');assert receipt['before_review_brief_or_root'] and receipt['both_existing_original_initial_briefs_exclude_analytic_r161_review_names'] and receipt['no_active_peer_body_read_poll_or_steer'] and len(receipt['existing_active_peer_original_initial_briefs'])==2
 for e,i in zip(receipt['existing_active_peer_original_initial_briefs'],[560,561]):
  peer=old['tasks'][i];assert e['task_index']==i and e['taskId']==peer['taskId'] and e['brief']==peer['brief'] and h.sha(B/e['brief'])==e['sha256']==peer['brief_sha256'] and '*analytic*r161*' in (B/e['brief']).read_text()
 root=B/'fresh-analytic-discovery-r161';assert h.sha(root/'FROZEN-STATEMENT.md')==h.SCOPE==intake['frozen_scope_sha256'] and h.sha(root/'AUTHOR-PROOF.md')==h.PROOF==intake['author_proof_sha256']
 for kind,other in [('proof','contribution'),('contribution','proof-r')]:
  key='brief' if kind=='proof' else 'contribution_brief';q=B/intake[key];text=q.read_text();assert h.sha(q)==intake[key+'_sha256'] and text.split('--- ENTIRE UNCHANGED FROZEN STATEMENT ---\n')[1]==(root/'FROZEN-STATEMENT.md').read_text() and '*analytic*r161*'+other+'*' in text
 assert not intake['contribution_review_dispatched'] and not (B/'analytic-r161-contribution-r1').exists() and s['analytic_r161_reviews']['contribution']['taskId'] is None and s['analytic_r161_reviews']['contribution']['status']=='PREPARED_PENDING_CAPACITY'
 observed=read(O/'observed-root.json');assert h.snap(root)==observed['root'] and stat.S_IMODE(root.stat().st_mode)==observed['root_mode'] and all(h.sha(P/e['path'])==e['sha256'] for e in read(O/'replay.json')['stable_named_originals']) and h.sha(O/'assessment.md')==intake['assessment_sha256']
 assert all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items()) and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
 files=read(O/'staging-allowlist.json')['files'];assert len(files)==len(set(files)) and not any('/private/' in p or '/controls/' in p for p in files) and len([p for p in files if '/fresh-analytic-discovery-r161/' in p])==18
 assert not any('/analytic-r161-proof-r1/' in p or '/analytic-r161-contribution-r1/' in p or '/fresh-arithmetic-discovery-r133/' in p or '/fresh-structural-discovery-r167/' in p for p in files)
 assert not any(p.endswith(('/observed-root.json','/replay.json')) for p in files)
 expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
 if mode=='prestage':
  assert not git('diff','--cached','--name-only') and set(git('diff','--name-only').decode().splitlines())==protected|{prefix+path,prefix+'frontier/NEW-TEN-2026-10-14.md'}
  (O/'integration-validation.json').write_text(json.dumps({'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_head':head,'changed_existing_task_indices':[559],'new_task_indices':[562],'other_tasks_and_snapshot_fields_unchanged':True,'full_frozen_scope_in_both_separate_review_briefs':True,'correctness_actually_dispatched':True,'contribution_prepared_not_dispatched_pending_capacity':True,'existing_original_peer_initial_briefs_exclude_review_identity':True,'no_peer_body_read_poll_or_steer':True,'sealed_author_root_stable_originals_journal_prefix_protected_files_unchanged':True,'protected_body_identity_inventory_and_replay_remain_local_unstaged':True,'explicit_allowed_paths':len(files),'newAccepted':19,'remaining':1,'publication':'STOPPED','mathematical_gate_assigned':False},indent=2)+'\n')
 else:
  if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
  else:
   assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
  assert actual==expected,(actual-expected,expected-actual);assert all(git('show',obj+prefix+p)==(P/p).read_bytes() for p in files) and set(git('diff','--name-only').decode().splitlines())==protected
 print(json.dumps({'phase':mode,'files':len(files),'tasks':563,'count':19,'remaining':1,'sealed_root_and_stable_inputs_unchanged':True}))
if __name__=='__main__':main(sys.argv[1])
