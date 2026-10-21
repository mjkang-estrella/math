#!/usr/bin/env python3
"""Exact two-dispatch integration check;no mathematical test or liveness polling."""
import datetime,hashlib,json,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2]
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=P)
def main(mode):
 baseline=read(O/'integration-baseline.json');head=baseline['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
 if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
 taskpath=str((B/'tasks.json').relative_to(P));old=json.loads(git('show',head+':'+prefix+taskpath));new=read(B/'tasks.json');assert len(old['tasks'])==518 and len(new['tasks'])==520 and old['tasks']==new['tasks'][:518]
 assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'}
 assert new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
 s0,s=old['current_work_snapshot'],new['current_work_snapshot'];assert {k for k in s0 if k in s and s0[k]!=s[k]}=={'observed_utc','note','status_note','fresh_discovery_current','t3_current_confirmed_running','t3_dispatch_observations','t360s147_reviews','arithmetic_discovery_deferred_for_t360s147_reviews'}
 assert set(s)-set(s0)=={'post_t360s147_distinct_discovery'} and not set(s0)-set(s)
 assert s['t3_dispatch_observations'][:-2]==s0['t3_dispatch_observations'] and s['t3_last_polled_running']==[]
 assert {k for k in s['t360s147_reviews'] if s['t360s147_reviews'][k]!=s0['t360s147_reviews'][k]}=={'discovery_deferred'} and not s['t360s147_reviews']['discovery_deferred']
 a,a0=s['arithmetic_discovery_deferred_for_t360s147_reviews'],s0['arithmetic_discovery_deferred_for_t360s147_reviews'];assert {k for k in a if a[k]!=a0[k]}=={'review_outcomes_still_pending'} and not a['review_outcomes_still_pending']
 marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=(B/old['tasks'][512]['brief']).read_text().split(marker)[1]
 for i,kind,n in [(518,'structural',154),(519,'analytic',148)]:
  d=read(O/(kind+str(n)+'-dispatch.json'))['structuredContent'];task=new['tasks'][i];assert all(task[k]==v for k,v in d.items())
  assert task['providerInstanceId']=='codex' and task['model']=='gpt-6-astra' and {e['id']:e['value'] for e in task['options']}=={'reasoningEffort':'high','serviceTier':'default'}
  p=B/task['brief'];text=p.read_text();assert sha(p)==task['brief_sha256'] and text.split(marker)[1]==standing
  assert all(x in text for x in ['*arithmetic*r119*','*structural*r154*','*analytic*r148*','*arithmetic*r120*','*structural*r155*','*analytic*r149*','*t360s147*'])
  assert 'T360S147 now has separate FULL correctnessPASS/no mathematical repairs and FULL contributionTECHNICAL' in text
 receipt=read(O/'prospective-isolation.json');e=receipt['arithmetic119_original_initial_brief'];assert receipt['before_both_new_briefs_and_roots'] and receipt['no_active_peer_status_body_read_or_steer']
 assert e['brief']==old['tasks'][517]['brief'] and sha(B/e['brief'])==e['sha256']==old['tasks'][517]['brief_sha256'] and all(x in (B/e['brief']).read_text() for x in ['*structural*r154*','*analytic*r148*'])
 assert s['fresh_discovery_current']==[new['tasks'][i]['output'] for i in [517,518,519]] and s['t3_current_confirmed_running']==[new['tasks'][i]['taskId'] for i in [517,518,519]]
 assert (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
 assert all(sha(P/p)==v for p,v in baseline['protected_unrelated_sha256'].items());files=read(O/'staging-allowlist.json')['files'];assert len(files)==len(set(files))==13
 assert not any('/private/' in p or '/fresh-structural-discovery-r154/' in p or '/fresh-analytic-discovery-r148/' in p or '/fresh-arithmetic-discovery-r119/' in p for p in files)
 expected={prefix+p for p in files};protected={prefix+p for p in baseline['protected_unrelated_sha256']}
 if mode=='prestage':
  assert not git('diff','--cached','--name-only') and set(git('diff','--name-only').decode().splitlines())==protected|{prefix+taskpath,prefix+'frontier/NEW-TEN-2026-10-14.md'}
  (O/'integration-validation.json').write_text(json.dumps({'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_head':head,'prestage_index_empty':True,'changed_existing_task_indices':[],'new_task_indices':[518,519],'old_task_records_and_gates_unchanged':True,'unrelated_snapshot_fields_unchanged':True,'reciprocal_original_initial_prompt_exclusions_verified':True,'complete_standing_brief_preserved':True,'no_peer_status_body_read_or_steer':True,'journal_prefix_and_protected_files_unchanged':True,'explicit_paths':13,'newAccepted':19,'remaining':1,'publication':'STOPPED'},indent=2)+'\n')
 else:
  if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
  else:
   assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
  assert actual==expected,(actual-expected,expected-actual)
  assert all(git('show',obj+prefix+p)==(P/p).read_bytes() for p in files) and set(git('diff','--name-only').decode().splitlines())==protected
 print(json.dumps({'phase':mode,'files':13,'tasks':520,'count':19,'remaining':1,'two_actual_discovery_dispatches':True}))
if __name__=='__main__':main(sys.argv[1])
