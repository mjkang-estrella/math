#!/usr/bin/env python3
"""Check exact structural153 archive/arithmetic119 dispatch integration and staging."""
import datetime,importlib.util,json,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2]
spec=importlib.util.spec_from_file_location('helpers',O/'replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
def read(p):return json.loads(p.read_text())
def git(*args):return subprocess.check_output(['git',*args],cwd=P)
def main(mode):
 base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
 if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
 taskpath=str((B/'tasks.json').relative_to(P));old=json.loads(git('show',head+':'+prefix+taskpath));new=read(B/'tasks.json');assert len(old['tasks'])==517 and len(new['tasks'])==518
 assert [i for i in range(517) if old['tasks'][i]!=new['tasks'][i]]==[514]
 assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'}
 assert new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
 s0,s=old['current_work_snapshot'],new['current_work_snapshot']
 assert {k for k in s0 if k in s and s0[k]!=s[k]}=={'observed_utc','note','status_note','fresh_discovery_current','t3_current_confirmed_running','t3_dispatch_observations','arithmetic_discovery_deferred_for_t360s147_reviews'}
 assert set(s)-set(s0)=={'structural_r153_archive','arithmetic119_prospective_isolation'} and not set(s0)-set(s)
 assert s['t3_dispatch_observations'][:-1]==s0['t3_dispatch_observations'] and s['t3_last_polled_running']==[]
 for i,n in [(514,'task-status.json'),(517,'r119-dispatch.json')]:
  d=read(O/n)['structuredContent'];assert all(new['tasks'][i][k]==v for k,v in d.items())
 assert new['tasks'][514]['parent_disposition']=='PREFREEZE_NO_NOMINEE' and not new['tasks'][514]['scope_frozen'] and new['tasks'][514]['nominee'] is None
 assert new['tasks'][514]['correctness']==new['tasks'][514]['contribution']=='UNREVIEWED' and not new['tasks'][514]['accepted'] and new['tasks'][514]['count_change']==0
 assert new['tasks'][517]['providerInstanceId']=='codex' and new['tasks'][517]['model']=='gpt-6-astra' and {e['id']:e['value'] for e in new['tasks'][517]['options']}=={'reasoningEffort':'high','serviceTier':'default'}
 assert s['t3_current_confirmed_running']==[new['tasks'][i]['taskId'] for i in [515,516,517]] and s['fresh_discovery_current']==[new['tasks'][517]['output']]
 receipt=read(O/'prospective-isolation.json');assert receipt['before_arithmetic119_brief_or_root'] and receipt['no_active_peer_status_body_read_or_steer'] and len(receipt['active_review_initial_briefs'])==2
 for e,i in zip(receipt['active_review_initial_briefs'],[515,516]):
  assert e['brief']==old['tasks'][i]['brief'] and h.sha(B/e['brief'])==e['sha256']==old['tasks'][i]['brief_sha256'] and '*arithmetic*r119*' in (B/e['brief']).read_text()
 text=(B/new['tasks'][517]['brief']).read_text();assert h.sha(B/new['tasks'][517]['brief'])==new['tasks'][517]['brief_sha256'];marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
 assert text.split(marker)[1]==(B/old['tasks'][513]['brief']).read_text().split(marker)[1]
 assert all(x in text for x in ['*t360s147*','*analytic*r147*','*structural*r153*','*structural*r154*','*analytic*r148*'])
 journal=P/'frontier/NEW-TEN-2026-10-14.md';assert journal.read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
 assert h.snap(B/'fresh-structural-discovery-r153')==read(O/'observed-root.json')['root']
 assert all(h.sha(P/e['path'])==e['sha256'] for e in read(O/'replay.json')['stable_named_originals'])
 assert h.sha(O/'assessment.md')==read(O/'intake.json')['assessment_sha256']
 assert all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 allow=read(O/'staging-allowlist.json');files=allow['files'];assert len(files)==len(set(files))==43
 assert {p for p in files if '/private/' in p}=={str((B/'fresh-structural-discovery-r153'/n).relative_to(P)) for n in allow['private_metadata_and_own_diagnostic_only']}
 assert not any('/t360s147-proof-r1/' in p or '/t360s147-contribution-r1/' in p or '/fresh-arithmetic-discovery-r119/' in p or '/private/controls/selection/' in p or '/private/sources/preprints/' in p or '/private/search/' in p for p in files)
 expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
 if mode=='prestage':
  assert not git('diff','--cached','--name-only')
  assert set(git('diff','--name-only').decode().splitlines())==protected|{prefix+taskpath,prefix+'frontier/NEW-TEN-2026-10-14.md'}
  (O/'integration-validation.json').write_text(json.dumps({'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_head':head,'prestage_index_empty':True,'changed_existing_task_indices':[514],'new_task_indices':[517],'other_tasks_and_snapshot_fields_unchanged':True,'journal_prefix_and_actual_root_unchanged':True,'stable_originals_and_protected_files_unchanged':True,'both_original_review_briefs_exclude_future119':True,'complete_original_standing_brief_preserved':True,'no_peer_status_or_body_read_or_steer':True,'explicit_allowed_paths':43,'newAccepted':19,'remaining':1,'publication':'STOPPED','mathematical_or_contribution_gate_assigned':False},indent=2)+'\n')
 else:
  if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
  else:
   assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
  assert actual==expected,(actual-expected,expected-actual)
  assert all(git('show',obj+prefix+p)==(P/p).read_bytes() for p in files)
  assert set(git('diff','--name-only').decode().splitlines())==protected
 print(json.dumps({'phase':mode,'files':43,'tasks':518,'count':19,'remaining':1,'sealed_root_and_stable_inputs_unchanged':True}))
if __name__=='__main__':main(sys.argv[1])
