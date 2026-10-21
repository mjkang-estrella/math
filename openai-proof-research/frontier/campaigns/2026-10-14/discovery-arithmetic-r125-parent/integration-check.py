#!/usr/bin/env python3
"""Arithmetic125 archive and single-active-peer Arithmetic126 dispatch guard."""
import datetime,importlib.util,json,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2]
spec=importlib.util.spec_from_file_location('replay',O/'replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
def read(p):return json.loads(p.read_text())
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
def main(mode):
 base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
 if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
 path=str((B/'tasks.json').relative_to(P));old=json.loads(git('show',head+':'+prefix+path));new=read(B/'tasks.json');assert len(old['tasks'])==538 and len(new['tasks'])==539 and [i for i in range(538) if old['tasks'][i]!=new['tasks'][i]]==[535]
 assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'} and new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
 s0,s=old['current_work_snapshot'],new['current_work_snapshot'];assert {k for k in s0 if k in s and s0[k]!=s[k]}=={'observed_utc','note','status_note','fresh_discovery_current','t3_current_confirmed_running','t3_dispatch_observations','structural161_deferred_for_initial_exclusions'} and set(s)-set(s0)=={'arithmetic_r125_archive','arithmetic126_prospective_isolation'} and not set(s0)-set(s)
 assert s['t3_dispatch_observations'][:-1]==s0['t3_dispatch_observations'] and s['t3_last_polled_running']==[]
 for i,n in [(535,'task-status.json'),(538,'r126-dispatch.json')]:
  raw=read(O/n)['structuredContent'];assert all(new['tasks'][i][k]==v for k,v in raw.items())
 t=new['tasks'][535];assert t['parent_disposition']=='PREFREEZE_NO_NOMINEE' and t['correctness']==t['contribution']=='UNREVIEWED' and not t['scope_frozen'] and t['nominee'] is None and not t['accepted'] and t['count_change']==0
 t=new['tasks'][538];assert t['providerInstanceId']=='codex' and t['model']=='gpt-6-astra' and {e['id']:e['value'] for e in t['options']}=={'reasoningEffort':'high','serviceTier':'default'}
 assert s['fresh_discovery_current']==[new['tasks'][j]['output'] for j in [536,538]] and s['t3_current_confirmed_running']==[new['tasks'][j]['taskId'] for j in [536,538]]
 receipt=read(O/'prospective-isolation.json');assert receipt['before_arithmetic126_brief_or_root'] and receipt['structural161_not_yet_created'] and receipt['no_active_peer_status_poll_body_read_or_steer'] and len(receipt['active_peer_original_initial_briefs'])==1
 e=receipt['active_peer_original_initial_briefs'][0];assert e['brief']==old['tasks'][536]['brief'] and h.sha(B/e['brief'])==e['sha256']==old['tasks'][536]['brief_sha256'] and '*arithmetic*r126*' in (B/e['brief']).read_text()
 text=(B/t['brief']).read_text();assert h.sha(B/t['brief'])==t['brief_sha256'];marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';assert text.split(marker)[1]==(B/old['tasks'][535]['brief']).read_text().split(marker)[1];assert all(x in text for x in ['ONLY active peer','*analytic*r154*','*analytic*r155*','*structural*r161*','*structural*r162*','*t360s147*'])
 deferred=s['structural161_deferred_for_initial_exclusions'];assert deferred['arithmetic126_initial_exclusion_confirmed'] and deferred['waiting_for_analytic155_initial_exclusion'] and not deferred['campaign_paused'] and deferred['arithmetic126_initial_brief_sha256']==t['brief_sha256']
 assert not (B/'fresh-structural-discovery-r161').exists() and not (B/'expanded-target-2026-10-17/fresh-structural-r161-brief.txt').exists()
 assert h.snap(B/'fresh-arithmetic-discovery-r125')==read(O/'observed-root.json')['root'] and all(h.sha(P/e['path'])==e['sha256'] for e in read(O/'replay.json')['stable_named_originals']) and h.sha(O/'assessment.md')==read(O/'intake.json')['assessment_sha256']
 assert all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items()) and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
 allow=read(O/'staging-allowlist.json');files=allow['files'];assert len(files)==len(set(files))==37 and not allow['private_metadata_only'] and not any('/private/' in p for p in files) and len([p for p in files if '/fresh-arithmetic-discovery-r125/' in p])==18
 assert not any('/fresh-arithmetic-discovery-r126/' in p or '/fresh-analytic-discovery-r154/' in p or '/fresh-structural-discovery-r161/' in p for p in files)
 expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
 if mode=='prestage':
  assert not git('diff','--cached','--name-only') and set(git('diff','--name-only').decode().splitlines())==protected|{prefix+path,prefix+'frontier/NEW-TEN-2026-10-14.md'}
  (O/'integration-validation.json').write_text(json.dumps({'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_head':head,'changed_existing_task_indices':[535],'new_task_indices':[538],'other_tasks_and_snapshot_fields_unchanged':True,'one_existing_peer_original_initial_brief_excludes126':True,'complete_original_standing_brief_preserved':True,'arithmetic126_initial_structural161_guard_confirmed':True,'structural161_still_waits_for_analytic155_initial_guard':True,'journal_prefix_sealed_root_stable_originals_protected_files_unchanged':True,'explicit_allowed_paths':37,'newAccepted':19,'remaining':1,'publication':'STOPPED','mathematical_or_contribution_gate_assigned':False},indent=2)+'\n')
 else:
  if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
  else:
   assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
  assert actual==expected,(actual-expected,expected-actual);assert all(git('show',obj+prefix+p)==(P/p).read_bytes() for p in files) and set(git('diff','--name-only').decode().splitlines())==protected
 print(json.dumps({'phase':mode,'files':37,'tasks':539,'count':19,'remaining':1,'sealed_root_and_stable_inputs_unchanged':True}))
if __name__=='__main__':main(sys.argv[1])
