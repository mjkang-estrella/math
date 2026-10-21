#!/usr/bin/env python3
"""Exact failed-source-selection adoption; no successor task dispatched."""
import datetime,importlib.util,json,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2]
spec=importlib.util.spec_from_file_location('replay',O/'replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
def read(p):return json.loads(p.read_text())
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
def main(mode):
 base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
 if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
 path=str((B/'tasks.json').relative_to(P));old=json.loads(git('show',head+':'+prefix+path));new=read(B/'tasks.json');assert len(old['tasks'])==len(new['tasks'])==538 and [i for i in range(538) if old['tasks'][i]!=new['tasks'][i]]==[537]
 assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'} and new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
 s0,s=old['current_work_snapshot'],new['current_work_snapshot'];assert {k for k in s0 if k in s and s0[k]!=s[k]}=={'observed_utc','note','status_note','fresh_discovery_current','t3_current_confirmed_running'} and set(s)-set(s0)=={'structural_r160_archive','structural161_deferred_for_initial_exclusions'} and not set(s0)-set(s)
 assert s['t3_dispatch_observations']==s0['t3_dispatch_observations'] and s['t3_last_polled_running']==[]
 t=new['tasks'][537];raw=read(O/'task-status.json')['structuredContent'];assert all(t[k]==v for k,v in raw.items());assert t['parent_disposition']=='PREFREEZE_NO_NOMINEE' and t['correctness']==t['contribution']=='UNREVIEWED' and t['nominee'] is None and not t['scope_frozen'] and not t['accepted'] and t['count_change']==0
 assert t['discovery_requirements_met']==t['pinned_source_development_met']==t['sustained_mathematical_discovery_met']==False
 assert s['t3_current_confirmed_running']==[new['tasks'][i]['taskId'] for i in [535,536]] and s['fresh_discovery_current']==[new['tasks'][i]['output'] for i in [535,536]]
 req=read(O/'structural161-launch-prerequisites.json');assert req['dispatch_deferred'] and req['no_new_structural_brief_root_or_task'] and req['no_active_peer_status_poll_or_mathematical_body_read_or_steer']
 for e,i in zip(req['original_initial_peer_briefs'],[535,536]):
  assert e['brief']==old['tasks'][i]['brief'] and h.sha(B/e['brief'])==e['sha256']==old['tasks'][i]['brief_sha256'];text=(B/e['brief']).read_text();assert '*structural*r160*' in text and '*structural*r161*' not in text
 assert not (B/'fresh-structural-discovery-r161').exists() and not (B/'expanded-target-2026-10-17/fresh-structural-r161-brief.txt').exists()
 assert h.snap(B/'fresh-structural-discovery-r160')==read(O/'observed-root.json')['root'] and all(h.sha(P/e['path'])==e['sha256'] for e in read(O/'replay.json')['stable_named_originals']) and h.sha(O/'assessment.md')==read(O/'intake.json')['assessment_sha256']
 assert all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items()) and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
 allow=read(O/'staging-allowlist.json');files=allow['files'];assert len(files)==len(set(files))==24 and not allow['private_metadata_only'] and not any('/private/' in p for p in files) and len([p for p in files if '/fresh-structural-discovery-r160/' in p])==9
 assert not any('/fresh-arithmetic-discovery-r125/' in p or '/fresh-analytic-discovery-r154/' in p or '/fresh-structural-discovery-r161/' in p for p in files)
 expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
 if mode=='prestage':
  assert not git('diff','--cached','--name-only') and set(git('diff','--name-only').decode().splitlines())==protected|{prefix+path,prefix+'frontier/NEW-TEN-2026-10-14.md'}
  (O/'integration-validation.json').write_text(json.dumps({'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_head':head,'changed_existing_task_indices':[537],'new_task_indices':[],'other_tasks_and_snapshot_fields_unchanged':True,'no_new_dispatch_or_structural161_brief_root':True,'both_peer_original_initial_briefs_lack161_guard':True,'next_successor_exclusions_recorded':True,'journal_prefix_sealed_root_stable_originals_protected_files_unchanged':True,'explicit_allowed_paths':24,'newAccepted':19,'remaining':1,'publication':'STOPPED','mathematical_or_contribution_gate_assigned':False},indent=2)+'\n')
 else:
  if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
  else:
   assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
  assert actual==expected,(actual-expected,expected-actual);assert all(git('show',obj+prefix+p)==(P/p).read_bytes() for p in files) and set(git('diff','--name-only').decode().splitlines())==protected
 print(json.dumps({'phase':mode,'files':24,'tasks':538,'count':19,'remaining':1,'new_tasks':0,'sealed_root_and_stable_inputs_unchanged':True}))
if __name__=='__main__':main(sys.argv[1])
