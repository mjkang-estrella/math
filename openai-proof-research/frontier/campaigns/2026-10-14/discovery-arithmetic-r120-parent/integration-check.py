#!/usr/bin/env python3
"""Exact Arithmetic120 archive / Arithmetic121 dispatch integration check."""
import datetime, importlib.util, json, subprocess, sys
from pathlib import Path
O=Path(__file__).resolve().parent; B=O.parent; P=B.parents[2]
spec=importlib.util.spec_from_file_location('archive',O/'replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
def read(p): return json.loads(p.read_text())
def git(*args): return subprocess.check_output(['git',*args],cwd=P)
def main(mode):
 base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip()
 assert prefix=='openai-proof-research/'
 if mode!='committed': assert git('rev-parse','HEAD').decode().strip()==head
 taskpath=str((B/'tasks.json').relative_to(P));old=json.loads(git('show',head+':'+prefix+taskpath));new=read(B/'tasks.json')
 assert len(old['tasks'])==523 and len(new['tasks'])==524
 assert [i for i in range(523) if old['tasks'][i]!=new['tasks'][i]]==[520]
 assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'}
 assert new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
 s0,s=old['current_work_snapshot'],new['current_work_snapshot']
 assert {k for k in s0 if k in s and s0[k]!=s[k]}=={'observed_utc','note','status_note','fresh_discovery_current','t3_current_confirmed_running','t3_dispatch_observations'}
 assert set(s)-set(s0)=={'arithmetic_r120_archive','arithmetic121_prospective_isolation'}
 assert set(s0)-set(s)=={'arithmetic_r120_pending_archive'}
 assert s['t3_dispatch_observations'][:-1]==s0['t3_dispatch_observations'] and s['t3_last_polled_running']==[]
 for i,n in [(520,'task-status.json'),(523,'r121-dispatch.json')]:
  d=read(O/n)['structuredContent'];assert all(new['tasks'][i][k]==v for k,v in d.items())
 t=new['tasks'][520]
 assert 'parent_archive_pending' not in t and t['parent_disposition']=='PREFREEZE_NO_NOMINEE' and not t['scope_frozen'] and t['nominee'] is None
 assert t['correctness']==t['contribution']=='UNREVIEWED' and not t['accepted'] and t['count_change']==0
 t=new['tasks'][523]
 assert t['providerInstanceId']=='codex' and t['model']=='gpt-6-astra' and {e['id']:e['value'] for e in t['options']}=={'reasoningEffort':'high','serviceTier':'default'}
 assert s['t3_current_confirmed_running']==[new['tasks'][i]['taskId'] for i in [521,522,523]]
 assert s['fresh_discovery_current']==[new['tasks'][i]['output'] for i in [521,522,523]]
 receipt=read(O/'prospective-isolation.json')
 assert receipt['before_arithmetic121_brief_or_root'] and receipt['no_active_peer_status_body_read_or_steer'] and len(receipt['both_peer_original_initial_briefs'])==2
 for e,i in zip(receipt['both_peer_original_initial_briefs'],[521,522]):
  assert e['brief']==old['tasks'][i]['brief'] and h.sha(B/e['brief'])==e['sha256']==old['tasks'][i]['brief_sha256']
  assert '*arithmetic*r121*' in (B/e['brief']).read_text()
 text=(B/t['brief']).read_text();assert h.sha(B/t['brief'])==t['brief_sha256']
 marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
 assert text.split(marker)[1]==(B/old['tasks'][520]['brief']).read_text().split(marker)[1]
 assert all(x in text for x in ['*t360s147*','*structural*r155*','*analytic*r149*','*structural*r156*','*analytic*r150*'])
 journal=P/'frontier/NEW-TEN-2026-10-14.md';assert journal.read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
 assert h.snap(B/'fresh-arithmetic-discovery-r120')==read(O/'observed-root.json')['root']
 assert all(h.sha(P/e['path'])==e['sha256'] for e in read(O/'replay.json')['stable_named_originals'])
 assert h.sha(O/'assessment.md')==read(O/'intake.json')['assessment_sha256']
 assert all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 allow=read(O/'staging-allowlist.json');files=allow['files'];assert len(files)==len(set(files))==31
 assert not any('/private/' in p or '/fresh-arithmetic-discovery-r121/' in p or '/fresh-analytic-discovery-r149/' in p or '/fresh-structural-discovery-r155/' in p for p in files)
 assert len([p for p in files if '/fresh-arithmetic-discovery-r120/' in p])==13
 expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
 if mode=='prestage':
  assert not git('diff','--cached','--name-only')
  assert set(git('diff','--name-only').decode().splitlines())==protected|{prefix+taskpath,prefix+'frontier/NEW-TEN-2026-10-14.md'}
  (O/'integration-validation.json').write_text(json.dumps({'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_head':head,'prestage_index_empty':True,'changed_existing_task_indices':[520],'new_task_indices':[523],'other_tasks_and_snapshot_fields_unchanged':True,'removed_pending_archive_marker':True,'journal_prefix_and_sealed_root_unchanged':True,'stable_originals_and_protected_files_unchanged':True,'both_original_peer_briefs_exclude_future121':True,'complete_original_standing_brief_preserved':True,'no_active_peer_status_body_read_or_steer':True,'explicit_allowed_paths':31,'newAccepted':19,'remaining':1,'publication':'STOPPED','mathematical_or_contribution_gate_assigned':False},indent=2)+'\n')
 else:
  if mode=='staged':
   actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':'
   subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
  else:
   assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head
   actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
  assert actual==expected,(actual-expected,expected-actual)
  assert all(git('show',obj+prefix+p)==(P/p).read_bytes() for p in files)
  assert set(git('diff','--name-only').decode().splitlines())==protected
 print(json.dumps({'phase':mode,'files':31,'tasks':524,'count':19,'remaining':1,'sealed_root_and_stable_inputs_unchanged':True}))
if __name__=='__main__':main(sys.argv[1])
