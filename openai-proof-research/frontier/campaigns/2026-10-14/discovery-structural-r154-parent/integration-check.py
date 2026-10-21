#!/usr/bin/env python3
"""Check exact structural154 archive/structural155 dispatch integration and staging."""
import datetime,importlib.util,json,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2]
spec=importlib.util.spec_from_file_location('helpers',O/'replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
def read(p):return json.loads(p.read_text())
def git(*args):return subprocess.check_output(['git',*args],cwd=P)
def main(mode):
 base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
 if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
 taskpath=str((B/'tasks.json').relative_to(P));old=json.loads(git('show',head+':'+prefix+taskpath));new=read(B/'tasks.json');assert len(old['tasks'])==522 and len(new['tasks'])==523
 assert [i for i in range(522) if old['tasks'][i]!=new['tasks'][i]]==[518,520]
 assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'}
 assert new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
 s0,s=old['current_work_snapshot'],new['current_work_snapshot']
 assert {k for k in s0 if k in s and s0[k]!=s[k]}=={'observed_utc','note','status_note','fresh_discovery_current','t3_current_confirmed_running','t3_dispatch_observations'}
 assert set(s)-set(s0)=={'structural_r154_archive','structural155_prospective_isolation','arithmetic_r120_pending_archive'} and not set(s0)-set(s)
 assert s['t3_dispatch_observations'][:-1]==s0['t3_dispatch_observations'] and s['t3_last_polled_running']==[]
 for i,n in [(518,'task-status.json'),(520,'arithmetic120-terminal-status.json'),(522,'r155-dispatch.json')]:
  d=read(O/n)['structuredContent'];assert all(new['tasks'][i][k]==v for k,v in d.items())
 assert new['tasks'][518]['parent_disposition']=='PREFREEZE_NO_NOMINEE' and not new['tasks'][518]['scope_frozen'] and new['tasks'][518]['nominee'] is None
 assert new['tasks'][518]['correctness']==new['tasks'][518]['contribution']=='UNREVIEWED' and not new['tasks'][518]['accepted'] and new['tasks'][518]['count_change']==0
 assert new['tasks'][522]['providerInstanceId']=='codex' and new['tasks'][522]['model']=='gpt-6-astra' and {e['id']:e['value'] for e in new['tasks'][522]['options']}=={'reasoningEffort':'high','serviceTier':'default'}
 assert s['t3_current_confirmed_running']==[new['tasks'][i]['taskId'] for i in [521,522]] and s['fresh_discovery_current']==[new['tasks'][i]['output'] for i in [521,522]]
 assert new['tasks'][520]['parent_archive_pending'] and s['arithmetic_r120_pending_archive']['taskId']==new['tasks'][520]['taskId']
 receipt=read(O/'prospective-isolation.json');assert receipt['before_structural155_brief_or_root'] and receipt['no_peer_mathematical_body_read_or_steer'] and len(receipt['both_peer_original_initial_briefs'])==2
 for e,i in zip(receipt['both_peer_original_initial_briefs'],[520,521]):
  assert e['brief']==old['tasks'][i]['brief'] and h.sha(B/e['brief'])==e['sha256']==old['tasks'][i]['brief_sha256'] and '*structural*r155*' in (B/e['brief']).read_text()
 text=(B/new['tasks'][522]['brief']).read_text();assert h.sha(B/new['tasks'][522]['brief'])==new['tasks'][522]['brief_sha256'];marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
 assert text.split(marker)[1]==(B/old['tasks'][518]['brief']).read_text().split(marker)[1]
 assert all(x in text for x in ['*t360s147*','*arithmetic*r120*','*analytic*r149*','*arithmetic*r121*','*analytic*r150*'])
 journal=P/'frontier/NEW-TEN-2026-10-14.md';assert journal.read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
 assert h.snap(B/'fresh-structural-discovery-r154')==read(O/'observed-root.json')['root']
 assert all(h.sha(P/e['path'])==e['sha256'] for e in read(O/'replay.json')['stable_named_originals'])
 assert h.sha(O/'assessment.md')==read(O/'intake.json')['assessment_sha256']
 assert all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 allow=read(O/'staging-allowlist.json');files=allow['files'];assert len(files)==len(set(files))==43
 assert {p for p in files if '/private/' in p}=={str((B/'fresh-structural-discovery-r154'/n).relative_to(P)) for n in allow['private_metadata_and_own_diagnostic_only']}
 assert not any('/t360s147-proof-r1/' in p or '/t360s147-contribution-r1/' in p or '/fresh-structural-discovery-r155/' in p or '/seal/copied-controls/' in p or '/private/sources/preprints/' in p or '/private/search/' in p for p in files)
 expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
 if mode=='prestage':
  assert not git('diff','--cached','--name-only')
  assert set(git('diff','--name-only').decode().splitlines())==protected|{prefix+taskpath,prefix+'frontier/NEW-TEN-2026-10-14.md'}
  (O/'integration-validation.json').write_text(json.dumps({'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_head':head,'prestage_index_empty':True,'changed_existing_task_indices':[518,520],'new_task_indices':[522],'other_tasks_and_snapshot_fields_unchanged':True,'journal_prefix_and_actual_root_unchanged':True,'stable_originals_and_protected_files_unchanged':True,'both_original_peer_briefs_exclude_future155':True,'complete_original_standing_brief_preserved':True,'no_peer_mathematical_body_read_or_steer':True,'actual_arithmetic120_terminal_recorded_pending_archive':True,'explicit_allowed_paths':43,'newAccepted':19,'remaining':1,'publication':'STOPPED','mathematical_or_contribution_gate_assigned':False},indent=2)+'\n')
 else:
  if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
  else:
   assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
  assert actual==expected,(actual-expected,expected-actual)
  assert all(git('show',obj+prefix+p)==(P/p).read_bytes() for p in files)
  assert set(git('diff','--name-only').decode().splitlines())==protected
 print(json.dumps({'phase':mode,'files':43,'tasks':523,'count':19,'remaining':1,'sealed_root_and_stable_inputs_unchanged':True}))
if __name__=='__main__':main(sys.argv[1])
