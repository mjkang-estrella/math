#!/usr/bin/env python3
"""Exact Analytic150 archive / Analytic151 dispatch integration check."""
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
 assert len(old['tasks'])==527 and len(new['tasks'])==528
 assert [i for i in range(527) if old['tasks'][i]!=new['tasks'][i]]==[524]
 assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'}
 assert new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
 s0,s=old['current_work_snapshot'],new['current_work_snapshot']
 assert {k for k in s0 if k in s and s0[k]!=s[k]}=={'observed_utc','note','status_note','fresh_discovery_current','t3_current_confirmed_running','t3_dispatch_observations'}
 assert set(s)-set(s0)=={'analytic_r150_archive','analytic151_prospective_isolation'}
 assert not set(s0)-set(s)
 assert s['t3_dispatch_observations'][:-1]==s0['t3_dispatch_observations'] and s['t3_last_polled_running']==[]
 for i,n in [(524,'task-status.json'),(527,'r151-dispatch.json')]:
  d=read(O/n)['structuredContent'];assert all(new['tasks'][i][k]==v for k,v in d.items())
 t=new['tasks'][524]
 assert 'parent_archive_pending' not in t and t['parent_disposition']=='PREFREEZE_NO_NOMINEE' and not t['scope_frozen'] and t['nominee'] is None
 assert t['correctness']==t['contribution']=='UNREVIEWED' and not t['accepted'] and t['count_change']==0
 t=new['tasks'][527]
 assert t['providerInstanceId']=='codex' and t['model']=='gpt-6-astra' and {e['id']:e['value'] for e in t['options']}=={'reasoningEffort':'high','serviceTier':'default'}
 assert s['t3_current_confirmed_running']==[new['tasks'][i]['taskId'] for i in [525,526,527]]
 assert s['fresh_discovery_current']==[new['tasks'][i]['output'] for i in [525,526,527]]
 receipt=read(O/'prospective-isolation.json')
 assert receipt['before_analytic151_brief_or_root'] and receipt['no_active_peer_status_body_read_or_steer'] and len(receipt['both_peer_original_initial_briefs'])==2
 for e,i in zip(receipt['both_peer_original_initial_briefs'],[525,526]):
  assert e['brief']==old['tasks'][i]['brief'] and h.sha(B/e['brief'])==e['sha256']==old['tasks'][i]['brief_sha256']
  assert '*analytic*r151*' in (B/e['brief']).read_text()
 text=(B/t['brief']).read_text();assert h.sha(B/t['brief'])==t['brief_sha256']
 marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
 assert text.split(marker)[1]==(B/old['tasks'][524]['brief']).read_text().split(marker)[1]
 assert all(x in text for x in ['*t360s147*','*structural*r156*','*arithmetic*r122*','*structural*r157*','*arithmetic*r123*'])
 journal=P/'frontier/NEW-TEN-2026-10-14.md';assert journal.read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
 assert h.snap(B/'fresh-analytic-discovery-r150')==read(O/'observed-root.json')['root']
 assert all(h.sha(P/e['path'])==e['sha256'] for e in read(O/'replay.json')['stable_named_originals'])
 assert h.sha(O/'assessment.md')==read(O/'intake.json')['assessment_sha256']
 assert all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 allow=read(O/'staging-allowlist.json');files=allow['files'];assert len(files)==len(set(files))==37
 assert {p for p in files if '/private/' in p}=={str((B/'fresh-analytic-discovery-r150'/n).relative_to(P)) for n in allow['private_metadata_only']} and len(allow['private_metadata_only'])==2
 assert not any('/fresh-analytic-discovery-r151/' in p or '/fresh-arithmetic-discovery-r122/' in p or '/fresh-structural-discovery-r156/' in p for p in files)
 assert len([p for p in files if '/fresh-analytic-discovery-r150/' in p])==19
 expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
 if mode=='prestage':
  assert not git('diff','--cached','--name-only')
  assert set(git('diff','--name-only').decode().splitlines())==protected|{prefix+taskpath,prefix+'frontier/NEW-TEN-2026-10-14.md'}
  (O/'integration-validation.json').write_text(json.dumps({'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_head':head,'prestage_index_empty':True,'changed_existing_task_indices':[524],'new_task_indices':[527],'other_tasks_and_snapshot_fields_unchanged':True,'no_pending_archive_marker':True,'journal_prefix_and_sealed_root_unchanged':True,'stable_originals_and_protected_files_unchanged':True,'both_original_peer_briefs_exclude_future151':True,'complete_original_standing_brief_preserved':True,'no_active_peer_status_body_read_or_steer':True,'explicit_allowed_paths':37,'newAccepted':19,'remaining':1,'publication':'STOPPED','mathematical_or_contribution_gate_assigned':False},indent=2)+'\n')
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
 print(json.dumps({'phase':mode,'files':37,'tasks':528,'count':19,'remaining':1,'sealed_root_and_stable_inputs_unchanged':True}))
if __name__=='__main__':main(sys.argv[1])
