#!/usr/bin/env python3
"""Exact semantic/staging check for this two-role review adoption."""
import datetime,importlib.util,json,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parents[1];P=B.parents[2]
spec=importlib.util.spec_from_file_location('helpers',O/'replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
def read(p):return json.loads(p.read_text())
def git(*args):return subprocess.check_output(['git',*args],cwd=P)
def main(mode):
 base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
 if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
 taskpath=str((B/'tasks.json').relative_to(P));old=json.loads(git('show',head+':'+prefix+taskpath));new=read(B/'tasks.json');assert len(old['tasks'])==len(new['tasks'])==518
 assert [i for i in range(518) if old['tasks'][i]!=new['tasks'][i]]==[512,515,516]
 assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'}
 assert new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
 s0,s=old['current_work_snapshot'],new['current_work_snapshot'];assert {k for k in s0 if k in s and s0[k]!=s[k]}=={'observed_utc','note','status_note','t3_current_confirmed_running','t360s147_reviews'}
 assert set(s)-set(s0)=={'t360s147_review_adoption'} and not set(s0)-set(s)
 assert s['t3_dispatch_observations']==s0['t3_dispatch_observations'] and s['t3_last_polled_running']==[]
 for i,role,gate in [(515,'proof','PASS'),(516,'contribution','TECHNICAL')]:
  d=read(O/(role+'-task-status.json'))['structuredContent'];assert all(new['tasks'][i][k]==v for k,v in d.items());assert new['tasks'][i]['parent_adopted_gate']==gate and new['tasks'][i]['full_frozen_scope'] and not new['tasks'][i]['mathematical_repairs_required']
 assert new['tasks'][512]['correctness']=='PASS' and new['tasks'][512]['contribution']=='TECHNICAL' and new['tasks'][512]['scope_frozen'] and not new['tasks'][512]['downstream_stages_open']
 assert new['tasks'][516]['correctness_condition_discharged'] and new['tasks'][516]['condition_discharged_by']==new['tasks'][515]['taskId']
 assert all(not new['tasks'][i]['accepted'] and new['tasks'][i]['count_change']==0 for i in [512,515,516])
 assert s['t3_current_confirmed_running']==[new['tasks'][517]['taskId']] and s['fresh_discovery_current']==s0['fresh_discovery_current']==[new['tasks'][517]['output']]
 assert (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
 states=read(O/'observed-roots.json');assert h.snap(B/'fresh-analytic-discovery-r147')==states['author']
 for role in ['proof','contribution']:assert h.snap(B/('t360s147-'+role+'-r1'))==states[role]
 assert all(h.sha(P/e['path'])==e['sha256'] for e in read(O/'replay.json')['stable_named_originals'])
 assert all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items())
 assert h.sha(O/'disposition.md')==s['t360s147_review_adoption']['disposition_sha256']
 allow=read(O/'staging-allowlist.json');files=allow['files'];assert len(files)==len(set(files))==45 and {p for p in files if '/private/' in p}==set(allow['private_metadata_only'])
 assert not any('/private/source/' in p or '/private/history/' in p or '/private/incoming/' in p or '/private/controls/' in p or '/fresh-arithmetic-discovery-r119/' in p for p in files)
 expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
 if mode=='prestage':
  assert not git('diff','--cached','--name-only') and set(git('diff','--name-only').decode().splitlines())==protected|{prefix+taskpath,prefix+'frontier/NEW-TEN-2026-10-14.md'}
  (O/'integration-validation.json').write_text(json.dumps({'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_head':head,'prestage_index_empty':True,'changed_existing_task_indices':[512,515,516],'new_task_indices':[],'other_tasks_and_snapshot_fields_unchanged':True,'all_three_actual_roots_unchanged':True,'all_selected_originals_and_protected_files_unchanged':True,'journal_prefix_preserved':True,'correctness':'PASS','contribution':'TECHNICAL','correctness_condition_discharged':True,'full_unchanged_scope':True,'explicit_paths':45,'accepted':False,'count_change':0,'newAccepted':19,'remaining':1,'publication':'STOPPED'},indent=2)+'\n')
 else:
  if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
  else:
   assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
  assert actual==expected,(actual-expected,expected-actual)
  assert all(git('show',obj+prefix+p)==(P/p).read_bytes() for p in files)
  assert set(git('diff','--name-only').decode().splitlines())==protected
 print(json.dumps({'phase':mode,'files':45,'tasks':518,'correctness':'PASS','contribution':'TECHNICAL','count':19,'remaining':1,'immutable_roots_unchanged':True}))
if __name__=='__main__':main(sys.argv[1])
