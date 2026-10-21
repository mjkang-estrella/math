#!/usr/bin/env python3
"""Structural166 archive and Structural167 initial-prompt integration guard."""
import datetime,importlib.util,json,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2]
spec=importlib.util.spec_from_file_location('replay',O/'replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
def read(p):return json.loads(p.read_text())
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
def main(mode):
 base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
 if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
 path=str((B/'tasks.json').relative_to(P));old=json.loads(git('show',head+':'+prefix+path));new=read(B/'tasks.json');assert len(old['tasks'])==560 and len(new['tasks'])==561 and [i for i in range(560) if old['tasks'][i]!=new['tasks'][i]]==[558]
 assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'} and new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
 s0,s=old['current_work_snapshot'],new['current_work_snapshot'];assert {k for k in s0 if s0[k]!=s[k]}=={'observed_utc','note','status_note','fresh_discovery_current','t3_current_confirmed_running','t3_dispatch_observations','pending_terminal_intakes_20261021'} and set(s)-set(s0)=={'structural_r166_archive','structural167_prospective_isolation'} and not set(s0)-set(s)
 assert s['t3_dispatch_observations'][:-1]==s0['t3_dispatch_observations'] and s['t3_last_polled_running']==[]
 for i,n in [(558,'task-status.json'),(560,'r167-dispatch.json')]:
  raw=read(O/n)['structuredContent'];assert all(new['tasks'][i][k]==v for k,v in raw.items())
 t=new['tasks'][558];assert t['parent_disposition']=='PREFREEZE_NO_NOMINEE' and t['correctness']==t['contribution']=='UNREVIEWED' and not t['scope_frozen'] and t['nominee'] is None and not t['accepted'] and t['count_change']==0
 t=new['tasks'][560];assert t['providerInstanceId']=='codex' and t['model']=='gpt-6-astra' and {e['id']:e['value'] for e in t['options']}=={'reasoningEffort':'high','serviceTier':'default'} and t['status']=='running' and not t['hasPendingChildRuns'] and not t['hasPendingQuestion']
 assert s['fresh_discovery_current']==[new['tasks'][j]['output'] for j in [559,560]] and s['t3_current_confirmed_running']==[new['tasks'][j]['taskId'] for j in [559,560]]
 assert not new['tasks'][558]['pending_parent_intake'] and [e['task_index'] for e in s['pending_terminal_intakes_20261021']]==[557] and s['pending_terminal_intakes_20261021']==[e for e in s0['pending_terminal_intakes_20261021'] if e['task_index']==557]
 receipt=read(O/'prospective-isolation.json');assert receipt['before_structural167_brief_or_root'] and receipt['all_existing_original_initial_briefs_exclude_future167'] and receipt['no_active_peer_body_read_poll_or_steer'] and len(receipt['existing_active_peer_original_initial_briefs'])==1
 for e,i in zip(receipt['existing_active_peer_original_initial_briefs'],[559]):
  peer=old['tasks'][i];assert e['task_index']==i and e['taskId']==peer['taskId'] and e['brief']==peer['brief'] and h.sha(B/e['brief'])==e['sha256']==peer['brief_sha256'];assert '*structural*r167*' in (B/e['brief']).read_text()
 text=(B/t['brief']).read_text();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';assert h.sha(B/t['brief'])==t['brief_sha256'] and text.split(marker)[1]==(B/old['tasks'][558]['brief']).read_text().split(marker)[1] and len(text.split(marker)[1].encode())==5570;assert all(x in text for x in ['ONE existing active peer','*analytic*r161*','*arithmetic*r132*','*arithmetic*r133*','*analytic*r162*','*t360s147*'])
 assert h.snap(B/'fresh-structural-discovery-r166')==read(O/'observed-root.json')['root'] and all(h.sha(P/e['path'])==e['sha256'] for e in read(O/'replay.json')['stable_named_originals']) and h.sha(O/'assessment.md')==read(O/'intake.json')['assessment_sha256']
 assert all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items()) and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
 files=read(O/'staging-allowlist.json')['files'];assert len(files)==len(set(files))==25 and not any('/private/' in p for p in files) and len([p for p in files if '/fresh-structural-discovery-r166/' in p])==9;assert not any('/fresh-structural-discovery-r167/' in p or '/fresh-analytic-discovery-r161/' in p or '/fresh-arithmetic-discovery-r132/' in p for p in files)
 expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
 if mode=='prestage':
  assert not git('diff','--cached','--name-only') and set(git('diff','--name-only').decode().splitlines())==protected|{prefix+path,prefix+'frontier/NEW-TEN-2026-10-14.md'}
  (O/'integration-validation.json').write_text(json.dumps(dict(observed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),baseline_head=head,changed_existing_task_indices=[558],new_task_indices=[560],other_tasks_and_snapshot_fields_unchanged=True,both_original_initial_peer_briefs_exclude167=True,complete_original_standing_brief_preserved=True,sealed_root_stable_originals_journal_prefix_protected_files_unchanged=True,explicit_allowed_paths=25,newAccepted=19,remaining=1,publication='STOPPED',mathematical_gate_assigned=False),indent=2)+'\n')
 else:
  if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
  else:
   assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
  assert actual==expected,(actual-expected,expected-actual);assert all(git('show',obj+prefix+p)==(P/p).read_bytes() for p in files) and set(git('diff','--name-only').decode().splitlines())==protected
 print(json.dumps(dict(phase=mode,files=25,tasks=561,count=19,remaining=1,sealed_root_and_stable_inputs_unchanged=True)))
if __name__=='__main__':main(sys.argv[1])
