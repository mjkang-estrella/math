#!/usr/bin/env python3
"""Arithmetic128 archive and Arithmetic129 initial-prompt integration guard."""
import datetime,importlib.util,json,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2]
spec=importlib.util.spec_from_file_location('replay',O/'replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
def read(p):return json.loads(p.read_text())
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
def main(mode):
 base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
 if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
 path=str((B/'tasks.json').relative_to(P));old=json.loads(git('show',head+':'+prefix+path));new=read(B/'tasks.json');assert len(old['tasks'])==548 and len(new['tasks'])==549 and [i for i in range(548) if old['tasks'][i]!=new['tasks'][i]]==[545]
 assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'} and new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
 s0,s=old['current_work_snapshot'],new['current_work_snapshot'];assert {k for k in s0 if s0[k]!=s[k]}=={'observed_utc','note','status_note','fresh_discovery_current','t3_current_confirmed_running','t3_dispatch_observations','arithmetic128_terminal_pending_intake'} and set(s)-set(s0)=={'arithmetic_r128_archive','arithmetic129_prospective_isolation'} and not set(s0)-set(s)
 assert s['t3_dispatch_observations'][:-1]==s0['t3_dispatch_observations'] and s['t3_last_polled_running']==[]
 for i,n in [(545,'task-status.json'),(548,'r129-dispatch.json')]:
  raw=read(O/n)['structuredContent'];assert all(new['tasks'][i][k]==v for k,v in raw.items())
 t=new['tasks'][545];assert t['parent_disposition']=='PREFREEZE_NO_NOMINEE' and t['correctness']==t['contribution']=='UNREVIEWED' and not t['scope_frozen'] and t['nominee'] is None and not t['accepted'] and t['count_change']==0
 t=new['tasks'][548];assert t['providerInstanceId']=='codex' and t['model']=='gpt-6-astra' and {e['id']:e['value'] for e in t['options']}=={'reasoningEffort':'high','serviceTier':'default'} and t['status']=='running' and not t['hasPendingChildRuns'] and not t['hasPendingQuestion']
 assert s['fresh_discovery_current']==[new['tasks'][j]['output'] for j in [547,548]] and s['t3_current_confirmed_running']==[new['tasks'][j]['taskId'] for j in [547,548]]
 receipt=read(O/'prospective-isolation.json');assert receipt['before_arithmetic129_brief_or_root'] and receipt['all_existing_peer_initial_briefs_exclude_future129'] and receipt['no_active_peer_body_read_poll_or_steer'] and len(receipt['existing_active_peer_original_initial_briefs'])==1
 for e,i in zip(receipt['existing_active_peer_original_initial_briefs'],[547]):
  peer=old['tasks'][i];assert e['task_index']==i and e['taskId']==peer['taskId'] and e['brief']==peer['brief'] and h.sha(B/e['brief'])==e['sha256']==peer['brief_sha256'];assert '*arithmetic*r129*' in (B/e['brief']).read_text()
 text=(B/t['brief']).read_text();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';assert h.sha(B/t['brief'])==t['brief_sha256'] and text.split(marker)[1]==(B/old['tasks'][545]['brief']).read_text().split(marker)[1] and len(text.split(marker)[1].encode())==5570;assert all(x in text for x in ['ONLY existing active peer','*analytic*r157*','*analytic*r158*','*structural*r163*','*structural*r164*','*t126s161*','TECHNICAL','*t360s147*'])
 assert h.snap(B/'fresh-arithmetic-discovery-r128')==read(O/'observed-root.json')['root'] and all(h.sha(P/e['path'])==e['sha256'] for e in read(O/'replay.json')['stable_named_originals']) and h.sha(O/'assessment.md')==read(O/'intake.json')['assessment_sha256']
 assert all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items()) and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
 files=read(O/'staging-allowlist.json')['files'];assert len(files)==len(set(files))==27 and not any('/private/' in p for p in files) and len([p for p in files if '/fresh-arithmetic-discovery-r128/' in p])==10;assert not any('/fresh-arithmetic-discovery-r129/' in p or '/fresh-analytic-discovery-r157/' in p or '/fresh-structural-discovery-r161/' in p for p in files)
 expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
 if mode=='prestage':
  assert not git('diff','--cached','--name-only') and set(git('diff','--name-only').decode().splitlines())==protected|{prefix+path,prefix+'frontier/NEW-TEN-2026-10-14.md'}
  (O/'integration-validation.json').write_text(json.dumps(dict(observed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),baseline_head=head,changed_existing_task_indices=[545],new_task_indices=[548],other_tasks_and_snapshot_fields_unchanged=True,sole_existing_peer_initial_brief_excludes129=True,complete_original_standing_brief_preserved=True,sealed_root_stable_originals_journal_prefix_protected_files_unchanged=True,explicit_allowed_paths=27,newAccepted=19,remaining=1,publication='STOPPED',mathematical_gate_assigned=False),indent=2)+'\n')
 else:
  if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
  else:
   assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
  assert actual==expected,(actual-expected,expected-actual);assert all(git('show',obj+prefix+p)==(P/p).read_bytes() for p in files) and set(git('diff','--name-only').decode().splitlines())==protected
 print(json.dumps(dict(phase=mode,files=27,tasks=549,count=19,remaining=1,sealed_root_and_stable_inputs_unchanged=True)))
if __name__=='__main__':main(sys.argv[1])
