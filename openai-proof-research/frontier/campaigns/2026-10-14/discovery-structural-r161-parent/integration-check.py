#!/usr/bin/env python3
"""Preserve T126S161 frozen scope and independently dispatched review identities."""
import datetime,importlib.util,json,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2]
spec=importlib.util.spec_from_file_location('replay',O/'replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
def read(p):return json.loads(p.read_text())
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
def main(mode):
 base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
 if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
 path=str((B/'tasks.json').relative_to(P));old=json.loads(git('show',head+':'+prefix+path));new=read(B/'tasks.json');assert len(old['tasks'])==543 and len(new['tasks'])==545 and [i for i in range(543) if old['tasks'][i]!=new['tasks'][i]]==[540]
 assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'} and new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
 s0,s=old['current_work_snapshot'],new['current_work_snapshot'];assert {k for k in s0 if s0[k]!=s[k]}=={'observed_utc','note','status_note','fresh_discovery_current','t3_current_confirmed_running','t3_dispatch_observations'} and set(s)-set(s0)=={'t126s161_author_intake','t126s161_reviews','arithmetic127_terminal_pending_intake'} and not set(s0)-set(s)
 assert s['t3_dispatch_observations'][:-2]==s0['t3_dispatch_observations'] and s['t3_last_polled_running']==[]
 t=new['tasks'][540];raw=read(O/'task-status.json')['structuredContent'];assert all(t[k]==v for k,v in raw.items());assert t['parent_disposition']=='FULL_AUTHOR_PROOF_NOMINEE_REVIEW_PENDING' and t['nominee']=='T126S161' and t['scope_frozen'] and t['scope_frozen_sha256']==h.SCOPE and t['author_proof_sha256']==h.PROOF and t['correctness']==t['contribution']=='UNREVIEWED' and t['formal']=='NOT_STARTED' and not t['accepted'] and t['count_change']==0
 for i,name,gate in [(543,'proof','correctness'),(544,'contribution','substantial_contribution')]:
  t=new['tasks'][i];r=read(O/f'{name}-r1-dispatch.json')['structuredContent'];assert all(t[k]==v for k,v in r.items()) and t['gate']==gate and t['nominee']=='T126S161' and t['providerInstanceId']=='codex' and t['model']=='gpt-6-astra' and {e['id']:e['value'] for e in t['options']}=={'reasoningEffort':'high','serviceTier':'default'} and t['status']=='running' and not t['hasPendingChildRuns'] and not t['hasPendingQuestion'] and not t['accepted'] and t['count_change']==0
  text=(B/t['brief']).read_text();assert h.sha(B/t['brief'])==t['brief_sha256'] and text.split('--- ENTIRE UNCHANGED FROZEN STATEMENT ---\n')[1]==(B/'fresh-structural-discovery-r161/scope-frozen.md').read_text();assert all(x in text for x in ['*analytic*r156*','*arithmetic*r127*','*arithmetic*r128*','all *t360s147*'])
 assert '*structural*r161*contribution*' in (B/new['tasks'][543]['brief']).read_text() and '*structural*r161*proof-r*' in (B/new['tasks'][544]['brief']).read_text()
 assert s['fresh_discovery_current']==[new['tasks'][542]['output']] and s['t3_current_confirmed_running']==[new['tasks'][j]['taskId'] for j in [542,543,544]]
 pending=read(O/'arithmetic127-terminal-status.json')['structuredContent'];assert pending['taskId']==new['tasks'][541]['taskId'] and pending['status']=='completed' and pending['workState']=='result_available' and not pending['hasPendingChildRuns'] and s['arithmetic127_terminal_pending_intake']['parent_archive_pending'] and not s['arithmetic127_terminal_pending_intake']['new_arithmetic128_dispatched']
 isolation=read(O/'review-isolation.json');assert isolation['initial_review_briefs_mutually_exclude_siblings'] and len(isolation['existing_discovery_initial_guards'])==2
 for e,i in zip(isolation['existing_discovery_initial_guards'],[541,542]):assert e['task_index']==i and e['brief']==old['tasks'][i]['brief'] and h.sha(B/e['brief'])==e['sha256']==old['tasks'][i]['brief_sha256'] and '*structural*r161*' in (B/e['brief']).read_text()
 assert h.snap(B/'fresh-structural-discovery-r161')==read(O/'observed-root.json')['root'] and h.sha(B/'fresh-structural-discovery-r161/scope-frozen.md')==h.SCOPE and h.sha(B/'fresh-structural-discovery-r161/author-proof.md')==h.PROOF and all(h.sha(P/e['path'])==e['sha256'] for e in read(O/'replay.json')['stable_named_originals']) and h.sha(O/'assessment.md')==read(O/'intake.json')['assessment_sha256']
 assert all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items()) and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
 files=read(O/'staging-allowlist.json')['files'];assert len(files)==len(set(files))==43 and not any('/private/' in p for p in files) and len([p for p in files if '/fresh-structural-discovery-r161/' in p])==21 and not any('/structural-r161-proof-r1/' in p or '/structural-r161-contribution-r1/' in p or '/fresh-analytic-discovery-r156/' in p or '/fresh-arithmetic-discovery-r127/' in p for p in files)
 expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
 if mode=='prestage':
  assert not git('diff','--cached','--name-only') and set(git('diff','--name-only').decode().splitlines())==protected|{prefix+path,prefix+'frontier/NEW-TEN-2026-10-14.md'}
  (O/'integration-validation.json').write_text(json.dumps(dict(observed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),baseline_head=head,changed_existing_task_indices=[540],new_task_indices=[543,544],other_tasks_and_snapshot_fields_unchanged=True,full_frozen_statement_and_author_proof_unchanged=True,independent_actual_review_dispatches_with_requested_options=True,no_mathematical_gate_or_count=True,arithmetic127_delivered_terminal_saved_pending_archive=True,sealed_root_stable_originals_journal_prefix_protected_files_unchanged=True,explicit_allowed_paths=43,newAccepted=19,remaining=1,publication='STOPPED'),indent=2)+'\n')
 else:
  if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
  else:
   assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
  assert actual==expected,(actual-expected,expected-actual);assert all(git('show',obj+prefix+p)==(P/p).read_bytes() for p in files) and set(git('diff','--name-only').decode().splitlines())==protected
 print(json.dumps(dict(phase=mode,files=43,tasks=545,count=19,remaining=1,full_frozen_nominee_unchanged=True,independent_reviews_dispatched=2)))
if __name__=='__main__':main(sys.argv[1])
