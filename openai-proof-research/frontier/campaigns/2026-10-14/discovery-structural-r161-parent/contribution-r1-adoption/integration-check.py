#!/usr/bin/env python3
"""Adopt full TECHNICAL with identical full correctness PASS; zero count."""
import datetime,importlib.util,json,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;C=O.parent;B=C.parent;P=B.parents[2]
spec=importlib.util.spec_from_file_location('replay',O/'replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
def read(p):return json.loads(p.read_text())
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
def main(mode):
 base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
 if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
 path=str((B/'tasks.json').relative_to(P));old=json.loads(git('show',head+':'+prefix+path));new=read(B/'tasks.json');assert len(old['tasks'])==546 and len(new['tasks'])==547 and [i for i in range(546) if old['tasks'][i]!=new['tasks'][i]]==[540,544]
 assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'} and new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
 s0,s=old['current_work_snapshot'],new['current_work_snapshot'];assert {k for k in s0 if s0[k]!=s[k]}=={'observed_utc','note','status_note','fresh_discovery_current','t3_current_confirmed_running','t3_dispatch_observations','t126s161_author_intake','t126s161_reviews'} and set(s)-set(s0)=={'t126s161_contribution_adoption','structural162_prospective_isolation'} and not set(s0)-set(s)
 assert s['t3_dispatch_observations'][:-1]==s0['t3_dispatch_observations'] and s['t3_last_polled_running']==[]
 t=new['tasks'][540];assert t['scope_frozen'] and t['scope_frozen_sha256']==h.SCOPE and t['author_proof_sha256']==h.PROOF and t['correctness']=='PASS' and t['contribution']=='TECHNICAL' and t['correctness_condition_discharged'] and all(t[k]=='CLOSED_TECHNICAL' for k in ['formal','manuscript','release']) and not t['accepted'] and t['count_change']==0
 assert new['tasks'][543]==old['tasks'][543] and new['tasks'][543]['correctness']=='PASS' and not new['tasks'][543]['mathematical_repairs_required']
 t=new['tasks'][544];r=read(O/'task-status.json')['structuredContent'];assert all(t[k]==v for k,v in r.items()) and t['contribution']=='TECHNICAL' and t['correctness']=='NOT_ASSIGNED' and t['correctness_condition_discharged'] and not t['accepted'] and t['count_change']==0
 t=new['tasks'][546];r=read(O/'r162-dispatch.json')['structuredContent'];assert all(t[k]==v for k,v in r.items()) and t['providerInstanceId']=='codex' and t['model']=='gpt-6-astra' and {e['id']:e['value'] for e in t['options']}=={'reasoningEffort':'high','serviceTier':'default'} and t['status']=='running' and not t['hasPendingChildRuns'] and not t['hasPendingQuestion']
 receipt=read(O/'prospective-isolation.json');assert receipt['before_structural162_brief_or_root'] and receipt['only_active_peer']=='Arithmetic128' and receipt['no_active_peer_status_poll_body_read_or_steer'] and len(receipt['active_peer_original_initial_briefs'])==1
 e=receipt['active_peer_original_initial_briefs'][0];assert e['task_index']==545 and e['brief']==old['tasks'][545]['brief'] and h.sha(B/e['brief'])==e['sha256']==old['tasks'][545]['brief_sha256'] and '*structural*r162*' in (B/e['brief']).read_text()
 text=(B/t['brief']).read_text();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';assert h.sha(B/t['brief'])==t['brief_sha256'] and text.split(marker)[1]==(B/old['tasks'][540]['brief']).read_text().split(marker)[1] and len(text.split(marker)[1].encode())==5570 and all(x in text for x in ['ONLY active peer','*arithmetic*r128*','*arithmetic*r129*','*analytic*r157*','*analytic*r158*','*structural*r161*','*t126s161*','*t360s147*','correctnesscondition DISCHARGED'])
 assert not (B/'fresh-analytic-discovery-r157').exists() and not (B/'expanded-target-2026-10-17/fresh-analytic-r157-brief.txt').exists()
 assert s['fresh_discovery_current']==[new['tasks'][j]['output'] for j in [545,546]] and s['t3_current_confirmed_running']==[new['tasks'][j]['taskId'] for j in [545,546]] and s['t126s161_reviews']['correctness']=='PASS' and s['t126s161_reviews']['substantial_contribution']=='TECHNICAL' and s['t126s161_reviews']['correctness_condition_discharged']
 assert h.snap(h.ROOT)==read(O/'observed-root.json')['root'] and h.snap(h.AUTHOR)==read(C/'observed-root.json')['root'] and h.snap(B/'structural-r161-proof-r1')==read(C/'proof-r1-adoption/observed-root.json')['root'] and h.sha(h.AUTHOR/'scope-frozen.md')==h.SCOPE and h.sha(h.AUTHOR/'author-proof.md')==h.PROOF and all(h.sha(P/e['path'])==e['sha256'] for e in read(O/'replay.json')['stable_named_originals']) and h.sha(O/'assessment.md')==read(O/'intake.json')['assessment_sha256']
 assert all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items()) and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
 files=read(O/'staging-allowlist.json')['files'];assert len(files)==len(set(files))==27 and not any('/private/' in p for p in files) and len([p for p in files if '/structural-r161-contribution-r1/' in p])==9 and not any('/structural-r161-proof-r1/' in p or '/fresh-structural-discovery-r161/' in p or '/fresh-structural-discovery-r162/' in p or '/fresh-arithmetic-discovery-r128/' in p for p in files)
 expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
 if mode=='prestage':
  assert not git('diff','--cached','--name-only') and set(git('diff','--name-only').decode().splitlines())==protected|{prefix+path,prefix+'frontier/NEW-TEN-2026-10-14.md'}
  (O/'integration-validation.json').write_text(json.dumps(dict(observed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),baseline_head=head,changed_existing_task_indices=[540,544],new_task_indices=[546],other_tasks_unchanged=True,full_scope_PASS_TECHNICAL=True,correctness_condition_discharged=True,downstream_closed_zero_count=True,no_scope_proof_or_review_change=True,complete_standing_brief_preserved=True,only_existing_peer_initial_guard_checked_before_new_brief=True,analytic157_still_not_created=True,sealed_roots_originals_journal_prefix_protected_files_unchanged=True,explicit_allowed_paths=27,newAccepted=19,remaining=1,publication='STOPPED'),indent=2)+'\n')
 else:
  if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
  else:
   assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
  assert actual==expected,(actual-expected,expected-actual);assert all(git('show',obj+prefix+p)==(P/p).read_bytes() for p in files) and set(git('diff','--name-only').decode().splitlines())==protected
 print(json.dumps(dict(phase=mode,files=27,tasks=547,count=19,remaining=1,full_scope='PASS/TECHNICAL',correctness_condition_discharged=True)))
if __name__=='__main__':main(sys.argv[1])
