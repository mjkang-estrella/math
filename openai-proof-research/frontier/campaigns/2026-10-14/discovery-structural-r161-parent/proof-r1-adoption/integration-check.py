#!/usr/bin/env python3
"""Adopt only T126S161 full correctness PASS; preserve scope and contribution independence."""
import datetime,importlib.util,json,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;C=O.parent;B=C.parent;P=B.parents[2]
spec=importlib.util.spec_from_file_location('replay',O/'replay.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
def read(p):return json.loads(p.read_text())
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
def main(mode):
 base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
 if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
 path=str((B/'tasks.json').relative_to(P));old=json.loads(git('show',head+':'+prefix+path));new=read(B/'tasks.json');assert len(old['tasks'])==545 and len(new['tasks'])==546 and [i for i in range(545) if old['tasks'][i]!=new['tasks'][i]]==[540,543]
 assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'} and new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
 s0,s=old['current_work_snapshot'],new['current_work_snapshot'];assert {k for k in s0 if s0[k]!=s[k]}=={'observed_utc','note','status_note','fresh_discovery_current','t3_current_confirmed_running','t3_dispatch_observations','t126s161_author_intake','t126s161_reviews','arithmetic128_deferred_for_review_capacity'} and set(s)-set(s0)=={'t126s161_correctness_adoption','arithmetic128_prospective_isolation','analytic156_terminal_pending_intake'} and not set(s0)-set(s)
 assert s['t3_dispatch_observations'][:-1]==s0['t3_dispatch_observations'] and s['t3_last_polled_running']==[]
 t=new['tasks'][540];assert t['scope_frozen'] and t['scope_frozen_sha256']==h.SCOPE and t['author_proof_sha256']==h.PROOF and t['correctness']=='PASS' and t['contribution']=='UNREVIEWED' and t['formal']=='NOT_STARTED' and not t['accepted'] and t['count_change']==0 and not t['mathematical_repairs_required']
 t=new['tasks'][543];r=read(O/'task-status.json')['structuredContent'];assert all(t[k]==v for k,v in r.items()) and t['correctness']=='PASS' and not t['mathematical_repairs_required'] and not t['unresolved_objections'] and t['contribution']=='NOT_ASSIGNED' and not t['accepted'] and t['count_change']==0
 t=new['tasks'][545];r=read(O/'r128-dispatch.json')['structuredContent'];assert all(t[k]==v for k,v in r.items()) and t['providerInstanceId']=='codex' and t['model']=='gpt-6-astra' and {e['id']:e['value'] for e in t['options']}=={'reasoningEffort':'high','serviceTier':'default'} and t['status']=='running' and not t['hasPendingChildRuns'] and not t['hasPendingQuestion']
 receipt=read(O/'prospective-isolation.json');assert receipt['before_arithmetic128_brief_or_root'] and receipt['both_original_initial_briefs_exclude_future128'] and receipt['no_active_peer_status_poll_body_read_or_steer'] and len(receipt['active_peer_original_initial_briefs'])==2
 for e,i in zip(receipt['active_peer_original_initial_briefs'],[542,544]):assert e['task_index']==i and e['brief']==old['tasks'][i]['brief'] and h.sha(B/e['brief'])==e['sha256']==old['tasks'][i]['brief_sha256'] and '*arithmetic*r128*' in (B/e['brief']).read_text()
 text=(B/t['brief']).read_text();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';assert h.sha(B/t['brief'])==t['brief_sha256'] and text.split(marker)[1]==(B/old['tasks'][541]['brief']).read_text().split(marker)[1] and len(text.split(marker)[1].encode())==5570 and all(x in text for x in ['*analytic*r156*','*analytic*r157*','*structural*r161*','*structural*r162*','*t126s161*','*t360s147*','contribution review is PENDING'])
 assert s['fresh_discovery_current']==[new['tasks'][545]['output']] and s['t3_current_confirmed_running']==[new['tasks'][j]['taskId'] for j in [544,545]] and s['t126s161_reviews']['correctness']=='PASS' and s['t126s161_reviews']['substantial_contribution']=='PENDING'
 pending=read(O/'analytic156-terminal-status.json')['structuredContent'];assert pending['taskId']==new['tasks'][542]['taskId'] and pending['status']=='completed' and pending['workState']=='result_available' and not pending['hasPendingChildRuns'] and s['analytic156_terminal_pending_intake']['parent_archive_pending']
 assert s['arithmetic128_deferred_for_review_capacity']['resolved_by_arithmetic128_dispatch'] and s['arithmetic128_deferred_for_review_capacity']['arithmetic128_dispatched'] and not s['arithmetic128_deferred_for_review_capacity']['campaign_paused']
 assert h.snap(h.ROOT)==read(O/'observed-root.json')['root'] and h.snap(h.AUTHOR)==read(C/'observed-root.json')['root'] and h.sha(h.AUTHOR/'scope-frozen.md')==h.SCOPE and h.sha(h.AUTHOR/'author-proof.md')==h.PROOF and all(h.sha(P/e['path'])==e['sha256'] for e in read(O/'replay.json')['stable_named_originals']) and h.sha(O/'assessment.md')==read(O/'intake.json')['assessment_sha256']
 assert all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items()) and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
 files=read(O/'staging-allowlist.json')['files'];assert len(files)==len(set(files))==29 and not any('/private/' in p for p in files) and len([p for p in files if '/structural-r161-proof-r1/' in p])==9 and not any('/structural-r161-contribution-r1/' in p or '/fresh-structural-discovery-r161/' in p or '/fresh-arithmetic-discovery-r128/' in p or '/fresh-analytic-discovery-r156/' in p for p in files)
 expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
 if mode=='prestage':
  assert not git('diff','--cached','--name-only') and set(git('diff','--name-only').decode().splitlines())==protected|{prefix+path,prefix+'frontier/NEW-TEN-2026-10-14.md'}
  (O/'integration-validation.json').write_text(json.dumps(dict(observed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),baseline_head=head,changed_existing_task_indices=[540,543],new_task_indices=[545],other_tasks_unchanged=True,full_correctness_only_adopted=True,no_repairs_or_scope_change=True,contribution_pending_and_dispatch_unchanged=True,complete_standing_brief_preserved=True,initial_reciprocal_guards_checked_before_new_brief=True,analytic156_delivered_terminal_after_preparation_saved=True,sealed_author_review_roots_originals_journal_prefix_protected_files_unchanged=True,explicit_allowed_paths=29,newAccepted=19,remaining=1,publication='STOPPED'),indent=2)+'\n')
 else:
  if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
  else:
   assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
  assert actual==expected,(actual-expected,expected-actual);assert all(git('show',obj+prefix+p)==(P/p).read_bytes() for p in files) and set(git('diff','--name-only').decode().splitlines())==protected
 print(json.dumps(dict(phase=mode,files=29,tasks=546,count=19,remaining=1,full_correctness='PASS',contribution='PENDING',frozen_scope_and_proof_unchanged=True)))
if __name__=='__main__':main(sys.argv[1])
