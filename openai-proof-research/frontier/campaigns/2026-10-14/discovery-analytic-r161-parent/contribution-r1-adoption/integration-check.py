#!/usr/bin/env python3
"""Adopt full-scope TECHNICAL, discharge its correctness condition, retain zero count."""
import datetime,importlib.util,json,stat,subprocess,sys
from pathlib import Path
O=Path(__file__).resolve().parent;A=O.parent;B=A.parent;P=B.parents[2]
sp=importlib.util.spec_from_file_location('replay',O/'replay.py');h=importlib.util.module_from_spec(sp);sp.loader.exec_module(h)
def read(p):return json.loads(p.read_text())
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
def main(mode):
 base=read(O/'integration-baseline.json');head=base['head'];prefix=git('rev-parse','--show-prefix').decode().strip();assert prefix=='openai-proof-research/'
 if mode!='committed':assert git('rev-parse','HEAD').decode().strip()==head
 path=str((B/'tasks.json').relative_to(P));old=json.loads(git('show',head+':'+prefix+path));new=read(B/'tasks.json');assert len(old['tasks'])==len(new['tasks'])==564 and [i for i in range(564) if old['tasks'][i]!=new['tasks'][i]]==[559,563]
 assert {k for k in old if old[k]!=new[k]}=={'tasks','last_parent_progress','current_work_snapshot'} and new['newAccepted']==19 and new['remaining']==1 and new['target']==20 and new['latestAcceptance']==old['latestAcceptance']=='R041'
 t0,t=old['tasks'][559],new['tasks'][559];assert {k for k in t0 if t0[k]!=t[k]}=={'contribution','independent_contribution_status','parent_disposition','formalization','manuscript','local_release'} and set(t)-set(t0)=={'contribution_adoption','contribution_correctness_condition'} and not set(t0)-set(t)
 assert t['correctness']=='PASS' and t['contribution']=='TECHNICAL' and t['parent_disposition']=='FULL_SCOPE_PASS_TECHNICAL_NO_COUNT' and not t['accepted'] and t['count_change']==0 and all(t[k]=='CLOSED_SUBSTANTIALITY_GATE_NOT_MET' for k in ['formalization','manuscript','local_release'])
 s0,s=old['current_work_snapshot'],new['current_work_snapshot'];assert {k for k in s0 if s0[k]!=s[k]}=={'observed_utc','note','status_note','t3_current_confirmed_running','analytic_r161_intake','analytic_r161_reviews'} and set(s)-set(s0)=={'analytic_r161_contribution_adoption'} and not set(s0)-set(s)
 assert s['t3_dispatch_observations']==s0['t3_dispatch_observations'] and not s['t3_last_polled_running'] and not s['fresh_discovery_current'] and not s['pending_terminal_intakes_20261021'] and not s['t3_current_confirmed_running'] and s['analytic_r161_reviews']['correctness']==s0['analytic_r161_reviews']['correctness']
 t=new['tasks'][563];raw=read(O/'task-status.json')['structuredContent'];assert all(t[k]==v for k,v in raw.items()) and t['status']=='completed' and t['workState']=='result_available' and not t['hasPendingChildRuns'] and not t['hasPendingQuestion'] and t['review_verdict']=='TECHNICAL' and t['parent_adopted_contribution'] and t['entire_unchanged_frozen_scope'] and not t['accepted'] and t['count_change']==0
 adopt=read(O/'adoption.json');correct=read(A/'proof-r1-adoption/adoption.json');assert adopt['verdict']=='TECHNICAL' and adopt['gate']=='substantial-contribution' and adopt['entire_unchanged_frozen_scope'] and adopt['correctness']=='PASS' and correct['verdict']=='PASS' and correct['entire_unchanged_frozen_scope'] and adopt['correctness_condition']==t['correctness_condition']=='DISCHARGED_BY_INDEPENDENT_ENTIRE_UNCHANGED_FROZEN_SCOPE_PASS' and adopt['frozen_scope_sha256']==correct['frozen_scope_sha256'] and adopt['author_proof_sha256']==correct['author_proof_sha256'] and not adopt['accepted'] and adopt['count_change']==0
 author=B/'fresh-analytic-discovery-r161';assert h.sha(author/'FROZEN-STATEMENT.md')==adopt['frozen_scope_sha256']==t['frozen_scope_sha256'] and h.sha(author/'AUTHOR-PROOF.md')==adopt['author_proof_sha256']==t['author_proof_sha256'] and h.snap(author)==read(A/'observed-root.json')['root'] and h.sha(A/'assessment.md')==read(A/'intake.json')['assessment_sha256']
 assert h.snap(B/'analytic-r161-proof-r1')==read(A/'proof-r1-adoption/observed-root.json')['root'] and h.sha(A/'proof-r1-adoption/assessment.md')==correct['assessment_sha256']
 root=B/'analytic-r161-contribution-r1';observed=read(O/'observed-root.json');assert h.snap(root)==observed['root'] and stat.S_IMODE(root.stat().st_mode)==observed['root_mode'] and all(h.sha(P/e['path'])==e['sha256'] and stat.S_IMODE((P/e['path']).stat().st_mode)==e['mode'] for e in read(O/'replay.json')['stable_named_originals']) and h.sha(O/'assessment.md')==adopt['assessment_sha256']
 assert all(h.sha(P/p)==v for p,v in base['protected_unrelated_sha256'].items()) and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes().startswith(git('show',head+':'+prefix+'frontier/NEW-TEN-2026-10-14.md'))
 files=read(O/'staging-allowlist.json')['files'];assert len(files)==len(set(files))==19 and len([p for p in files if '/analytic-r161-contribution-r1/' in p])==9 and not any('/private/' in p or '/analytic-r161-proof-r1/' in p or '/fresh-analytic-discovery-r161/' in p or p.endswith(('/observed-root.json','/replay.json')) for p in files)
 expected={prefix+p for p in files};protected={prefix+p for p in base['protected_unrelated_sha256']}
 if mode=='prestage':
  assert not git('diff','--cached','--name-only') and set(git('diff','--name-only').decode().splitlines())==protected|{prefix+path,prefix+'frontier/NEW-TEN-2026-10-14.md'}
  (O/'integration-validation.json').write_text(json.dumps({'observed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline_head':head,'changed_existing_task_indices':[559,563],'new_task_indices':[],'other_tasks_and_snapshot_fields_unchanged':True,'entire_unchanged_frozen_statement_and_proof':True,'full_scope_PASS_TECHNICAL_zero_count':True,'correctness_condition_discharged_by_independent_identical_scope_PASS':True,'downstream_gates_closed_for_substantiality':True,'author_and_both_review_roots_and_old_assessments_unchanged':True,'protected_identity_inventory_replay_local_unstaged':True,'journal_prefix_and_protected_unrelated_files_unchanged':True,'explicit_allowed_paths':19,'newAccepted':19,'remaining':1,'publication':'STOPPED','acceptance_assigned':False},indent=2)+'\n')
 else:
  if mode=='staged':actual=set(git('diff','--cached','--name-only').decode().splitlines());obj=':';subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
  else:
   assert mode=='committed' and not git('diff','--cached','--name-only') and git('rev-parse','HEAD^').decode().strip()==head;actual=set(git('diff-tree','--no-commit-id','--name-only','-r','HEAD').decode().splitlines());obj='HEAD:'
  assert actual==expected,(actual-expected,expected-actual);assert all(git('show',obj+prefix+p)==(P/p).read_bytes() for p in files) and set(git('diff','--name-only').decode().splitlines())==protected
 print(json.dumps({'phase':mode,'files':19,'tasks':564,'correctness':'PASS','contribution':'TECHNICAL','condition':'DISCHARGED','count':19,'remaining':1,'sealed_roots_unchanged':True}))
if __name__=='__main__':main(sys.argv[1])
