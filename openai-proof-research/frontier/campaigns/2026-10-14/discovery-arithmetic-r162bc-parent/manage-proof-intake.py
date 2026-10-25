#!/usr/bin/env python3
"""CAS adopt one full correctness PASS; preserve pending contribution and count19."""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
TP='frontier/campaigns/2026-10-14/tasks.json';JP='frontier/NEW-TEN-2026-10-14.md'
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def snapshot(root):
 out={}
 for f in root.rglob('*'):
  assert not f.is_symlink()
  if f.is_file():
   a=f.read_bytes();out[f.relative_to(root).as_posix()]=dict(bytes=len(a),sha256=sha(a),mode=f.stat().st_mode)
 return out
assert not git('diff','--cached','--name-only').strip()
head=git('rev-parse','HEAD').decode().strip();raw_t=git('show',head+':openai-proof-research/'+TP);raw_j=git('show',head+':openai-proof-research/'+JP)
assert (P/TP).read_bytes()==raw_t and (P/JP).read_bytes()==raw_j,'Concurrent uncommitted coordination; no overwrite.'
old=json.loads(raw_t);new=copy.deepcopy(old);baseline=json.loads((D/'proof-intake-baseline.json').read_text())
assert old['newAccepted']==19 and old['target']==20 and old['latestAcceptance']=='R041'
author=next(i for i,x in enumerate(old['tasks']) if x.get('clientRequestId')=='twenty-20261024-fresh-arithmetic-r162bc-codex-astra-r1');assert author==791
own=next(i for i,x in enumerate(old['tasks']) if x.get('clientRequestId')=='twenty-20261024-arithmetic-r162bc-proof-codex-astra-r1');assert own==794 and old['tasks'][own]['status']=='running'
assert old['tasks'][author]['correctness_gate'] is None and old['tasks'][author]['contribution_gate'] is None
for n,h in baseline['protected'].items():assert sha((P/n).read_bytes())==h
terminal=json.loads((D/'proof-task-status.json').read_text())['structuredContent']
assert terminal['taskId']==old['tasks'][own]['taskId'] and terminal['status']=='completed' and terminal['workState']=='result_available'
assert not terminal['hasPendingChildRuns'] and not terminal['hasPendingQuestion'] and terminal['pendingApproval'] is None
v=json.loads((D/'proof-verification.json').read_text());assert v['status']=='MATCH' and v['bundled_verifier_passed'] and v['review_root_bytes_and_full_modes_unchanged'] and v['author_root_bytes_and_full_modes_unchanged']
assert snapshot(B/'arithmetic-r162bc-proof-r1')==json.loads((D/'private/proof-intake/root-before.json').read_text())
assert snapshot(B/'fresh-arithmetic-discovery-r162bc')==json.loads((D/'private/intake/root-before.json').read_text())
now=datetime.now(timezone.utc).isoformat();review=new['tasks'][own];review.update(terminal)
review.update(observed_utc=now,disposition='PASS_ENTIRE_UNCHANGED_FROZEN_SCOPE',correctness_gate='PASS',verdict_scope='ENTIRE unchanged frozen R162BC7 statement and proof',verdict_condition='Stipulated Source135 operative truth at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',required_author_repairs=[],essential_unverified_correctness_obligations=[],parent_assessment='discovery-arithmetic-r162bc-parent/proof-assessment.md',artifact_verification='discovery-arithmetic-r162bc-parent/proof-verification.json',artifact_status='MATCH',bundled_verifier_passed=True,review='arithmetic-r162bc-proof-r1/private/REVIEW.md',reading_limits='arithmetic-r162bc-proof-r1/private/READING-LIMITS.md',review_sha256=v['review_sha256'],statement_sha256=v['statement_sha256'],proof_sha256=v['proof_sha256'],review_seal_unchanged=True,author_original_files_unchanged=66,admitted_author_copies_unchanged=46,contribution_gate=None,accepted=False,count_change=0,parent_count_at_intake=19,optional_original_history_traversals=0,other_review_inspection=False,transitive_primary_reading_complete=False,status_provenance='Own terminal task_status read once; complete independent correctness reconstruction and reading limits read before adopting PASS. Artifact authentication separate. No sibling live query or watcher.')
a=new['tasks'][author]
a.update(disposition='CORRECTNESS_PASS_CONTRIBUTION_PENDING',correctness_gate='PASS',correctness_review_task_index=own,correctness_review_task_id=terminal['taskId'],correctness_review='arithmetic-r162bc-proof-r1/private/REVIEW.md',correctness_review_sha256=v['review_sha256'],correctness_parent_assessment='discovery-arithmetic-r162bc-parent/proof-assessment.md',correctness_verdict_scope='ENTIRE unchanged frozen statement and proof',correctness_verdict_condition='Stipulated Source135 operative truth at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',correctness_required_author_repairs=[],correctness_essential_unverified_obligations=[],independent_reviews_pending=['substantial_contribution'],contribution_gate=None,accepted=False,count_change=0,frozen_scope_unchanged=True,sealed_author_root_unchanged=True)
assert a['statement_sha256']==v['statement_sha256'] and a['proof_sha256']==v['proof_sha256']
note='R162BC7 independent correctness PASS adopted for the ENTIRE unchanged frozen seven-layer IMM theorem/proof,under stipulated Source135 truth. No required repair or essential unresolved correctness dependency remains. Exact every-field/absolute-threshold/computational-gate/shared-gate/bottom-support/formal-degree scope and1/20000 constant preserved. Parent read full reconstruction and reading limits;review and author seals authenticated unchanged. Separate full substantial-contribution review remains pending,not inspected or live-queried here. No acceptance,count change,downstream work,publication or verdict retry. Campaign19/20,latestR041.'
new['last_parent_progress']=note;snap=new['current_work_snapshot'];snap.update(observed_utc=now,note=note)
snap['arithmetic_r162bc_correctness_pass']=dict(author_task_index=author,review_task_index=own,taskId=terminal['taskId'],correctness_gate='PASS',scope='ENTIRE unchanged frozen statement and proof',condition='Stipulated Source135 operative truth',assessment='discovery-arithmetic-r162bc-parent/proof-assessment.md',statement_sha256=v['statement_sha256'],proof_sha256=v['proof_sha256'],required_repairs=[],essential_unverified_obligations=[],contribution_gate=None,contribution_pending=True,accepted=False,count_change=0,publication='STOPPED')
changed=[i for i,(x,y) in enumerate(zip(old['tasks'],new['tasks'])) if x!=y];assert changed==[author,own] and len(new['tasks'])==len(old['tasks'])
assert all(new[k]==old[k] for k in old if k not in {'tasks','last_parent_progress','current_work_snapshot'})
allowed={'observed_utc','note','arithmetic_r162bc_correctness_pass'};assert all(snap[k]==x for k,x in old['current_work_snapshot'].items() if k not in allowed)
addition=('\n\n### R162BC7 full correctness PASS; contribution pending — '+now+'\n\n'+note+'\n\nThe [parent correctness intake](campaigns/2026-10-14/discovery-arithmetic-r162bc-parent/proof-assessment.md) adopts the separate [complete review](campaigns/2026-10-14/arithmetic-r162bc-proof-r1/private/REVIEW.md),which reconstructs common parameters,all nearest-integer bands,charged S^3 shared-gate occurrence expansion,intermediate rank spaces,exact occupation and four-path trace normalization,adjacent N/D/E partitions,joint run folding including every endpoint/constant case,all-interval scheduling,rounding/switch sums,positive-moment rank,integer-minor transfer and exact final constant. Statement SHA256 '+v['statement_sha256']+' and proof SHA256 '+v['proof_sha256']+' are unchanged. Every characteristic-zero field,one absolute eventual threshold,and all frozen arbitrary-support/fan-in/fan-out/sharing/repetition/free coefficients/zero/constant/formal-degree conventions retained. No narrowing or repair. Reviewer read11 complete canonical texts71737 bytes;12 blobs/16 entries authenticate. Seven supplied primary versions and79 primary page bodies332355 bytes were read at exact recorded extents,including complete operative decomposition/deferred claims and full Forbes paper,with visual exponent checks and seams recovered before verdict. Unread transitive/comparison portions are expressly nonessential to this correctness argument;no external human/exhaustive/priority/history certificate. Zero optional history traversal,no sibling inspection,network retrieval or author followup. Parent original review verifier and independent exact membership/hash/length/full-mode/source/copy checks MATCH79 payloads13648765 bytes,82 whole-root files,16 directories including root;all66 original author inputs and46 admitted copies unchanged. Copied restored fixture and3 wrong anchors behaved as expected. Artifact checks are separate from mathematics. No live contribution-task query,additional delegation,repair,downstream work,polling or watcher. Contribution outcome and acceptance remain pending;count19/20,all older scopes and every unrelated record/modification preserved.\n').encode()
next_t=(json.dumps(new,ensure_ascii=False,indent=2)+'\n').encode();next_j=raw_j+addition
dump(D/'proof-coordination-rebase.json',dict(intake_head=baseline['head'],integration_head=head,head_advanced=head!=baseline['head'],before_task_count=len(old['tasks']),after_task_count=len(new['tasks']),changed_old_task_indices=changed,all_other_tasks_preserved=True,all_other_top_fields_preserved=True,journal_prefix_preserved=True,protected_modifications_preserved=True,tasks_before_sha256=sha(raw_t),tasks_after_sha256=sha(next_t),journal_before_sha256=sha(raw_j),journal_after_sha256=sha(next_j),no_sibling_live_query=True))
dump(D/'proof-registration.json',dict(author_task_index=author,review_task_index=own,taskId=terminal['taskId'],correctness_gate='PASS',scope='ENTIRE unchanged frozen statement/proof',condition='Stipulated Source135 operative truth',contribution_gate=None,contribution_pending=True,accepted=False,count_change=0,campaign_count=19,publication='STOPPED'))
(D/'private/proof-intake/our-tasks-after.json').write_bytes(next_t);(D/'private/proof-intake/our-journal-after.md').write_bytes(next_j)
assert git('rev-parse','HEAD').decode().strip()==head and (P/TP).read_bytes()==raw_t and (P/JP).read_bytes()==raw_j
(P/TP).write_bytes(next_t);(P/JP).write_bytes(next_j)
names=['proof-task-status.json','proof-intake-baseline.json','proof-verification.json','verify-proof-intake.py','proof-assessment.md','manage-proof-intake.py','proof-coordination-rebase.json','proof-registration.json']
paths=[(D/n).relative_to(P).as_posix() for n in names]+[TP,JP];assert len(paths)==len(set(paths))==10
assert git('rev-parse','HEAD').decode().strip()==head and (P/TP).read_bytes()==next_t and (P/JP).read_bytes()==next_j
subprocess.run(['git','add','--',*paths],cwd=P,check=True)
assert {x for x in git('diff','--cached','--name-only','-z').decode().split('\0') if x}=={'openai-proof-research/'+n for n in paths}
for n in paths:assert git('show',':openai-proof-research/'+n)==(P/n).read_bytes()
subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True);assert git('rev-parse','HEAD').decode().strip()==head
subprocess.run(['git','commit','-m','Adopt full correctness PASS for seven-layer IMM nominee'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip()
assert snapshot(B/'arithmetic-r162bc-proof-r1')==json.loads((D/'private/proof-intake/root-before.json').read_text())
assert snapshot(B/'fresh-arithmetic-discovery-r162bc')==json.loads((D/'private/intake/root-before.json').read_text())
assert git('show','HEAD:openai-proof-research/'+TP)==next_t and git('show','HEAD:openai-proof-research/'+JP)==next_j
for n,h in baseline['protected'].items():assert sha((P/n).read_bytes())==h
print(json.dumps(dict(commit=git('rev-parse','HEAD').decode().strip(),changed_old_tasks=changed,all_other_tasks_preserved=True,staged_allowed_paths=10,correctness_gate='PASS',contribution_gate=None,campaign_count=19,index_empty=True,author_and_review_seals_unchanged=True,protected_modifications_preserved=True)))
