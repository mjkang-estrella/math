#!/usr/bin/env python3
"""CAS integrate author nominee and two independent review receipts; no count change."""
from pathlib import Path
from datetime import datetime,timezone
import copy,fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent;A=B/'fresh-arithmetic-discovery-r162bc'
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
old=json.loads(raw_t);new=copy.deepcopy(old)
assert old['newAccepted']==19 and old['target']==20 and old['latestAcceptance']=='R041'
own=next(i for i,x in enumerate(old['tasks']) if x.get('clientRequestId')=='twenty-20261024-fresh-arithmetic-r162bc-codex-astra-r1');assert own==791 and old['tasks'][own]['status']=='running'
baseline=json.loads((D/'intake-baseline.json').read_text())
for n,h in baseline['protected'].items():assert sha((P/n).read_bytes())==h
guard=json.loads((D/'review-prospective-isolation.json').read_text());checks=[]
for i,x in enumerate(old['tasks']):
 if i==own or x.get('status') not in {'running','queued','waiting'} or not x.get('brief'):continue
 a=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(a)==x['brief_sha256']
 patterns=[z for z in re.findall(r'\*[^\s,;()]*\*',a.decode()) if z not in {'*','**'}]
 matches={n:sorted(z for z in patterns if fnmatch.fnmatchcase(n.casefold(),z.casefold())) for n in guard['namespaces']};assert all(matches.values())
 checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=matches))
terminal=json.loads((D/'task-status.json').read_text())['structuredContent']
assert terminal['taskId']==old['tasks'][own]['taskId'] and terminal['status']=='completed' and terminal['workState']=='result_available'
assert not terminal['hasPendingChildRuns'] and not terminal['hasPendingQuestion'] and terminal['pendingApproval'] is None
v=json.loads((D/'verification.json').read_text());intake=json.loads((D/'intake.json').read_text())
assert v['status']=='MATCH' and v['bundled_verifier_passed'] and v['whole_root_bytes_and_full_modes_unchanged']
assert intake['disposition']=='FROZEN_AUTHOR_PROOF_NOMINEE' and intake['frozen_statement'] and intake['accepted'] is False and intake['count_change']==0
assert snapshot(A)==json.loads((D/'private/intake/root-before.json').read_text())
now=datetime.now(timezone.utc).isoformat();rec=new['tasks'][own];rec.update(terminal)
rec.update(observed_utc=now,disposition='FROZEN_AUTHOR_PROOF_NOMINEE',nominee='R162BC7',parent_intake='discovery-arithmetic-r162bc-parent/intake.json',parent_assessment='discovery-arithmetic-r162bc-parent/assessment.md',artifact_verification='discovery-arithmetic-r162bc-parent/verification.json',artifact_status='MATCH',bundled_verifier_passed=True,sealed_author_root_unchanged=True,frozen_statement=True,author_proof_nominee=True,statement=intake['statement'],statement_sha256=intake['statement_sha256'],statement_bytes=intake['statement_bytes'],proof=intake['proof'],proof_sha256=intake['proof_sha256'],proof_bytes=intake['proof_bytes'],full_frozen_scope=intake['full_scope'],proposed_additional_operation=intake['proposed_additional_operation'],paid_source_primary_operations=intake['paid_source_primary_operations'],author_declared_remaining_obligation=None,independent_reviews_pending=['correctness','substantial_contribution'],correctness_gate=None,contribution_gate=None,accepted=False,count_change=0,full_scopes_preserved=True,canonical_text_objects_read_and_authenticated=11,canonical_text_bytes=71737,canonical_folder_blobs=12,primary_objects=7,primary_full_papers=2,transitive_primary_reading_complete=False,optional_original_history_traversals=0,parent_full_intake_pending=False,status_provenance='Own terminal task_status queried once and persisted; complete frozen statement/proof/comparison/reading chronology read; sealed author packet verified unchanged. No independent mathematical grade assigned and no foreign liveness query.')
registrations=[]
for role,scope in [('proof','correctness'),('contribution','substantial_contribution')]:
 prep=json.loads((D/f'{role}-review-preparation.json').read_text());dispatch=json.loads((D/f'{role}-review-dispatch.json').read_text())['structuredContent']
 client=f'twenty-20261024-arithmetic-r162bc-{role}-codex-astra-r1'
 assert not any(x.get('clientRequestId')==client for x in old['tasks'])
 assert dispatch['status']=='running' and dispatch['workState']=='working' and dispatch['providerInstanceId']=='codex' and dispatch['model']=='gpt-6-astra'
 assert {x['id']:x['value'] for x in dispatch['options']}==dict(reasoningEffort='high',serviceTier='default')
 assert not dispatch['hasPendingQuestion'] and dispatch['pendingApproval'] is None
 brief=(P/prep['brief']).read_bytes();assert len(brief)==prep['brief_bytes'] and sha(brief)==prep['brief_sha256']
 assert prep['entire_original_author_brief_retained'] and prep['all_literal_guards_retained'] and prep['standing_bytes_preserved']==5570 and prep['other_review_inspection_forbidden']
 assert intake['statement_sha256']==prep['statement_sha256'] and intake['proof_sha256']==prep['proof_sha256']
 inputs=json.loads((P/prep['root']/'private/author-inputs.json').read_text());assert len(inputs)==66
 for e in inputs:
  f=P/e['path'];a=f.read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256'] and f.stat().st_mode==e['mode']
 index=len(new['tasks']);fresh=copy.deepcopy(dispatch)
 fresh.update(observed_utc=now,role='review',round=1,review_scope=scope,nominee='R162BC7',title='R162BC7: independent full '+('correctness' if role=='proof' else 'substantial-contribution')+' review',clientRequestId=client,parent_thread='6742db91-d35c-44d0-a762-e5d9232f5177',target=dict(providerInstanceId='codex',model='gpt-6-astra',options=dict(reasoningEffort='high',serviceTier='default')),output=prep['root']+'/',brief=prep['brief'],brief_sha256=prep['brief_sha256'],brief_bytes=prep['brief_bytes'],submitted_prompt_contains_full_brief=True,entire_original_author_brief_retained=True,full_frozen_statement_in_prompt=True,statement=intake['statement'],statement_sha256=intake['statement_sha256'],proof=intake['proof'],proof_sha256=intake['proof_sha256'],unchanged_scope=True,independent_review=True,new_review_conversation=True,other_review_inspection_forbidden=True,author_files_hash_only=66,author_semantic_inputs=prep['author_semantic_inputs'],all_previous_literal_guards_and5570_standing_bytes_retained=True,original_foreign_brief_guard_checks_before_creation=True,dispatch_receipt=f'discovery-arithmetic-r162bc-parent/{role}-review-dispatch.json',preparation=f'discovery-arithmetic-r162bc-parent/{role}-review-preparation.json',correctness_gate=None,contribution_gate=None,accepted=False,count_change=0,parent_count_at_dispatch=19,publication='STOPPED',status_provenance='Actual fresh async delegate_task receipt verified as Codex/GPT-6 Astra/high/default; status records dispatch time, no polling/watcher or foreign liveness query.')
 new['tasks'].append(fresh);registrations.append(dict(role=role,review_scope=scope,task_index=index,taskId=dispatch['taskId'],status_at_dispatch=dispatch['status'],brief=prep['brief'],model_options_verified=True,unchanged_frozen_scope=True,independent_conversation=True,count_change=0))
rec['independent_review_task_indices']={x['role']:x['task_index'] for x in registrations};rec['independent_review_task_ids']={x['role']:x['taskId'] for x in registrations}
note='Arithmetic162bc submitted R162BC7,a frozen full author-proof nominee:EVERY characteristic-zero field and sufficiently large n,ONE absolute threshold,EVERY syntactically homogeneous shared-gate seven-layer IMM circuit needs n^(n^(1/4)/20000) computational gates,with arbitrary bottom support/fan-in/out/repeated occurrences/free edge coefficients and exact zero/constant formal-degree conventions. Proposed joint V/U equality-state collision count and run folding retained;no independent correctness/contribution verdict or acceptance. Both independent full-scope reviews dispatched on Codex/GPT-6 Astra/high/default in fresh conversations with peer inspection forbidden. Original verifier and separate parent authentication MATCH,all sealed author bytes/full modes unchanged. All older scopes/dispositions and foreign records preserved. Campaign19/20,latestR041;publication STOPPED.'
new['last_parent_progress']=note;snap=new['current_work_snapshot'];snap.update(observed_utc=now,note=note)
snap['arithmetic_r162bc_nominee_review']=dict(author_task_index=own,nominee='R162BC7',intake='discovery-arithmetic-r162bc-parent/intake.json',frozen_statement=True,author_proof_nominee=True,statement_sha256=intake['statement_sha256'],proof_sha256=intake['proof_sha256'],correctness_gate=None,contribution_gate=None,accepted=False,count_change=0)
snap['arithmetic_r162bc_independent_reviews']=dict(registrations=registrations,other_review_inspection_forbidden=True,full_scope_unchanged=True,foreign_live_queries=False,count_change=0,publication='STOPPED')
changed=[i for i,(a,b) in enumerate(zip(old['tasks'],new['tasks'])) if a!=b];assert changed==[own] and len(new['tasks'])==len(old['tasks'])+2
assert all(new[k]==old[k] for k in old if k not in {'tasks','last_parent_progress','current_work_snapshot'})
allowed={'observed_utc','note','arithmetic_r162bc_nominee_review','arithmetic_r162bc_independent_reviews'};assert all(snap[k]==x for k,x in old['current_work_snapshot'].items() if k not in allowed)
addition=('\n\n### R162BC7 frozen author nominee and two independent reviews — '+now+'\n\n'+note+'\n\nThe [parent intake](campaigns/2026-10-14/discovery-arithmetic-r162bc-parent/assessment.md) preserves the exact statement2250 bytes/SHA256 '+intake['statement_sha256']+' and proof23940 bytes/SHA256 '+intake['proof_sha256']+'. The claimed additional operation expands equality corrections from BOTH layer types on SAME path quadruples,introduces a third state and folds decorations into binary runs for e·2^(runs). The author then claims one common t=floor(n^(1/4)) rank/moment budget,all-interval discrepancy,charged S^3 shared-gate degree-band decomposition,arbitrary-support factor estimates and integer-minor transfer,with every endpoint/rounding/constant/invalid-shift case retained. This is an author claim;no mathematical gate is adopted. The entire stronger actual source and primary operations remain paid. Parent read the full statement/proof/feasibility/working/source comparison/handoff/reading limits,without independently rereading upstream or primary proofs. Author records11 complete canonical texts71737 bytes,12 blobs/16 subtree entries,one source pairing-page visual check,and seven primary versions with two full papers plus bounded operative/deferred reads. Version distinctions,late proof/display recoveries,postfreeze primary visual check,extraction limitations and unexamined transitive ancestry disclosed. No optional original-history traversal,no full formalization/compiler and no exhaustive/priority/isolation claim. Parent exact authentication matched63 payloads/8429780 bytes,66 whole-root files/full modes,11 subdirectories,12 pinned Git blobs,5 unchanged completed original/copy pairs and exact bounded catalogue copy. Frozen statement/proof and3 detached anchors match;original read-only verifier PASS,intact copied fixture and3 wrong-anchor controls behaved as expected. Sorting was fixed BEFORE the one-time seal;this does not relabel prior BB verifier failure. Evidence is artifact-only. Review prompts retain the entire original author brief,all inherited literal guards and5570 standing bytes,full unchanged statement and exact author input ledgers. Current-original foreign brief guards were checked before creating both roots;no foreign live query. Each reviewer independently reads actual source/primary proofs,states full-scope verdict/limits,keeps protected bodies/named metadata private,and may not inspect the other review,repair originals,assign acceptance/count,publish or perform downstream work. No desired-grade retry,polling or watcher. Every foreign task,unrelated modification,journal prefix and older scope/disposition remains unchanged.\n').encode()
next_t=(json.dumps(new,ensure_ascii=False,indent=2)+'\n').encode();next_j=raw_j+addition
dump(D/'coordination-rebase.json',dict(intake_head=baseline['head'],integration_head=head,head_advanced=head!=baseline['head'],before_task_count=len(old['tasks']),after_task_count=len(new['tasks']),changed_old_task_indices=changed,new_task_indices=[x['task_index'] for x in registrations],all_other_tasks_preserved=True,all_other_top_fields_preserved=True,journal_prefix_preserved=True,protected_modifications_preserved=True,tasks_before_sha256=sha(raw_t),tasks_after_sha256=sha(next_t),journal_before_sha256=sha(raw_j),journal_after_sha256=sha(next_j),integration_original_brief_guard_checks=checks,no_foreign_live_queries=True))
dump(D/'review-registration.json',dict(registrations=registrations,author_task_index=own,nominee='R162BC7',frozen_scope_unchanged=True,correctness_gate=None,contribution_gate=None,campaign_count=19,count_change=0,publication='STOPPED'))
(D/'private/intake/our-tasks-after.json').write_bytes(next_t);(D/'private/intake/our-journal-after.md').write_bytes(next_j)
assert git('rev-parse','HEAD').decode().strip()==head and (P/TP).read_bytes()==raw_t and (P/JP).read_bytes()==raw_j
(P/TP).write_bytes(next_t);(P/JP).write_bytes(next_j)
names=['assessment.md','intake.json','verification.json','verify-intake.py','task-status.json','intake-baseline.json','intake-prospective-isolation.json','review-capabilities.json','prepare-reviews.py','review-prospective-isolation.json','proof-review-preparation.json','contribution-review-preparation.json','proof-review-dispatch.json','contribution-review-dispatch.json','manage-intake.py','coordination-rebase.json','review-registration.json']
briefs=[json.loads((D/f'{role}-review-preparation.json').read_text())['brief'] for role in ['proof','contribution']]
paths=[(D/n).relative_to(P).as_posix() for n in names]+briefs+[TP,JP];assert len(paths)==len(set(paths))==21
assert git('rev-parse','HEAD').decode().strip()==head and (P/TP).read_bytes()==next_t and (P/JP).read_bytes()==next_j
subprocess.run(['git','add','--',*paths],cwd=P,check=True)
assert {x for x in git('diff','--cached','--name-only','-z').decode().split('\0') if x}=={'openai-proof-research/'+n for n in paths}
for n in paths:assert git('show',':openai-proof-research/'+n)==(P/n).read_bytes()
subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True);assert git('rev-parse','HEAD').decode().strip()==head
subprocess.run(['git','commit','-m','Record seven-layer IMM nominee and commission independent reviews'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip()
assert snapshot(A)==json.loads((D/'private/intake/root-before.json').read_text())
assert git('show','HEAD:openai-proof-research/'+TP)==next_t and git('show','HEAD:openai-proof-research/'+JP)==next_j
for n,h in baseline['protected'].items():assert sha((P/n).read_bytes())==h
print(json.dumps(dict(commit=git('rev-parse','HEAD').decode().strip(),changed_old_tasks=changed,new_review_indices=[x['task_index'] for x in registrations],all_other_tasks_preserved=True,staged_allowed_paths=21,campaign_count=19,no_mathematical_gate_assigned=True,index_empty=True,sealed_author_root_unchanged=True,protected_modifications_preserved=True)))
