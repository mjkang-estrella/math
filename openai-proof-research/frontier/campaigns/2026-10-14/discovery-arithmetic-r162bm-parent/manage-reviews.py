#!/usr/bin/env python3
"""Register independent reviews; preserve unrelated uncommitted coordination edits."""
from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json, subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
R=B/'fresh-arithmetic-discovery-r162bm';TP='frontier/campaigns/2026-10-14/tasks.json';JP='frontier/NEW-TEN-2026-10-14.md'
def git(*args,input=None):return subprocess.check_output(['git',*args],cwd=P,input=input)
def sha(a):return hashlib.sha256(a).hexdigest()
def encoded(x):return (json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode()
def dump(p,x):p.write_bytes(encoded(x))
def snapshot(root):
 out={}
 for p in root.rglob('*'):
  assert not p.is_symlink()
  if p.is_file():
   a=p.read_bytes();out[p.relative_to(root).as_posix()]=dict(bytes=len(a),sha256=sha(a),mode=p.stat().st_mode)
 return out
assert not git('diff','--cached','--name-only').strip()
head=git('rev-parse','HEAD').decode().strip();ht=git('show',head+':openai-proof-research/'+TP);hj=git('show',head+':openai-proof-research/'+JP)
wt=(P/TP).read_bytes();wj=(P/JP).read_bytes();assert hj==wj,'Concurrent journal edits require separate rebase.'
base=json.loads(ht);working=json.loads(wt)
assert len(base['tasks'])==len(working['tasks'])
assert base['newAccepted']==working['newAccepted']==19 and base['latestAcceptance']==working['latestAcceptance']=='R041'
assert base['gpt_subagent_preferences']==working['gpt_subagent_preferences'] and base['gpt_subagent_preferences']['serviceTier']=='default'
own=817;assert base['tasks'][own]==working['tasks'][own]
assert base['tasks'][own]['clientRequestId']=='twenty-20261024-fresh-arithmetic-r162bm-codex-astra-r1'
foreign_changed=[i for i,(a,b) in enumerate(zip(base['tasks'],working['tasks'])) if a!=b]
foreign_top=[k for k in base if k!='tasks' and base[k]!=working[k]]
terminal=json.loads((D/'task-status.json').read_bytes())['structuredContent']
assert terminal['taskId']==base['tasks'][own]['taskId'] and terminal['status']=='completed' and terminal['workState']=='result_available'
assert not terminal['hasPendingChildRuns'] and not terminal['hasPendingQuestion'] and terminal['pendingApproval'] is None
v=json.loads((D/'verification.json').read_bytes());assert v['status']=='MATCH' and v['whole_root_bytes_and_full_modes_unchanged']
assert snapshot(R)==json.loads((D/'private/intake/root-before.json').read_bytes())
baseline=json.loads((D/'intake-baseline.json').read_bytes())
for n,h in baseline['protected'].items():assert sha((P/n).read_bytes())==h
now=datetime.now(timezone.utc).isoformat();review_records=[];preps=[]
for role in ['proof','contribution']:
 prep=json.loads((D/f'{role}-brief-preparation.json').read_bytes());preps.append(prep)
 a=(P/prep['brief']).read_bytes();assert len(a)==prep['bytes'] and sha(a)==prep['sha256'] and len(a.decode())<120000
 receipt=json.loads((D/f'{role}-dispatch.json').read_bytes())['structuredContent']
 assert receipt['status']=='running' and receipt['workState']=='working' and receipt['providerInstanceId']=='codex' and receipt['model']=='gpt-6-astra'
 assert {x['id']:x['value'] for x in receipt['options']}==dict(reasoningEffort='high',serviceTier='default')
 assert not receipt['hasPendingQuestion'] and receipt['pendingApproval'] is None
 client=f'twenty-20261024-arithmetic-r162bm-{role}-codex-astra-r1'
 assert not any(x.get('clientRequestId')==client for x in working['tasks'])
 rec=copy.deepcopy(receipt)
 rec.update(observed_utc=now,role='review',review_kind='correctness' if role=='proof' else 'substantial_contribution',round=1,title='R162BM: independent full '+('correctness' if role=='proof' else 'substantial-contribution')+' review',clientRequestId=client,parent_thread='6742db91-d35c-44d0-a762-e5d9232f5177',target=dict(providerInstanceId='codex',model='gpt-6-astra',options=dict(reasoningEffort='high',serviceTier='default')),output=prep['root']+'/',brief=prep['brief'],brief_bytes=prep['bytes'],brief_sha256=prep['sha256'],submitted_prompt_contains_full_brief=True,candidate='R162BM',statement_sha256=v['statement_sha256'],author_proof_sha256=v['proof_sha256'],entire_unchanged_scope=True,independent_review=True,peer_review_excluded=True,optional_history_traversals=0,all_inherited_literal_guards_retained=True,standing_bytes_preserved=5570,accepted=False,count_change=0,parent_count_at_dispatch=19,publication='STOPPED',status_provenance='Fresh async receipt confirms Codex/GPT-6 Astra/high/default. No peer-body/status inspection or polling.')
 review_records.append(rec)
indices=[len(base['tasks']),len(base['tasks'])+1]
def apply(original):
 out=copy.deepcopy(original);rec=out['tasks'][own];rec.update(terminal)
 rec.update(observed_utc=now,disposition='AUTHOR_PROOF_NOMINEE_REVIEWS_PENDING',candidate='R162BM',parent_intake='discovery-arithmetic-r162bm-parent/intake.json',parent_assessment='discovery-arithmetic-r162bm-parent/assessment.md',artifact_verification='discovery-arithmetic-r162bm-parent/verification.json',artifact_status='MATCH',bundled_verifier_passed=True,sealed_author_root_unchanged=True,frozen_statement=True,author_proof_nominee=True,statement='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bm/STATEMENT.md',statement_sha256=v['statement_sha256'],author_proof_sha256=v['proof_sha256'],full_scope='Original sine standard map on the two-torus,normalized area,natural entropy;h_m(f_k)-log(pi*k) tends to0 for every sufficiently large positive real parameter.',correctness_gate=None,contribution_gate=None,accepted=False,count_change=0,correctness_review_task=review_records[0]['taskId'],contribution_review_task=review_records[1]['taskId'],canonical_text_objects_read_and_authenticated=11,canonical_text_bytes=145989,canonical_folder_blobs=12,canonical_entries=16,primary_objects=6,primary_distinct_pages_touched=99,primary_full_papers=4,complete_primary_errata=1,primary_visual_pages=13,transitive_primary_reading_complete=False,late_primary_comparison='BXY2017 read after freeze,before extended proof drafting',optional_original_history_traversals=0,parent_full_intake_pending=False,status_provenance='Own terminal result queried once;full author proof and evidence read. Initial combined proof display recovered in two complete contiguous spans. Independent mathematical gates remain pending;artifact checks only.')
 out['tasks'].extend(copy.deepcopy(review_records))
 additions={
 'arithmetic_r162bm_author_intake':dict(task_index=own,disposition='AUTHOR_PROOF_NOMINEE_REVIEWS_PENDING',candidate='R162BM',statement_sha256=v['statement_sha256'],proof_sha256=v['proof_sha256'],artifact_status='MATCH',correctness_gate=None,contribution_gate=None,count_change=0),
 'arithmetic_r162bm_independent_reviews':dict(proof_task_index=indices[0],contribution_task_index=indices[1],proof_task_id=review_records[0]['taskId'],contribution_task_id=review_records[1]['taskId'],entire_scope_unchanged=True,peer_isolation=True,serviceTier='default',count_change=0,publication='STOPPED')}
 for k,value in additions.items():assert k not in out['current_work_snapshot'];out['current_work_snapshot'][k]=value
 assert [i for i,(a,b) in enumerate(zip(original['tasks'],out['tasks'])) if a!=b]==[own]
 assert all(out[k]==original[k] for k in original if k not in {'tasks','current_work_snapshot'})
 assert all(out['current_work_snapshot'][k]==value for k,value in original['current_work_snapshot'].items())
 return out
indexed=apply(base);merged=apply(working);it=encoded(indexed);mt=encoded(merged)
note='R162BM author-proof nominee:original standard sine map with normalized area satisfies h_m(f_k)=log(pi*k)+o(1) across the entire positive real parameter tail. Full unchanged statement/proof sent to separate independent correctness and substantial-contribution reviews,each Codex/GPT-6 Astra/high/default. No mathematical gate or count yet;campaign19/20,latestR041;publication STOPPED.'
addition=('\n\n### R162BM author-proof intake and independent reviews — '+now+'\n\n'+note+'\n\nThe [parent assessment](campaigns/2026-10-14/discovery-arithmetic-r162bm-parent/assessment.md) records all source/classical payments and the claimed additional joint stretching-loss argument,including global weighted affine-boundary control and transport through original graphs. Parent read the complete30,673-byte author proof,9,069-byte comparison,feasibility/working records and10,730-byte reading limits;initial combined truncation was recovered through contiguous proof spans. This is not independent mathematical verification. Canonical11texts145989bytes12blobs16entries authenticated and reported completely read;compiled PDF authentication only. Primary99touchedpages(somepartial),four fullpapers plus2pageerrata,13renders,incomplete ancestry. BXY2017 post-freeze/pre-drafting read remains explicitly disclosed. History0. Parent/bundled artifact MATCH67payloads5273454bytes69files10directories,12Gitblobs,6primaryPDFs,7direct/completedoriginal-copy pairs;frozen statement and all author bytes/fullmodes unchanged. Three wrong anchors rejected;restored tiny fixture passed. Reviewers independently assess every full-scope deduction and strongest compatible source/actual-primary contribution comparison;neither sees the other review. Both initial briefs retain all literal guards and5570standingbytes;full modes recorded for admitted author inputs. Unrelated uncommitted shared-index changes are preserved separately and excluded from this commit. No new discovery round,scope repair,desired-grade retry,downstream work or count.\n').encode();nj=hj+addition
paths=[(D/n).relative_to(P).as_posix() for n in ['assessment.md','intake.json','verification.json','verify-intake.py','task-status.json','intake-baseline.json','intake-prospective-isolation.json','prepare-reviews.py','review-prospective-isolation.json','review-capabilities.json','proof-brief-preparation.json','contribution-brief-preparation.json','proof-dispatch.json','contribution-dispatch.json','coordination-rebase.json','manage-reviews.py']]+[x['brief'] for x in preps]+[TP,JP]
assert len(paths)==len(set(paths))==20
dump(D/'coordination-rebase.json',dict(intake_head=baseline['head'],integration_head=head,head_advanced=head!=baseline['head'],before_task_count=len(base['tasks']),after_task_count=len(indexed['tasks']),changed_old_task_indices=[own],new_review_task_indices=indices,unrelated_uncommitted_task_indices=foreign_changed,unrelated_uncommitted_top_fields=foreign_top,all_unrelated_worktree_edits_preserved=True,foreign_edits_excluded_from_commit=True,top_progress_note_preserved=True,journal_prefix_preserved=True,head_tasks_before_sha256=sha(ht),working_tasks_before_sha256=sha(wt),index_tasks_after_sha256=sha(it),working_tasks_after_sha256=sha(mt),journal_after_sha256=sha(nj),no_foreign_live_queries=True))
(D/'private/intake/tasks-index-after.json').write_bytes(it);(D/'private/intake/tasks-working-after.json').write_bytes(mt)
assert git('rev-parse','HEAD').decode().strip()==head and (P/TP).read_bytes()==wt and (P/JP).read_bytes()==wj and not git('diff','--cached','--name-only').strip()
(P/TP).write_bytes(mt);(P/JP).write_bytes(nj)
other=[n for n in paths if n!=TP];subprocess.run(['git','add','--',*other],cwd=P,check=True)
blob=git('hash-object','-w','--stdin',input=it).decode().strip()
subprocess.run(['git','update-index','--add','--cacheinfo','100644',blob,'openai-proof-research/'+TP],cwd=P,check=True)
assert {s for s in git('diff','--cached','--name-only','-z').decode().split('\0') if s}=={'openai-proof-research/'+n for n in paths}
assert git('show',':openai-proof-research/'+TP)==it
for n in other:assert git('show',':openai-proof-research/'+n)==(P/n).read_bytes()
subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
assert git('rev-parse','HEAD').decode().strip()==head and (P/TP).read_bytes()==mt and (P/JP).read_bytes()==nj
subprocess.run(['git','commit','-m','Submit standard-map entropy nominee to two independent reviews'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip()
assert git('show','HEAD:openai-proof-research/'+TP)==it and (P/TP).read_bytes()==mt
after=json.loads((P/TP).read_bytes());committed=json.loads(it)
assert [i for i,(a,b) in enumerate(zip(after['tasks'],committed['tasks'])) if a!=b]==foreign_changed
assert [k for k in committed if k!='tasks' and after[k]!=committed[k]]==foreign_top
assert snapshot(R)==json.loads((D/'private/intake/root-before.json').read_bytes())
for n,h in baseline['protected'].items():assert sha((P/n).read_bytes())==h
print(json.dumps(dict(commit=git('rev-parse','HEAD').decode().strip(),new_review_indices=indices,campaign_count=19,staged_paths=20,foreign_uncommitted_edits_preserved=foreign_changed,foreign_edits_excluded_from_commit=True,author_seal_unchanged=True,index_empty=True)))
