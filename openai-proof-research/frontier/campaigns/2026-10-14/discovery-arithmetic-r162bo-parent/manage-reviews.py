#!/usr/bin/env python3
"""Register two independent reviews, preserving unrelated pending edits."""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent;R=B/'fresh-arithmetic-discovery-r162bo'
TP='frontier/campaigns/2026-10-14/tasks.json';JP='frontier/NEW-TEN-2026-10-14.md'
def git(*a,input=None):return subprocess.check_output(['git',*a],cwd=P,input=input)
def sha(a):return hashlib.sha256(a).hexdigest()
def enc(x):return (json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode()
def snap(root):
 d={}
 for p in root.rglob('*'):
  assert not p.is_symlink()
  if p.is_file():
   a=p.read_bytes();d[p.relative_to(root).as_posix()]=dict(bytes=len(a),sha256=sha(a),mode=p.stat().st_mode)
 return d
assert not git('diff','--cached','--name-only').strip()
h=git('rev-parse','HEAD').decode().strip();ht=git('show',h+':openai-proof-research/'+TP);hj=git('show',h+':openai-proof-research/'+JP)
wt=(P/TP).read_bytes();wj=(P/JP).read_bytes();assert wj==hj
base=json.loads(ht);work=json.loads(wt);assert len(base['tasks'])==len(work['tasks']) and base['tasks'][822]==work['tasks'][822]
assert base['newAccepted']==work['newAccepted']==19 and base['latestAcceptance']==work['latestAcceptance']=='R041'
assert base['gpt_subagent_preferences']==work['gpt_subagent_preferences'] and work['gpt_subagent_preferences']['serviceTier']=='default'
foreign=[i for i,(a,b) in enumerate(zip(base['tasks'],work['tasks'])) if a!=b];foreign_top=[k for k in base if k!='tasks' and base[k]!=work[k]]
terminal=json.loads((D/'task-status.json').read_bytes())['structuredContent'];assert terminal['taskId']==base['tasks'][822]['taskId'] and terminal['status']=='completed' and terminal['workState']=='result_available'
assert not terminal['hasPendingChildRuns'] and not terminal['hasPendingQuestion'] and terminal['pendingApproval'] is None
v=json.loads((D/'verification.json').read_bytes());assert v['status']=='MATCH' and snap(R)==json.loads((D/'private/intake/root-before.json').read_bytes())
baseline=json.loads((D/'intake-baseline.json').read_bytes())
for n,s in baseline['protected'].items():assert sha((P/n).read_bytes())==s
now=datetime.now(timezone.utc).isoformat();reviews=[];preps=[]
for role in ['proof','contribution']:
 prep=json.loads((D/f'{role}-brief-preparation.json').read_bytes());a=(P/prep['brief']).read_bytes();assert len(a)==prep['bytes'] and sha(a)==prep['sha256'] and len(a.decode())<120000;preps.append(prep)
 r=json.loads((D/f'{role}-dispatch.json').read_bytes())['structuredContent'];assert r['status']=='running' and r['workState']=='working' and r['providerInstanceId']=='codex' and r['model']=='gpt-6-astra'
 assert {x['id']:x['value'] for x in r['options']}==dict(reasoningEffort='high',serviceTier='default') and not r['hasPendingQuestion'] and r['pendingApproval'] is None
 client=f'twenty-20261025-arithmetic-r162bo-{role}-codex-astra-r1';assert not any(x.get('clientRequestId')==client for x in work['tasks'])
 rec=copy.deepcopy(r);rec.update(observed_utc=now,role='review',review_kind='correctness' if role=='proof' else 'substantial_contribution',round=1,title='R162BO: independent full '+('correctness' if role=='proof' else 'substantial-contribution')+' review',clientRequestId=client,parent_thread='6742db91-d35c-44d0-a762-e5d9232f5177',target=dict(providerInstanceId='codex',model='gpt-6-astra',options=dict(reasoningEffort='high',serviceTier='default')),output=prep['root']+'/',brief=prep['brief'],brief_bytes=prep['bytes'],brief_sha256=prep['sha256'],submitted_prompt_contains_full_brief=True,candidate='R162BO',statement_sha256=v['statement_sha256'],author_proof_sha256=v['proof_sha256'],entire_unchanged_scope=True,independent_review=True,peer_review_excluded=True,optional_history_traversals=0,all_inherited_literal_guards_retained=True,standing_bytes_preserved=5570,accepted=False,count_change=0,parent_count_at_dispatch=19,publication='STOPPED',status_provenance='Fresh async receipt confirms Codex/GPT-6 Astra/high/default. No peer-body/status inspection or polling.')
 reviews.append(rec)
indices=[len(base['tasks']),len(base['tasks'])+1]
def update(original):
 x=copy.deepcopy(original);r=x['tasks'][822];r.update(terminal)
 r.update(observed_utc=now,disposition='AUTHOR_PROOF_NOMINEE_REVIEWS_PENDING',candidate='R162BO',parent_intake='discovery-arithmetic-r162bo-parent/intake.json',parent_assessment='discovery-arithmetic-r162bo-parent/assessment.md',artifact_verification='discovery-arithmetic-r162bo-parent/verification.json',artifact_status='MATCH',sealed_author_root_unchanged=True,frozen_statement=True,author_proof_nominee=True,statement='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bo/STATEMENT.md',statement_sha256=v['statement_sha256'],author_proof_sha256=v['proof_sha256'],full_scope='Exact interval-variance energy E(rho)<=H(rho)/3 for every countably supported real finite-Shannon-entropy law,no support/moment bounds;coefficient1/3 optimal.',correctness_gate=None,contribution_gate=None,accepted=False,count_change=0,correctness_review_task=reviews[0]['taskId'],contribution_review_task=reviews[1]['taskId'],canonical_text_objects_read_and_authenticated=9,canonical_text_bytes=77648,canonical_folder_blobs=10,canonical_entries=13,primary_objects=7,primary_distinct_pages_read=117,primary_full_versions=5,primary_visual_pages=2,model_output_supplements_provenance_explicit=True,transitive_primary_reading_complete=False,optional_original_history_traversals=0,parent_full_intake_pending=False,status_provenance='Own terminal result queried once;complete author proof,feasibility,comparison,reading records,handoffs and actual private verifier read. Root verify.py missing-path attempt read no bytes. No mathematical grade from parent intake.')
 x['tasks'].extend(copy.deepcopy(reviews))
 additions={'arithmetic_r162bo_author_intake':dict(task_index=822,candidate='R162BO',disposition='AUTHOR_PROOF_NOMINEE_REVIEWS_PENDING',statement_sha256=v['statement_sha256'],proof_sha256=v['proof_sha256'],artifact_status='MATCH',correctness_gate=None,contribution_gate=None,count_change=0),'arithmetic_r162bo_independent_reviews':dict(proof_task_index=indices[0],contribution_task_index=indices[1],proof_task_id=reviews[0]['taskId'],contribution_task_id=reviews[1]['taskId'],entire_scope_unchanged=True,peer_isolation=True,serviceTier='default',count_change=0,publication='STOPPED')}
 for k,val in additions.items():assert k not in x['current_work_snapshot'];x['current_work_snapshot'][k]=val
 assert [i for i,(a,b) in enumerate(zip(original['tasks'],x['tasks'])) if a!=b]==[822]
 assert all(x[k]==original[k] for k in original if k not in {'tasks','current_work_snapshot'})
 assert all(x['current_work_snapshot'][k]==val for k,val in original['current_work_snapshot'].items())
 return x
idx=enc(update(base));merged=enc(update(work))
note=('\n\n### R162BO sharp variance-energy author proof and independent reviews — '+now+'\n\n'
'R162BO submits the entire unchanged sharp E(rho)<=H(rho)/3 theorem for countably supported real laws of finite Shannon entropy,without support/moment/minimum-mass/spacing bounds. Exact factor4,half-open intervals,natural logs,same actual law and optimality via uniform integer laws are retained. [Parent intake](campaigns/2026-10-14/discovery-arithmetic-r162bo-parent/assessment.md) assigns no grade/count. Full proof and prefreeze derivation read;the proposed new upper estimate is a weighted potential across simultaneous actual mass/distance jumps. Countable transfer is ordinary local-moment/Fatou;sharpness is credited to the actual companion. Source148 full formula and stronger operations paid. All9canonicaltexts77648bytes read,10blobs13entries authenticated;7primaryversions117pages(5fullversions),2renders,incomplete ancestry,recoveries and limited unused postproof search disclosed. Three model-output supplements were rebound before freeze to immutable e4aabb83a24608517193b1a48536dde094021c4f;their provenance is explicit and not silently peer-reviewed/stipulated. Parent/bundled artifact MATCH58payloads4579554bytes60files11dirs,7primarybindings,3supplementpins,5original/copy pairs,frozen hashes;wronganchors rejected,restoredfixturepassed,allsealedbytes/modesunchanged. Independent full correctness and substantial-contribution reviews now run Codex/GPT-6 Astra/high/default with peer isolation and zero optional history traversal. All guards/5570standingbytes retained. No scope repair,retry,downstream/publication or acceptance. Campaign19/20,latestR041. Unrelated pending shared-index edits preserved and excluded from this commit.\n').encode();nj=hj+note
(D/'coordination-rebase.json').write_bytes(enc(dict(intake_head=baseline['head'],integration_head=h,changed_old_task_indices=[822],new_review_task_indices=indices,foreign_uncommitted_task_indices=foreign,foreign_uncommitted_top_fields=foreign_top,foreign_edits_preserved_and_excluded=True,head_tasks_before_sha256=sha(ht),working_tasks_before_sha256=sha(wt),index_tasks_after_sha256=sha(idx),working_tasks_after_sha256=sha(merged),journal_prefix_preserved=True,count_change=0)))
names=['assessment.md','intake.json','verification.json','verify-intake.py','task-status.json','intake-baseline.json','intake-prospective-isolation.json','prepare-reviews.py','review-prospective-isolation.json','review-capabilities.json','proof-brief-preparation.json','contribution-brief-preparation.json','proof-dispatch.json','contribution-dispatch.json','coordination-rebase.json','manage-reviews.py'];paths=[(D/n).relative_to(P).as_posix() for n in names]+[x['brief'] for x in preps]+[TP,JP];assert len(paths)==len(set(paths))==20
assert git('rev-parse','HEAD').decode().strip()==h and (P/TP).read_bytes()==wt and (P/JP).read_bytes()==wj and not git('diff','--cached','--name-only').strip()
(P/TP).write_bytes(merged);(P/JP).write_bytes(nj)
subprocess.run(['git','add','--',*[n for n in paths if n!=TP]],cwd=P,check=True)
blob=git('hash-object','-w','--stdin',input=idx).decode().strip();subprocess.run(['git','update-index','--add','--cacheinfo','100644',blob,'openai-proof-research/'+TP],cwd=P,check=True)
assert {n for n in git('diff','--cached','--name-only','-z').decode().split('\0') if n}=={'openai-proof-research/'+n for n in paths}
assert git('show',':openai-proof-research/'+TP)==idx
for n in paths:
 if n!=TP:assert git('show',':openai-proof-research/'+n)==(P/n).read_bytes()
subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
assert git('rev-parse','HEAD').decode().strip()==h and (P/TP).read_bytes()==merged and (P/JP).read_bytes()==nj
subprocess.run(['git','commit','-m','Submit sharp variance-energy nominee to independent reviews'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip() and git('show','HEAD:openai-proof-research/'+TP)==idx and (P/TP).read_bytes()==merged
assert snap(R)==json.loads((D/'private/intake/root-before.json').read_bytes())
for n,s in baseline['protected'].items():assert sha((P/n).read_bytes())==s
print(json.dumps(dict(commit=git('rev-parse','HEAD').decode().strip(),changed_old_tasks=[822],new_review_indices=indices,staged_paths=20,foreign_edits_preserved=foreign,count=19,author_seal_unchanged=True)))
