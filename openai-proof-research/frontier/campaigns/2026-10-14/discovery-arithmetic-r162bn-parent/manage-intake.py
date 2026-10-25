#!/usr/bin/env python3
"""Archive one prefreeze round and start Source148; preserve foreign edits."""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
N=B/'discovery-arithmetic-r162bo-parent';R=B/'fresh-arithmetic-discovery-r162bn'
TP='frontier/campaigns/2026-10-14/tasks.json';JP='frontier/NEW-TEN-2026-10-14.md'
def git(*a,input=None):return subprocess.check_output(['git',*a],cwd=P,input=input)
def sha(a):return hashlib.sha256(a).hexdigest()
def enc(x):return (json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode()
def snap(root):
 out={}
 for p in root.rglob('*'):
  assert not p.is_symlink()
  if p.is_file():
   a=p.read_bytes();out[p.relative_to(root).as_posix()]=dict(bytes=len(a),sha256=sha(a),mode=p.stat().st_mode)
 return out
assert not git('diff','--cached','--name-only').strip()
h=git('rev-parse','HEAD').decode().strip();ht=git('show',h+':openai-proof-research/'+TP);hj=git('show',h+':openai-proof-research/'+JP)
wt=(P/TP).read_bytes();wj=(P/JP).read_bytes();assert wj==hj
base=json.loads(ht);work=json.loads(wt);assert len(base['tasks'])==len(work['tasks']) and base['tasks'][821]==work['tasks'][821]
assert base['newAccepted']==work['newAccepted']==19 and base['latestAcceptance']==work['latestAcceptance']=='R041'
assert base['gpt_subagent_preferences']==work['gpt_subagent_preferences'] and work['gpt_subagent_preferences']['serviceTier']=='default'
foreign=[i for i,(a,b) in enumerate(zip(base['tasks'],work['tasks'])) if a!=b];foreign_top=[k for k in base if k!='tasks' and base[k]!=work[k]]
term=json.loads((D/'task-status.json').read_bytes())['structuredContent'];assert term['taskId']==base['tasks'][821]['taskId'] and term['status']=='completed' and term['workState']=='result_available'
assert not term['hasPendingChildRuns'] and not term['hasPendingQuestion'] and term['pendingApproval'] is None
intake=json.loads((D/'intake.json').read_bytes());v=json.loads((D/'verification.json').read_bytes());assert intake['disposition']=='PREFREEZE_NO_NOMINEE' and v['status']=='MATCH'
assert snap(R)==json.loads((D/'private/intake/root-before.json').read_bytes())
prep=json.loads((N/'brief-preparation.json').read_bytes());brief=(P/prep['brief']).read_bytes();assert len(brief)==prep['bytes'] and sha(brief)==prep['sha256'] and len(brief.decode())<120000
dispatch=json.loads((N/'dispatch.json').read_bytes())['structuredContent'];assert dispatch['status']=='running' and dispatch['workState']=='working' and dispatch['model']=='gpt-6-astra' and dispatch['providerInstanceId']=='codex'
assert {e['id']:e['value'] for e in dispatch['options']}==dict(reasoningEffort='high',serviceTier='default')
assert not dispatch['hasPendingQuestion'] and dispatch['pendingApproval'] is None
assert prep['all_previous_literal_guards_retained'] and prep['all_extra_guard_literals_verified'] and prep['standing_bytes_preserved']==5570
client='twenty-20261025-fresh-arithmetic-r162bo-codex-astra-r1';assert not any(x.get('clientRequestId')==client for x in work['tasks'])
now=datetime.now(timezone.utc).isoformat();new_index=len(base['tasks'])
fresh=copy.deepcopy(dispatch)
fresh.update(observed_utc=now,role='research',round=1,title='Arithmetic162bo: confirmed entropy-rate dimension discovery',clientRequestId=client,parent_thread='6742db91-d35c-44d0-a762-e5d9232f5177',target=dict(providerInstanceId='codex',model='gpt-6-astra',options=dict(reasoningEffort='high',serviceTier='default')),output='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bo/',brief=prep['brief'],brief_bytes=prep['bytes'],brief_sha256=prep['sha256'],submitted_prompt_contains_full_brief=True,source_index=148,source_family_navigation='Exact catalogue[243744,244844). One bounded14000byte window decoded148/149titles and only148body;149body unread,third heading boundaryonly. Same window reread to correct paper.pdf assumption to actualmain.pdf. One root10blobs13entries9texts77648bytes. Actualbuild/main.tex2261/Gite545389b85c7d09dcc5381e460c707b9a74fd8bc. Parent operativeproofnotread.',round_namespace='Distinct entropy-rate dimension family. Entire finite real self-similar measure dimension min(1,h_RW/chi),with exact overlaps and unequal/negative contractions,is already paid. Strongest actual source/primary operations must be read. Actual composed-map entropy is not symbolic entropy;all old Salem/nonstationary/Markov and entropy-overlap scopes preserved.',all_previous_literal_guards_and5570_standing_bytes_retained=True,all_new_literal_guard_twins_verified_before_dispatch=True,completed_direct_inputs=5,dispatch_receipt='discovery-arithmetic-r162bo-parent/dispatch.json',prospective_isolation='discovery-arithmetic-r162bo-parent/prospective-isolation.json',prompt_length_checked_before_dispatch=True,distinct_family=True,new_author_conversation=True,independent_review=False,accepted=False,count_change=0,parent_count_at_dispatch=19,publication='STOPPED',status_provenance='Fresh async receipt verifies Codex/GPT-6 Astra/high/default. No polling,watcher or foreign liveness query.')
def update(original):
 x=copy.deepcopy(original);r=x['tasks'][821];r.update(term)
 r.update(observed_utc=now,disposition='PREFREEZE_NO_NOMINEE',parent_intake='discovery-arithmetic-r162bn-parent/intake.json',parent_assessment='discovery-arithmetic-r162bn-parent/assessment.md',artifact_status='MATCH',artifact_verification='discovery-arithmetic-r162bn-parent/verification.json',sealed_author_root_unchanged=True,frozen_statement=False,author_proof_nominee=False,no_new_diagnostic_selected=True,diagnostic_selected=False,correctness_gate=None,contribution_gate=None,accepted=False,count_change=0,paid_reduction=intake['paid_reduction'],retained_mathematics=intake['retained_mathematics'],unpaid_obligation=intake['unpaid_obligation'],canonical_text_objects_read_and_authenticated=28,canonical_text_bytes=601146,canonical_folder_blobs=30,canonical_entries=39,primary_objects=6,primary_distinct_pages_read=154,primary_full_papers=2,primary_visual_pages=3,transitive_primary_reading_complete=False,optional_original_history_traversals=0,parent_full_intake_pending=False,status_provenance='Own terminal result read once;complete author derivation,source-interface/working/reading records,handoffs and verifier read. No independent parent source rereview or mathematical grade. Packet unchanged.')
 x['tasks'].append(copy.deepcopy(fresh))
 additions={'arithmetic_r162bn_archive':dict(observed_utc=now,task_index=821,disposition='PREFREEZE_NO_NOMINEE',frozen_statement=False,accepted=False,count_change=0),'arithmetic_r162bo_dispatch':dict(task_index=new_index,taskId=dispatch['taskId'],source=148,status='running',serviceTier='default',distinct_family=True,catalogue_extent=[243744,244844],canonical_folders=1,canonical_blobs=10,canonical_entries=13,canonical_texts=9,canonical_text_bytes=77648,completed_direct_inputs=5,count_change=0,publication='STOPPED')}
 for k,val in additions.items():assert k not in x['current_work_snapshot'];x['current_work_snapshot'][k]=val
 assert [i for i,(a,b) in enumerate(zip(original['tasks'],x['tasks'])) if a!=b]==[821]
 assert all(x[k]==original[k] for k in original if k not in {'tasks','current_work_snapshot'})
 assert all(x['current_work_snapshot'][k]==val for k,val in original['current_work_snapshot'].items())
 return x
idx=enc(update(base));merged=enc(update(work));baseline=json.loads((D/'intake-baseline.json').read_bytes())
note=('\n\n### R162BN prefreeze archive and entropy-rate dimension dispatch — '+now+'\n\n'
'R162BN is PREFREEZE/no nominee,no statement or diagnostic frozen. The [parent intake](campaigns/2026-10-14/discovery-arithmetic-r162bn-parent/assessment.md) preserves the common second-order Euclidean action correction for the1/q tail,all its multiple harmonics,and the exact cubic incompatibility for one fourth-mode perturbation at denominators6/12. Those calculations neither construct exact caustics nor establish a general impossibility. Missing rational graphs and common analytic compatibility remain unproved;available rational first jets and full-family area-label reductions are already paid. Parent read complete DERIVATION16079bytes,SOURCE-INTERFACES8698bytes,WORKING3256bytes,READING-LIMITS8168bytes and handoffs/verifier,not independent source/primary proof rereading. Both source proofs28texts601146bytes30blobs39entries read/authenticated;2PDFsauthonly. Primary154pages across6PDFs includes distinct versions,2fullpapers and complete published dynamical proof,3already-counted rendered pages;late reads,partial appendices,version uncertainty and recoveries disclosed. History0. Parent/bundled artifact MATCH75payloads10346795bytes77files17dirs,5original/copy pairs unchanged;3wronganchorsrejected,restoredfixturepassed. No mathematical gates or count. New Arithmetic162bo Source148 entropy-rate dimension discovery runs Codex/GPT-6 Astra/high/default. Exact catalogue243744..244844,one boundedwindow148/149titles+only148body;149bodyunread;metadata regex assumption corrected on samewindow. One root10blobs13entries9texts77648bytes,actualbuild/main.tex2261/Gite545389b85c7d09dcc5381e460c707b9a74fd8bc,compiledmain.pdf;parent sourceproofnotread. Entire self-similar formula including exact overlaps,unequal/negative contractions is paid. All literalguards,5570standingbytes and old scopes preserved. Campaign19/20,latestR041,publication/downstreamSTOPPED. Unrelated uncommitted coordination remains preserved and excluded from this commit.\n').encode();nj=hj+note
for e in json.loads((N/'private/completed-direct-inputs.json').read_bytes()):
 p=P/e['path'];a=p.read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256'] and p.stat().st_mode==e['mode']
for n,s in baseline['protected'].items():assert sha((P/n).read_bytes())==s
(D/'coordination-rebase.json').write_bytes(enc(dict(intake_head=baseline['head'],integration_head=h,changed_old_tasks=[821],new_task_index=new_index,foreign_uncommitted_task_indices=foreign,foreign_uncommitted_top_fields=foreign_top,foreign_edits_preserved_and_excluded=True,journal_prefix_preserved=True,index_tasks_after_sha256=sha(idx),working_tasks_after_sha256=sha(merged),count_change=0)))
(N/'registration.json').write_bytes(enc(dict(task_index=new_index,taskId=dispatch['taskId'],status_at_dispatch='running',distinct_family=True,model_options_verified=True,count_change=0,publication='STOPPED')))
names=['intake-baseline.json','intake-prospective-isolation.json','verify-intake.py','verification.json','task-status.json','assessment.md','intake.json','prepare-next.py','integration-guard.json','manage-intake.py','coordination-rebase.json']
paths=[(D/n).relative_to(P).as_posix() for n in names]+[(N/n).relative_to(P).as_posix() for n in ['brief-preparation.json','capabilities.json','dispatch.json','prospective-isolation.json','registration.json']]+[prep['brief'],TP,JP];assert len(paths)==len(set(paths))==19
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
subprocess.run(['git','commit','-m','Archive billiard prefreeze work and start entropy-rate dimension discovery'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip() and git('show','HEAD:openai-proof-research/'+TP)==idx and (P/TP).read_bytes()==merged
assert snap(R)==json.loads((D/'private/intake/root-before.json').read_bytes())
for n,s in baseline['protected'].items():assert sha((P/n).read_bytes())==s
print(json.dumps(dict(commit=git('rev-parse','HEAD').decode().strip(),changed_old_tasks=[821],new_task_index=new_index,staged_paths=19,foreign_edits_preserved=foreign,count=19,author_seal_unchanged=True)))
