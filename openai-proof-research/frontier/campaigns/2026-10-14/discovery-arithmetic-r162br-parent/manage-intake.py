#!/usr/bin/env python3
"""Archive the paid comparison and register distinct discovery, preserving foreign edits."""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
N=B/'discovery-arithmetic-r162bs-parent';R=B/'fresh-arithmetic-discovery-r162br'
TP='frontier/campaigns/2026-10-14/tasks.json';JP='frontier/NEW-TEN-2026-10-14.md'
def git(*args,input=None):return subprocess.check_output(['git',*args],cwd=P,input=input)
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
base=json.loads(ht);work=json.loads(wt);assert len(base['tasks'])==len(work['tasks'])
assert base['tasks'][827]==work['tasks'][827]
assert base['newAccepted']==work['newAccepted']==19 and base['latestAcceptance']==work['latestAcceptance']=='R041'
assert base['gpt_subagent_preferences']==work['gpt_subagent_preferences'] and work['gpt_subagent_preferences']['serviceTier']=='default'
foreign=[i for i,(a,b) in enumerate(zip(base['tasks'],work['tasks'])) if a!=b];foreign_top=[k for k in base if k!='tasks' and base[k]!=work[k]]
term=json.loads((D/'task-status.json').read_bytes())['structuredContent'];assert term['taskId']==base['tasks'][827]['taskId'] and term['status']=='completed' and term['workState']=='result_available'
assert not term['hasPendingChildRuns'] and not term['hasPendingQuestion'] and term['pendingApproval'] is None
intake=json.loads((D/'intake.json').read_bytes());v=json.loads((D/'verification.json').read_bytes());baseline=json.loads((D/'intake-baseline.json').read_bytes())
assert intake['disposition']=='PREFREEZE_NO_NOMINEE' and v['status']=='MATCH' and snap(R)==json.loads((D/'private/intake/root-before.json').read_bytes())
prep=json.loads((N/'brief-preparation.json').read_bytes());brief=(P/prep['brief']).read_bytes();assert len(brief)==prep['bytes'] and sha(brief)==prep['sha256'] and len(brief.decode())<120000
dispatch=json.loads((N/'dispatch.json').read_bytes())['structuredContent']
assert dispatch['status']=='running' and dispatch['workState']=='working' and dispatch['model']=='gpt-6-astra' and dispatch['providerInstanceId']=='codex'
assert {x['id']:x['value'] for x in dispatch['options']}==dict(reasoningEffort='high',serviceTier='default')
assert not dispatch['hasPendingQuestion'] and dispatch['pendingApproval'] is None
assert prep['all_previous_literal_guards_retained'] and prep['all_extra_guard_literals_verified'] and prep['standing_bytes_preserved']==5570
client='twenty-20261025-fresh-arithmetic-r162bs-codex-astra-r1';assert not any(x.get('clientRequestId')==client for x in work['tasks'])
now=datetime.now(timezone.utc).isoformat();new_index=len(base['tasks']);fresh=copy.deepcopy(dispatch)
fresh.update(observed_utc=now,role='research',round=1,title='Arithmetic162bs: confirmed zero-entropy smooth-model obstruction discovery',clientRequestId=client,parent_thread='6742db91-d35c-44d0-a762-e5d9232f5177',target=dict(providerInstanceId='codex',model='gpt-6-astra',options=dict(reasoningEffort='high',serviceTier='default')),output='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bs/',brief=prep['brief'],brief_bytes=prep['bytes'],brief_sha256=prep['sha256'],submitted_prompt_contains_full_brief=True,source_index=152,source_family_navigation='Exact catalogue[249357,250526) contains smooth-positive-volume-model obstruction manuscript. One bounded14000-byte window decoded152/153titles and only152body;153body unread,thirdheadingboundaryonly. One root12blobs15entries11texts138943bytes;actual build/main.tex1000/Git09b361a61c2eef50cbda7f33ec652a6ac16faf43. Parent operativeproofnotread.',round_namespace='Distinct zero-entropy smooth-model obstruction family. One zero-entropy ergodic invertible nonatomic probability system excluding every smooth positive-density compact finite-dimensional model,including nonorientable/boundary,is already paid. Read all stronger actual source/primary operations before an additional claim. All old scopes and dispositions preserved.',all_previous_literal_guards_and5570_standing_bytes_retained=True,all_new_literal_guard_twins_verified_before_dispatch=True,completed_direct_inputs=5,dispatch_receipt='discovery-arithmetic-r162bs-parent/dispatch.json',prospective_isolation='discovery-arithmetic-r162bs-parent/prospective-isolation.json',prompt_length_checked_before_dispatch=True,distinct_family=True,new_author_conversation=True,independent_review=False,accepted=False,count_change=0,parent_count_at_dispatch=19,publication='STOPPED',status_provenance='Fresh async receipt confirms Codex/GPT-6 Astra/high/default. No polling,watcher or foreign liveness query.')
def update(original):
 x=copy.deepcopy(original);r=x['tasks'][827];r.update(term)
 r.update(observed_utc=now,disposition='PREFREEZE_NO_NOMINEE',theorem_frozen=False,diagnostic_frozen=False,correctness_gate=None,contribution_gate=None,parent_intake='discovery-arithmetic-r162br-parent/intake.json',parent_assessment='discovery-arithmetic-r162br-parent/assessment.md',artifact_status='MATCH',artifact_verification='discovery-arithmetic-r162br-parent/verification.json',author_inputs_unchanged=True,accepted=False,count_change=0,author_comparisons=intake['closed_author_comparisons'],unproved_directions=intake['unproved_directions'],earlier_smoothing_concern_closed=True,canonical_texts=8,canonical_text_bytes=55396,primary_pages=102,primary_acquired=10,primary_semantically_read=9,primary_papers_complete=6,primary_complete_body_pages=57,author_optional_history_traversals=0,all_old_scopes_preserved=True,status_provenance='Own terminal result queried once. Full DERIVATION,WORKING,READING-LIMITS,handoffs/verifier read. No independent mathematical gates or review retry. Artifact61payloads63files8dirs unchanged.')
 x['tasks'].append(copy.deepcopy(fresh))
 additions={'arithmetic_r162br_final_disposition':dict(observed_utc=now,task_index=827,disposition='PREFREEZE_NO_NOMINEE',closed_comparisons=intake['closed_author_comparisons'],earlier_smoothing_concern_closed=True,accepted=False,count_change=0,newAccepted=19,latestAcceptance='R041',publication='STOPPED'),'arithmetic_r162bs_dispatch':dict(task_index=new_index,taskId=dispatch['taskId'],source=152,status='running',serviceTier='default',distinct_family=True,catalogue_extent=[249357,250526],canonical_folders=1,canonical_blobs=12,canonical_entries=15,canonical_texts=11,canonical_text_bytes=138943,completed_direct_inputs=5,count_change=0,publication='STOPPED')}
 for k,value in additions.items():assert k not in x['current_work_snapshot'];x['current_work_snapshot'][k]=value
 assert [i for i,(a,b) in enumerate(zip(original['tasks'],x['tasks'])) if a!=b]==[827]
 assert all(x[k]==original[k] for k in original if k not in {'tasks','current_work_snapshot'})
 assert all(x['current_work_snapshot'][k]==a for k,a in original['current_work_snapshot'].items())
 return x
idx=enc(update(base));merged=enc(update(work))
note=('\n\n### R162BR archived; distinct smooth-model obstruction discovery — '+now+'\n\n'
+'R162BR is PREFREEZE/no nominee. Its [complete parent intake](campaigns/2026-10-14/discovery-arithmetic-r162br-parent/assessment.md) preserves the paid finite-regularity comparison on one fixed simply connected closed eleven-manifold:separate Cr maps for each finite r,zero topological entropy and H2 eigenvalue2^100. Source reset/trapping makes both attachment branches normal-constant before compatible retraction,handle/double and invariant-image assembly. Earlier smoothing concern is CLOSED. Full source homotopy action and finite-order invariant-measure dynamics are also paid. No single smooth map,invertibility,prescribed action,minimal dimension or limiting modulus is established;no alternative diagnostic was frozen. Parent read full DERIVATION29702bytes,WORKING,READING-LIMITS15578bytes,handoffs/verifier;author read8canonicaltexts55396bytes and102primarymathematicalpages across9of10acquiredPDFs,6full extracts57pages,10renders,with late reads,OCR/recovery and ancestry limits,history0 disclosed. Artifact MATCH61payloads7857185bytes63files8dirs,9pinnedblobs/3trees,10primarypairs/5completedbindings;wronganchorsrejected,authorbytes/modesunchanged. New Arithmetic162bs Source152 runs Codex/GPT-6 Astra/high/default. Exactcatalogue249357..250526,onewindow152/153titles+only152body,153bodyunread;one root12blobs15entries11texts138943bytes,actualwrapper1000bytes. Entire one-system all-finite-dimension smooth positive-volume-model obstruction is paid;parent operativeproofnotread. All guards,5570standingbytes,oldscopes and foreign uncommitted edits preserved. Campaign19/20,latestR041;publication/downstreamSTOPPED.\n').encode();nj=hj+note
for e in json.loads((N/'private/completed-direct-inputs.json').read_bytes()):
 p=P/e['path'];a=p.read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256'] and p.stat().st_mode==e['mode']
for n,s in baseline['protected'].items():assert sha((P/n).read_bytes())==s
(D/'coordination-rebase.json').write_bytes(enc(dict(intake_head=baseline['head'],integration_head=h,changed_old_tasks=[827],new_task_index=new_index,foreign_uncommitted_task_indices=foreign,foreign_uncommitted_top_fields=foreign_top,foreign_edits_preserved_and_excluded=True,journal_prefix_preserved=True,index_tasks_after_sha256=sha(idx),working_tasks_after_sha256=sha(merged),count_change=0)))
(N/'registration.json').write_bytes(enc(dict(task_index=new_index,taskId=dispatch['taskId'],status_at_dispatch='running',distinct_family=True,model_options_verified=True,count_change=0,publication='STOPPED')))
names=['intake-baseline.json','intake-prospective-isolation.json','verify-intake.py','verification.json','task-status.json','assessment.md','intake.json','prepare-next.py','integration-guard.json','manage-intake.py','coordination-rebase.json']
paths=[(D/n).relative_to(P).as_posix() for n in names]+[(N/n).relative_to(P).as_posix() for n in ['brief-preparation.json','capabilities.json','dispatch.json','prospective-isolation.json','registration.json']]+[prep['brief'],TP,JP]
assert len(paths)==len(set(paths))==19
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
subprocess.run(['git','commit','-m','Archive finite-regularity comparison and start smooth-model discovery'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip() and git('show','HEAD:openai-proof-research/'+TP)==idx and (P/TP).read_bytes()==merged
assert snap(R)==json.loads((D/'private/intake/root-before.json').read_bytes())
for n,s in baseline['protected'].items():assert sha((P/n).read_bytes())==s
print(json.dumps(dict(commit=git('rev-parse','HEAD').decode().strip(),changed_old_tasks=[827],new_task_index=new_index,staged_paths=19,foreign_edits_preserved=foreign,count=19,author_seal_unchanged=True)))
