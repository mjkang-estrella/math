#!/usr/bin/env python3
"""Archive this comparison and register one child, preserving foreign working edits."""
from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json, subprocess

P=Path(__file__).resolve().parents[4]; D=Path(__file__).resolve().parent; B=D.parent
N=B/'discovery-arithmetic-r162cg-parent'; R=B/'fresh-arithmetic-discovery-r162cf'
TP='frontier/campaigns/2026-10-14/tasks.json'; JP='frontier/NEW-TEN-2026-10-14.md'
def git(*args,input=None): return subprocess.check_output(['git',*args],cwd=P,input=input)
def sha(a): return hashlib.sha256(a).hexdigest()
def enc(x): return (json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode()
def snap(root):
 out={}
 for p in root.rglob('*'):
  assert not p.is_symlink()
  if p.is_file():
   a=p.read_bytes(); out[p.relative_to(root).as_posix()]=dict(bytes=len(a),sha256=sha(a),mode=p.stat().st_mode)
 return out

assert not git('diff','--cached','--name-only').strip()
h=git('rev-parse','HEAD').decode().strip()
ht=git('show',h+':openai-proof-research/'+TP); hj=git('show',h+':openai-proof-research/'+JP)
wt=(P/TP).read_bytes(); wj=(P/JP).read_bytes(); assert wj==hj
base=json.loads(ht); work=json.loads(wt); assert len(base['tasks'])==len(work['tasks'])
assert base['tasks'][843]==work['tasks'][843]
assert base['newAccepted']==work['newAccepted']==19 and base['latestAcceptance']==work['latestAcceptance']=='R041'
assert base['gpt_subagent_preferences']==work['gpt_subagent_preferences'] and work['gpt_subagent_preferences']['serviceTier']=='default'
foreign=[i for i,(a,b) in enumerate(zip(base['tasks'],work['tasks'])) if a!=b]
foreign_top=[k for k in base if k!='tasks' and base[k]!=work[k]]
term=json.loads((D/'task-status.json').read_bytes())['structuredContent']
assert term['taskId']==base['tasks'][843]['taskId'] and term['status']=='completed' and term['workState']=='result_available'
assert not term['hasPendingChildRuns'] and not term['hasPendingQuestion'] and term['pendingApproval'] is None
intake=json.loads((D/'intake.json').read_bytes()); v=json.loads((D/'verification.json').read_bytes())
baseline=json.loads((D/'intake-baseline.json').read_bytes())
assert intake['disposition']=='PREFREEZE_NO_NOMINEE' and v['status']=='MATCH'
assert snap(R)==json.loads((D/'private/intake/root-before.json').read_bytes())
prep=json.loads((N/'brief-preparation.json').read_bytes()); brief=(P/prep['brief']).read_bytes()
assert len(brief)==prep['bytes'] and sha(brief)==prep['sha256'] and len(brief.decode())<120000
dispatch=json.loads((N/'dispatch.json').read_bytes())['structuredContent']
assert dispatch['status']=='running' and dispatch['workState']=='working' and dispatch['model']=='gpt-6-astra' and dispatch['providerInstanceId']=='codex'
assert {x['id']:x['value'] for x in dispatch['options']}==dict(reasoningEffort='high',serviceTier='default')
assert not dispatch['hasPendingQuestion'] and dispatch['pendingApproval'] is None
assert prep['all_previous_literal_guards_retained'] and prep['all_extra_guard_literals_verified'] and prep['standing_bytes_preserved']==5570
client='twenty-20261025-fresh-arithmetic-r162cg-codex-astra-r1'
assert not any(x.get('clientRequestId')==client for x in work['tasks'])
now=datetime.now(timezone.utc).isoformat(); new_index=len(base['tasks']); fresh=copy.deepcopy(dispatch)
fresh.update(observed_utc=now,role='research',round=1,title='Arithmetic162cg: confirmed Kazhdan-Lusztig combinatorial-invariance discovery',clientRequestId=client,parent_thread='6742db91-d35c-44d0-a762-e5d9232f5177',target=dict(providerInstanceId='codex',model='gpt-6-astra',options=dict(reasoningEffort='high',serviceTier='default')),output='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cg/',brief=prep['brief'],brief_bytes=prep['bytes'],brief_sha256=prep['sha256'],submitted_prompt_contains_full_brief=True,source_index=168,source_family_navigation='Exact catalogue[269063,269890) contains Source168. One bounded14000-byte window decoded168/169titles and only168body;169body unread,thirdheadingboundaryonly. One root11blobs14entries10nonPDFtexts109980bytes;actual build/paper.tex2089/Gitaaeeea04c6c8cb25cfc6638c1bde8eacb2582004,all5mathematicalincludes2figuresbibliographyREADME. Parent operativeproofnotread.',round_namespace='Distinct from prior Source167;no exhaustive family-history clearance. Full arbitrary-Coxeter equal-parameter Kazhdan-Lusztig combinatorial invariance and stronger source operations are paid. Every older scope/disposition preserved.',all_previous_literal_guards_and5570_standing_bytes_retained=True,all_new_literal_guard_twins_verified_before_dispatch=True,completed_direct_inputs=5,dispatch_receipt='discovery-arithmetic-r162cg-parent/dispatch.json',prospective_isolation='discovery-arithmetic-r162cg-parent/prospective-isolation.json',prompt_length_checked_before_dispatch=True,distinct_family=True,new_author_conversation=True,independent_review=False,accepted=False,count_change=0,parent_count_at_dispatch=19,publication='STOPPED',status_provenance='Fresh async receipt confirms Codex/GPT-6 Astra/high/default. No polling,watcher or foreign liveness query.')

def update(original):
 x=copy.deepcopy(original); r=x['tasks'][843]; r.update(term)
 r.update(observed_utc=now,disposition='PREFREEZE_NO_NOMINEE',theorem_frozen=False,diagnostic_frozen=False,correctness_gate=None,contribution_gate=None,parent_intake='discovery-arithmetic-r162cf-parent/intake.json',parent_assessment='discovery-arithmetic-r162cf-parent/assessment.md',artifact_status='MATCH',artifact_verification='discovery-arithmetic-r162cf-parent/verification.json',author_inputs_unchanged=True,accepted=False,count_change=0,author_comparisons=intake['closed_author_comparisons'],unproved_directions=intake['unproved_directions'],canonical_texts=24,canonical_text_bytes=269725,primary_pages=122,primary_pdfs_acquired=9,primary_distinct_works=9,primary_complete_papers=7,primary_partial_papers=2,primary_visual_checks=4,author_optional_history_traversals=0,all_old_scopes_preserved=True,status_provenance='Own completed result queried once. Full DERIVATION,SOURCE-INTERFACES,WORKING,READING-LIMITS,handoffs/verifier read. No independent mathematical gates or review retry. Artifact68payloads70files14dirs unchanged; source26blobs8trees and9acquisitionPDFs authenticated. Product-law transfer is paid; actual energy-weighted sparse bands and variable-radius algebra remain uncontrolled.')
 x['tasks'].append(copy.deepcopy(fresh))
 additions={'arithmetic_r162cf_final_disposition':dict(observed_utc=now,task_index=843,disposition='PREFREEZE_NO_NOMINEE',closed_comparisons=intake['closed_author_comparisons'],unproved_directions=intake['unproved_directions'],accepted=False,count_change=0,newAccepted=19,latestAcceptance='R041',publication='STOPPED'),'arithmetic_r162cg_dispatch':dict(task_index=new_index,taskId=dispatch['taskId'],source=168,status='running',serviceTier='default',distinct_from_previous_family=True,catalogue_extent=[269063,269890],canonical_folders=1,canonical_blobs=11,canonical_entries=14,canonical_texts=10,canonical_text_bytes=109980,completed_direct_inputs=5,count_change=0,publication='STOPPED')}
 for k,value in additions.items():
  assert k not in x['current_work_snapshot']; x['current_work_snapshot'][k]=value
 assert [i for i,(a,b) in enumerate(zip(original['tasks'],x['tasks'])) if a!=b]==[843]
 assert all(x[k]==original[k] for k in original if k not in {'tasks','current_work_snapshot'})
 assert all(x['current_work_snapshot'][k]==a for k,a in original['current_work_snapshot'].items())
 return x

idx=enc(update(base)); merged=enc(update(work))
note=('\n\n### R162CF archived; Kazhdan-Lusztig discovery — '+now+'\n\n'
+'R162CF is PREFREEZE/no nominee. Its [complete parent intake](campaigns/2026-10-14/discovery-arithmetic-r162cf-parent/assessment.md) retains hereditary exceptional-pin bounds,unit sampling,centered-circle/bisector comparisons,fixed-c tail integration with its linear incidence term,and full small-atom product-law transfer by Bernoulli sampling as paid operations. Energy-weighted sparse bands and variable-radius derivative/discriminant terms remain unproved. A seven-point example rejects one radius-factor shortcut only. No theorem/diagnostic frozen or mathematical gate/count increment. Parent read full DERIVATION23362bytes,SOURCE-INTERFACES11242bytes,WORKING4038bytes,READING-LIMITS9364bytes,handoffs/verifier. Author read24canonicaltexts269725bytes,122primarypages9PDFs7full2partial,4visualchecks,5completedexceptions,history0;late corrections,encoding/recovery and ancestry limits disclosed. Artifact MATCH68payloads8062087bytes70files14dirs,26blobs8trees,9primaryPDFbindings/5completedpairs;threewronganchorsrejected,allauthorbytes/modesunchanged. Arithmetic162cg now uses distinct Source168, Codex/GPT-6 Astra/high/default. Exactcatalogue269063..269890,onewindow168/169titles+only168body,169bodyunread. One root11blobs14entries10texts109980bytes,actualpaper.tex2089bytes andall5includes pinned. Full combinatorial invariance and stronger operative proofs paid. All guards,5570standingbytes,older scopes and foreign working edits preserved. Campaign19/20,latestR041;publication/downstreamSTOPPED.\n').encode()
nj=hj+note
for e in json.loads((N/'private/completed-direct-inputs.json').read_bytes()):
 p=P/e['path']; a=p.read_bytes()
 assert len(a)==e['bytes'] and sha(a)==e['sha256'] and p.stat().st_mode==e['mode']
for n,s in baseline['protected'].items(): assert sha((P/n).read_bytes())==s
(D/'coordination-rebase.json').write_bytes(enc(dict(intake_head=baseline['head'],integration_head=h,changed_old_tasks=[843],new_task_index=new_index,foreign_uncommitted_task_indices=foreign,foreign_uncommitted_top_fields=foreign_top,foreign_edits_preserved_and_excluded=True,journal_prefix_preserved=True,index_tasks_after_sha256=sha(idx),working_tasks_after_sha256=sha(merged),count_change=0)))
(N/'registration.json').write_bytes(enc(dict(task_index=new_index,taskId=dispatch['taskId'],status_at_dispatch='running',distinct_family=True,model_options_verified=True,count_change=0,publication='STOPPED')))
names=['intake-baseline.json','intake-prospective-isolation.json','verify-intake.py','verification.json','task-status.json','assessment.md','intake.json','prepare-next.py','integration-guard.json','manage-intake.py','coordination-rebase.json']
paths=[(D/n).relative_to(P).as_posix() for n in names]+[(N/n).relative_to(P).as_posix() for n in ['brief-preparation.json','capabilities.json','dispatch.json','prospective-isolation.json','registration.json']]+[prep['brief'],TP,JP]
assert len(paths)==len(set(paths))==19
assert git('rev-parse','HEAD').decode().strip()==h and (P/TP).read_bytes()==wt and (P/JP).read_bytes()==wj and not git('diff','--cached','--name-only').strip()
(P/TP).write_bytes(merged); (P/JP).write_bytes(nj)
subprocess.run(['git','add','--',*[n for n in paths if n!=TP]],cwd=P,check=True)
blob=git('hash-object','-w','--stdin',input=idx).decode().strip()
subprocess.run(['git','update-index','--add','--cacheinfo','100644',blob,'openai-proof-research/'+TP],cwd=P,check=True)
assert {n for n in git('diff','--cached','--name-only','-z').decode().split('\0') if n}=={'openai-proof-research/'+n for n in paths}
assert git('show',':openai-proof-research/'+TP)==idx
for n in paths:
 if n!=TP: assert git('show',':openai-proof-research/'+n)==(P/n).read_bytes()
subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
assert git('rev-parse','HEAD').decode().strip()==h and (P/TP).read_bytes()==merged and (P/JP).read_bytes()==nj
subprocess.run(['git','commit','-m','Archive planar geometry comparisons and start Kazhdan-Lusztig discovery'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip() and git('show','HEAD:openai-proof-research/'+TP)==idx and (P/TP).read_bytes()==merged
assert snap(R)==json.loads((D/'private/intake/root-before.json').read_bytes())
for n,s in baseline['protected'].items(): assert sha((P/n).read_bytes())==s
print(json.dumps(dict(commit=git('rev-parse','HEAD').decode().strip(),changed_old_tasks=[843],new_task_index=new_index,staged_paths=19,foreign_edits_preserved=foreign,count=19,author_seal_unchanged=True)))
