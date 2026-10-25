#!/usr/bin/env python3
"""Archive this comparison and register one child, preserving foreign working edits."""
from pathlib import Path
from datetime import datetime, timezone
import copy, hashlib, json, subprocess

P=Path(__file__).resolve().parents[4]; D=Path(__file__).resolve().parent; B=D.parent
N=B/'discovery-arithmetic-r162ch-parent'; R=B/'fresh-arithmetic-discovery-r162cg'
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
assert base['tasks'][844]==work['tasks'][844]
assert base['newAccepted']==work['newAccepted']==19 and base['latestAcceptance']==work['latestAcceptance']=='R041'
assert base['gpt_subagent_preferences']==work['gpt_subagent_preferences'] and work['gpt_subagent_preferences']['serviceTier']=='default'
foreign=[i for i,(a,b) in enumerate(zip(base['tasks'],work['tasks'])) if a!=b]
foreign_top=[k for k in base if k!='tasks' and base[k]!=work[k]]
term=json.loads((D/'task-status.json').read_bytes())['structuredContent']
assert term['taskId']==base['tasks'][844]['taskId'] and term['status']=='completed' and term['workState']=='result_available'
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
client='twenty-20261025-fresh-arithmetic-r162ch-codex-astra-r1'
assert not any(x.get('clientRequestId')==client for x in work['tasks'])
now=datetime.now(timezone.utc).isoformat(); new_index=len(base['tasks']); fresh=copy.deepcopy(dispatch)
fresh.update(observed_utc=now,role='research',round=1,title='Arithmetic162ch: confirmed chromatic-quasisymmetric elementary-positivity discovery',clientRequestId=client,parent_thread='6742db91-d35c-44d0-a762-e5d9232f5177',target=dict(providerInstanceId='codex',model='gpt-6-astra',options=dict(reasoningEffort='high',serviceTier='default')),output='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ch/',brief=prep['brief'],brief_bytes=prep['bytes'],brief_sha256=prep['sha256'],submitted_prompt_contains_full_brief=True,source_index=169,source_family_navigation='Exact catalogue[269890,270748) contains Source169. One bounded14000-byte window decoded169/170titles and only169body;170body unread,thirdheadingboundaryonly. One root11blobs14entries10nonPDFtexts182105bytes;actual build/paper.tex2283/Git25797b655fe92033108f7ef9d2416079b71c20a3,all7mathematicalsectionincludes,bibliography,README. Parent operativeproofnotread.',round_namespace='Distinct from prior Source168;no exhaustive family-history clearance. Full elementary positivity over N[q] for natural unit interval graphs,explicit permutation interpretation and stronger source operations are paid. Every older scope/disposition preserved.',all_previous_literal_guards_and5570_standing_bytes_retained=True,all_new_literal_guard_twins_verified_before_dispatch=True,completed_direct_inputs=5,dispatch_receipt='discovery-arithmetic-r162ch-parent/dispatch.json',prospective_isolation='discovery-arithmetic-r162ch-parent/prospective-isolation.json',prompt_length_checked_before_dispatch=True,distinct_family=True,new_author_conversation=True,independent_review=False,accepted=False,count_change=0,parent_count_at_dispatch=19,publication='STOPPED',status_provenance='Fresh async receipt confirms Codex/GPT-6 Astra/high/default. No polling,watcher or foreign liveness query.')

def update(original):
 x=copy.deepcopy(original); r=x['tasks'][844]; r.update(term)
 r.update(observed_utc=now,disposition='PREFREEZE_NO_NOMINEE',theorem_frozen=False,diagnostic_frozen=False,correctness_gate=None,contribution_gate=None,parent_intake='discovery-arithmetic-r162cg-parent/intake.json',parent_assessment='discovery-arithmetic-r162cg-parent/assessment.md',artifact_status='MATCH',artifact_verification='discovery-arithmetic-r162cg-parent/verification.json',author_inputs_unchanged=True,accepted=False,count_change=0,author_comparisons=intake['closed_author_comparisons'],unproved_directions=intake['unproved_directions'],canonical_texts=10,canonical_text_bytes=109980,primary_pages=173,primary_pdfs_acquired=9,primary_distinct_works=8,primary_complete_papers=6,primary_partial_papers=2,primary_visual_checks=4,author_optional_history_traversals=0,all_old_scopes_preserved=True,status_provenance='Own completed result queried once. Full DERIVATION,SOURCE-INTERFACES,WORKING,READING-LIMITS,handoffs/verifier read. No independent mathematical gates or review retry. Artifact59payloads61files8dirs unchanged; source11blobs3trees and9acquisitionPDFs authenticated. General same-ideal weighted aggregate remains unproved; the bounded example satisfies that identity while rejecting specified stronger shortcuts.')
 x['tasks'].append(copy.deepcopy(fresh))
 additions={'arithmetic_r162cg_final_disposition':dict(observed_utc=now,task_index=844,disposition='PREFREEZE_NO_NOMINEE',closed_comparisons=intake['closed_author_comparisons'],unproved_directions=intake['unproved_directions'],accepted=False,count_change=0,newAccepted=19,latestAcceptance='R041',publication='STOPPED'),'arithmetic_r162ch_dispatch':dict(task_index=new_index,taskId=dispatch['taskId'],source=169,status='running',serviceTier='default',distinct_from_previous_family=True,catalogue_extent=[269890,270748],canonical_folders=1,canonical_blobs=11,canonical_entries=14,canonical_texts=10,canonical_text_bytes=182105,completed_direct_inputs=5,count_change=0,publication='STOPPED')}
 for k,value in additions.items():
  assert k not in x['current_work_snapshot']; x['current_work_snapshot'][k]=value
 assert [i for i,(a,b) in enumerate(zip(original['tasks'],x['tasks'])) if a!=b]==[844]
 assert all(x[k]==original[k] for k in original if k not in {'tasks','current_work_snapshot'})
 assert all(x['current_work_snapshot'][k]==a for k,a in original['current_work_snapshot'].items())
 return x

idx=enc(update(base)); merged=enc(update(work))
note=('\n\n### R162CG archived; chromatic-quasisymmetric positivity discovery — '+now+'\n\n'
+'R162CG is PREFREEZE/no nominee. Its [complete parent intake](campaigns/2026-10-14/discovery-arithmetic-r162cg-parent/assessment.md) preserves the same-interval relative incidence discrepancy and full antichain q-weights. General weighted aggregate cancellation for the supplied hypercube ideal remains unproved;the bounded S6 example satisfies that identity and rejects only specified unweighted,rowwise and singleton shortcuts. Stronger source and actual primary operations are paid. No theorem/diagnostic frozen or mathematical gate/count increment. Parent read full DERIVATION22367bytes,SOURCE-INTERFACES10798bytes,WORKING3221bytes,READING-LIMITS9767bytes,handoffs/verifier. Author read10canonicaltexts109980bytes,173primarypages6full2partial,4visualchecks,5completedexceptions,history0;one of9acquiredPDFs authentication-only,ancestry and late-read/mode limits disclosed. Artifact MATCH59payloads11489291bytes61files8dirs,11blobs3trees,9primaryPDFbindings/5completedpairs;threewronganchorsrejected,allauthorbytes/modesunchanged. Arithmetic162ch now uses distinct Source169, Codex/GPT-6 Astra/high/default. Exactcatalogue269890..270748,onewindow169/170titles+only169body,170bodyunread. One root11blobs14entries10texts182105bytes,actualpaper.tex2283bytes andall7includes pinned. Full elementary positivity,permutation interpretation and stronger operative proofs paid. All guards,5570standingbytes,older scopes and foreign working edits preserved. Campaign19/20,latestR041;publication/downstreamSTOPPED.\n').encode()
nj=hj+note
for e in json.loads((N/'private/completed-direct-inputs.json').read_bytes()):
 p=P/e['path']; a=p.read_bytes()
 assert len(a)==e['bytes'] and sha(a)==e['sha256'] and p.stat().st_mode==e['mode']
for n,s in baseline['protected'].items(): assert sha((P/n).read_bytes())==s
(D/'coordination-rebase.json').write_bytes(enc(dict(intake_head=baseline['head'],integration_head=h,changed_old_tasks=[844],new_task_index=new_index,foreign_uncommitted_task_indices=foreign,foreign_uncommitted_top_fields=foreign_top,foreign_edits_preserved_and_excluded=True,journal_prefix_preserved=True,index_tasks_after_sha256=sha(idx),working_tasks_after_sha256=sha(merged),count_change=0)))
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
subprocess.run(['git','commit','-m','Archive weighted KL comparisons and start elementary-positivity discovery'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip() and git('show','HEAD:openai-proof-research/'+TP)==idx and (P/TP).read_bytes()==merged
assert snap(R)==json.loads((D/'private/intake/root-before.json').read_bytes())
for n,s in baseline['protected'].items(): assert sha((P/n).read_bytes())==s
print(json.dumps(dict(commit=git('rev-parse','HEAD').decode().strip(),changed_old_tasks=[844],new_task_index=new_index,staged_paths=19,foreign_edits_preserved=foreign,count=19,author_seal_unchanged=True)))
