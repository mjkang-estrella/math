#!/usr/bin/env python3
"""Close PASS/TECHNICAL without a count, then register distinct discovery."""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
R=B/'arithmetic-r162cb-proof-r1';N=B/'discovery-arithmetic-r162cc-parent'
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
assert all(base['tasks'][i]==work['tasks'][i] for i in [837,838,839])
assert base['newAccepted']==work['newAccepted']==19 and base['latestAcceptance']==work['latestAcceptance']=='R041'
assert base['gpt_subagent_preferences']==work['gpt_subagent_preferences'] and work['gpt_subagent_preferences']['serviceTier']=='default'
foreign=[i for i,(a,b) in enumerate(zip(base['tasks'],work['tasks'])) if a!=b];foreign_top=[k for k in base if k!='tasks' and base[k]!=work[k]]
term=json.loads((D/'task-status.json').read_bytes())['structuredContent']
assert term['taskId']==base['tasks'][838]['taskId'] and term['status']=='completed' and term['workState']=='result_available'
assert not term['hasPendingChildRuns'] and not term['hasPendingQuestion'] and term['pendingApproval'] is None
intake=json.loads((D/'intake.json').read_bytes());baseline=json.loads((D/'baseline.json').read_bytes())
assert intake['correctness_verdict']=='PASS' and intake['contribution_verdict']=='TECHNICAL' and intake['contribution_condition_discharged']
assert intake['verification']['status']=='MATCH' and snap(R)==json.loads((D/'private/root-before.json').read_bytes())
assert snap(B/'fresh-arithmetic-discovery-r162cb')==json.loads((B/'discovery-arithmetic-r162cb-parent/private/intake/root-before.json').read_bytes())
assert snap(B/'arithmetic-r162cb-contribution-r1')==json.loads((B/'arithmetic-r162cb-contribution-r1-parent/private/root-before.json').read_bytes())
prep=json.loads((N/'brief-preparation.json').read_bytes());brief=(P/prep['brief']).read_bytes()
assert len(brief)==prep['bytes'] and sha(brief)==prep['sha256'] and len(brief.decode())<120000
assert prep['all_previous_literal_guards_retained'] and prep['all_extra_guard_literals_verified'] and prep['standing_bytes_preserved']==5570
dispatch=json.loads((N/'dispatch.json').read_bytes())['structuredContent']
assert dispatch['status']=='running' and dispatch['workState']=='working' and dispatch['model']=='gpt-6-astra' and dispatch['providerInstanceId']=='codex'
assert {o['id']:o['value'] for o in dispatch['options']}==dict(reasoningEffort='high',serviceTier='default')
assert not dispatch['hasPendingQuestion'] and dispatch['pendingApproval'] is None
client='twenty-20261025-fresh-arithmetic-r162cc-codex-astra-r1';assert not any(x.get('clientRequestId')==client for x in work['tasks'])
now=datetime.now(timezone.utc).isoformat();new_index=len(base['tasks']);fresh=copy.deepcopy(dispatch)
fresh.update(observed_utc=now,role='research',round=1,title='Arithmetic162cc: confirmed finite sums and products discovery',clientRequestId=client,parent_thread='6742db91-d35c-44d0-a762-e5d9232f5177',target=dict(providerInstanceId='codex',model='gpt-6-astra',options=dict(reasoningEffort='high',serviceTier='default')),output='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cc/',brief=prep['brief'],brief_bytes=prep['bytes'],brief_sha256=prep['sha256'],submitted_prompt_contains_full_brief=True,source_index=164,source_family_navigation='Actual Source164 occupies catalogue[264581,265378). Previous navigation inferred163; corrected by reading actual header. One bounded14000-byte window,only164body and164/165titles decoded; recovery exposed numeric heading boundaries and first120rawbytes of same family. Source165 body unread. One root12blobs15entries11texts261554bytes;actual build/main.tex2812/Git4c2e967a362b78eca7517cdb8c8182a2b3259ceb. No parent operative-proof reading.',round_namespace='Distinct from previous Source162 Ryser family,now closed PASS/TECHNICAL with zero increment. Entire finite sums/products source theorem and stronger actual operations paid. All older scopes immutable.',all_previous_literal_guards_and5570_standing_bytes_retained=True,all_new_literal_guard_twins_verified_before_dispatch=True,completed_direct_inputs=5,dispatch_receipt='discovery-arithmetic-r162cc-parent/dispatch.json',prospective_isolation='discovery-arithmetic-r162cc-parent/prospective-isolation.json',prompt_length_checked_before_dispatch=True,distinct_family=True,new_author_conversation=True,independent_review=False,accepted=False,count_change=0,parent_count_at_dispatch=19,publication='STOPPED',status_provenance='Fresh async receipt confirms Codex/GPT-6 Astra/high/default; no polling or foreign liveness query.')
def update(original):
 x=copy.deepcopy(original);r=x['tasks'][838];r.update(term)
 r.update(observed_utc=now,verdict='PASS',scope='entire unchanged frozen theorem',stipulated_upstream=True,correctness_obligations_remaining=[],accepted=False,count_change=0,parent_intake='arithmetic-r162cb-proof-r1-parent/intake.json',parent_assessment='arithmetic-r162cb-proof-r1-parent/assessment.md',artifact_status='MATCH',artifact_verification='arithmetic-r162cb-proof-r1-parent/verification.json',author_files_unchanged=61,status_provenance='Own terminal result queried once; full derivations,limits,handoff and verifier read. No contribution regrading or author repair.')
 x['tasks'][837].update(disposition='CORRECT_TECHNICAL_CLOSED',correctness_gate='PASS',correctness_review_task_index=838,contribution_gate='TECHNICAL',contribution_condition_discharged=True,accepted=False,count_change=0,author_inputs_unchanged=True)
 x['tasks'][839].update(contribution_condition_discharged=True,correctness_dependency_task_index=838,accepted=False,count_change=0)
 x['tasks'].append(copy.deepcopy(fresh))
 additions={'arithmetic_r162cb_final_disposition':dict(observed_utc=now,author_task_index=837,correctness='PASS',contribution='TECHNICAL',contribution_condition_discharged=True,accepted=False,count_change=0,newAccepted=19,latestAcceptance='R041'),'arithmetic_r162cc_dispatch':dict(task_index=new_index,taskId=dispatch['taskId'],source=164,status='running',serviceTier='default',distinct_from_previous_family=True,catalogue_extent=[264581,265378],canonical_blobs=12,canonical_texts=11,canonical_text_bytes=261554,count_change=0,publication='STOPPED')}
 for k,v in additions.items():assert k not in x['current_work_snapshot'];x['current_work_snapshot'][k]=v
 assert [i for i,(a,b) in enumerate(zip(original['tasks'],x['tasks'])) if a!=b]==[837,838,839]
 assert all(x[k]==original[k] for k in original if k not in {'tasks','current_work_snapshot'})
 assert all(x['current_work_snapshot'][k]==v for k,v in original['current_work_snapshot'].items())
 return x
idx=enc(update(base));merged=enc(update(work))
note=('\n\n### R162CB closed PASS / TECHNICAL; finite sums/products discovery — '+now+'\n\n'
+'The [independent correctness review](campaigns/2026-10-14/arithmetic-r162cb-proof-r1/FINAL.md) passes every unchanged frozen Ryser assertion relative to stipulated Source162. The prior full-scope contribution verdict is TECHNICAL;its correctness condition is now discharged. No repair or mathematical obligation remains,all61authorfiles and both review packets are unchanged,and the campaign increment is zero. Parent read complete correctness derivations12549bytes,limits9951bytes,verdict/report/verifier. Reviewer read18canonicaltexts291598bytes and40primarypages,with incomplete ancestry/reading limits disclosed. Read-only artifact MATCH55payloads4148157bytes57files14dirs;wronganchors rejected. New Arithmetic162cc Source164 finite-sums/products research runs Codex/GPT-6 Astra/high/default. Actual catalogue numbering164 corrected from an inferred163 label;only actual164body and164/165titles decoded,source165body unread. One root12blobs15entries11texts261554bytes,actualwrapper2812bytes pinned. Full source theorem and stronger operations paid. A stale copied guard suffix was caught before creation/dispatch and both next-round r/no-r twins corrected;all inherited literals and5570standingbytes retained. All old scopes and foreign edits preserved. Campaign19/20,latestR041;publication/downstreamSTOPPED.\n').encode();nj=hj+note
for e in json.loads((N/'private/completed-direct-inputs.json').read_bytes()):
 p=P/e['path'];a=p.read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256'] and p.stat().st_mode==e['mode']
for n,s in baseline['protected'].items():assert sha((P/n).read_bytes())==s
(D/'coordination-rebase.json').write_bytes(enc(dict(intake_head=baseline['head'],integration_head=h,changed_old_tasks=[837,838,839],new_task_index=new_index,foreign_uncommitted_task_indices=foreign,foreign_uncommitted_top_fields=foreign_top,foreign_edits_preserved_and_excluded=True,index_tasks_after_sha256=sha(idx),working_tasks_after_sha256=sha(merged),count_change=0)))
(N/'registration.json').write_bytes(enc(dict(task_index=new_index,taskId=dispatch['taskId'],status_at_dispatch='running',distinct_family=True,model_options_verified=True,count_change=0,publication='STOPPED')))
names=['baseline.json','prospective-isolation.json','task-status.json','verify-intake.py','verification.json','assessment.md','intake.json','prepare-next.py','integration-guard.json','manage-intake.py','coordination-rebase.json']
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
subprocess.run(['git','commit','-m','Close correct technical Ryser result and start sums-products discovery'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip() and git('show','HEAD:openai-proof-research/'+TP)==idx and (P/TP).read_bytes()==merged
assert snap(R)==json.loads((D/'private/root-before.json').read_bytes())
assert snap(B/'fresh-arithmetic-discovery-r162cb')==json.loads((B/'discovery-arithmetic-r162cb-parent/private/intake/root-before.json').read_bytes())
for n,s in baseline['protected'].items():assert sha((P/n).read_bytes())==s
print(json.dumps(dict(commit=git('rev-parse','HEAD').decode().strip(),changed_old_tasks=[837,838,839],new_task_index=new_index,staged_paths=19,foreign_edits_preserved=foreign,count=19,author_and_reviews_unchanged=True)))
