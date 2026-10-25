"""Adopt correctness verdict and register blind contribution review; count unchanged."""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
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
wt=(P/TP).read_bytes();wj=(P/JP).read_bytes();base=json.loads(ht);work=json.loads(wt)
assert len(base['tasks'])==len(work['tasks'])==855 and all(base['tasks'][i]==work['tasks'][i] for i in [853,854])
assert base['newAccepted']==work['newAccepted']==19 and base['latestAcceptance']==work['latestAcceptance']=='R041'
assert base['gpt_subagent_preferences']==work['gpt_subagent_preferences'] and work['gpt_subagent_preferences']['serviceTier']=='default'
foreign=[i for i,(a,b) in enumerate(zip(base['tasks'],work['tasks'])) if a!=b];foreign_top=[k for k in base if k!='tasks' and base[k]!=work[k]]
term=json.loads((D/'proof-task-status.json').read_bytes())['structuredContent'];assert term['taskId']==base['tasks'][854]['taskId'] and term['status']=='completed' and term['workState']=='result_available'
assert not term['hasPendingChildRuns'] and not term['hasPendingQuestion'] and term['pendingApproval'] is None
assert json.loads((D/'proof-verification.json').read_bytes())['status']=='MATCH'
assert snap(B/'arithmetic-r162cp-proof-r1')==json.loads((D/'private/proof-intake/root-before.json').read_bytes()) and snap(B/'fresh-arithmetic-discovery-r162cp')==json.loads((D/'private/proof-intake/author-before.json').read_bytes())
prep=json.loads((D/'review-preparation.json').read_bytes());c=next(x for x in prep['reviews'] if x['role']=='contribution');brief=(P/c['brief']).read_bytes();assert len(brief)==c['bytes'] and sha(brief)==c['sha256'] and c['all_inherited_literal_guards_retained']
dispatch=json.loads((D/'contribution-dispatch.json').read_bytes())['structuredContent'];assert dispatch['status']=='running' and dispatch['workState']=='working' and dispatch['providerInstanceId']=='codex' and dispatch['model']=='gpt-6-astra'
assert {x['id']:x['value'] for x in dispatch['options']}==dict(reasoningEffort='high',serviceTier='default') and not dispatch['hasPendingQuestion'] and dispatch['pendingApproval'] is None
client='twenty-20261025-arithmetic-r162cp-contribution-codex-astra-r1';assert not any(x.get('clientRequestId')==client for x in work['tasks'])
now=datetime.now(timezone.utc).isoformat();new_index=len(base['tasks']);fresh=copy.deepcopy(dispatch)
fresh.update(observed_utc=now,role='review',review_dimension='substantial_contribution',round=1,title='R162CP: independent full substantial-contribution review',clientRequestId=client,parent_thread='6742db91-d35c-44d0-a762-e5d9232f5177',target=dict(providerInstanceId='codex',model='gpt-6-astra',options=dict(reasoningEffort='high',serviceTier='default')),output=c['root']+'/',brief=c['brief'],brief_bytes=c['bytes'],brief_sha256=c['sha256'],submitted_prompt_contains_full_brief=True,source_index=177,nominee='R162CP',frozen_statement_sha256='ebbecfde0342e866f1401764980ccaf1f3f0c08bc1aea5269e217021774594c9',frozen_proof_sha256='7331535f72a9c9dbab2da0396af34c78eb0a1065afb5e96d4cfc618a22a052b6',author_input_count=68,author_input_manifest='discovery-arithmetic-r162cp-parent/private/review-inputs.json',independent_review=True,peer_review_inspection=False,peer_verdict_supplied=False,conditional_on_correctness=True,accepted=False,count_change=0,parent_count_at_dispatch=19,publication='STOPPED',dispatch_receipt='discovery-arithmetic-r162cp-parent/contribution-dispatch.json',status_provenance='Fresh async receipt,standard service. Exact contribution brief prepared before proof verdict and dispatched unchanged. No peer evidence or verdict in task. No polling.')
def update(original):
 x=copy.deepcopy(original)
 x['tasks'][853].update(observed_utc=now,disposition='CORRECTNESS_PASS_CONTRIBUTION_PENDING',correctness_gate='PASS',contribution_gate=None,correctness_review='arithmetic-r162cp-proof-r1/REVIEW.md',proof_parent_assessment='discovery-arithmetic-r162cp-parent/proof-assessment.md',accepted=False,count_change=0)
 r=x['tasks'][854];r.update(term);r.update(observed_utc=now,verdict='PASS',review_dimension='correctness',entire_unchanged_scope=True,essential_unresolved_obligations=False,author_inputs_unchanged=True,parent_assessment='discovery-arithmetic-r162cp-parent/proof-assessment.md',artifact_status='MATCH',artifact_verification='discovery-arithmetic-r162cp-parent/proof-verification.json',canonical_texts=9,canonical_text_bytes=52577,primary_pages=10,primary_source='Khot-Naor author-hosted pages1-10;all essential new steps reconstructed',optional_history_traversals=0,accepted=False,count_change=0,contribution_gate=None)
 x['tasks'].append(copy.deepcopy(fresh))
 adds={'arithmetic_r162cp_correctness_intake':dict(observed_utc=now,task_index=854,verdict='PASS',entire_unchanged_scope=True,source_truth_stipulated=True,unresolved_essential_obligations=False,artifact_status='MATCH',count_change=0),'arithmetic_r162cp_contribution_dispatch':dict(task_index=new_index,taskId=dispatch['taskId'],status='running',serviceTier='default',entire_unchanged_scope=True,brief_unchanged_since_before_proof_verdict=True,peer_verdict_supplied=False,count_change=0)}
 for k,value in adds.items():assert k not in x['current_work_snapshot'];x['current_work_snapshot'][k]=value
 assert [i for i,(a,b) in enumerate(zip(original['tasks'],x['tasks'])) if a!=b]==[853,854]
 assert all(x[k]==original[k] for k in original if k not in {'tasks','current_work_snapshot'}) and all(x['current_work_snapshot'][k]==a for k,a in original['current_work_snapshot'].items())
 return x
idx=enc(update(base));merged=enc(update(work))
note=('\n\n### R162CP correctness PASS; blind contribution review — '+now+'\n\n'
'[Correctness intake](campaigns/2026-10-14/discovery-arithmetic-r162cp-parent/proof-assessment.md):the independent review establishes the entire unchanged frozen theorem under stipulated Source177 truth,no repair or essential unresolved obligation. It reconstructs original weighted incidence/orbit data,arbitrary-law affine Fourier support,fixed-pair quantifiers,full-tail constants,common-cut marginals and S/U/R comparisons. Actual reviewer reading:all required author texts,9source texts52577bytes,KN10primarypages;other contribution ancestry unreviewed. Parent read full REVIEW/private derivation/reading records,handoffs/verifier. Review artifact MATCH19payloads88806bytes21files;three anchors/wrong-anchor rejections,all68author bytes/full modes unchanged. Review manifest binds file modes,not directory modes. New substantial-contribution review Codex/GPT-6 Astra/high/default uses the exact preprepared brief without correctness verdict or peer access,entire unchanged scope,conditional on correctness. No contribution grade or acceptance yet. Campaign19/20,latestR041;publication/downstreamSTOPPED.\n').encode()
ij=hj+note;mj=wj+note
baseline=json.loads((D/'intake-baseline.json').read_bytes())
for n,s in baseline['protected'].items():assert sha((P/n).read_bytes())==s
(D/'proof-coordination-rebase.json').write_bytes(enc(dict(integration_head=h,changed_old_tasks=[853,854],new_task_index=new_index,foreign_uncommitted_task_indices=foreign,foreign_uncommitted_top_fields=foreign_top,foreign_edits_preserved_and_excluded=True,foreign_journal_preserved_and_excluded=wj!=hj,index_tasks_sha256=sha(idx),working_tasks_sha256=sha(merged),index_journal_sha256=sha(ij),working_journal_sha256=sha(mj),count_change=0)))
(D/'contribution-registration.json').write_bytes(enc(dict(task_index=new_index,taskId=dispatch['taskId'],status_at_dispatch='running',brief_unchanged=True,peer_verdict_supplied=False,count_change=0)))
names=['proof-intake-baseline.json','proof-task-status.json','verify-proof-intake.py','proof-verification.json','proof-assessment.md','contribution-dispatch.json','manage-proof-intake.py','proof-coordination-rebase.json','contribution-registration.json']
paths=[(D/n).relative_to(P).as_posix() for n in names]+[TP,JP];assert len(paths)==len(set(paths))==11
assert git('rev-parse','HEAD').decode().strip()==h and (P/TP).read_bytes()==wt and (P/JP).read_bytes()==wj and not git('diff','--cached','--name-only').strip()
(P/TP).write_bytes(merged);(P/JP).write_bytes(mj);subprocess.run(['git','add','--',*[n for n in paths if n not in {TP,JP}]],cwd=P,check=True)
for path,content in [(TP,idx),(JP,ij)]:
 blob=git('hash-object','-w','--stdin',input=content).decode().strip();subprocess.run(['git','update-index','--add','--cacheinfo','100644',blob,'openai-proof-research/'+path],cwd=P,check=True)
assert {n for n in git('diff','--cached','--name-only','-z').decode().split('\0') if n}=={'openai-proof-research/'+n for n in paths}
assert git('show',':openai-proof-research/'+TP)==idx and git('show',':openai-proof-research/'+JP)==ij
for n in paths:
 if n not in {TP,JP}:assert git('show',':openai-proof-research/'+n)==(P/n).read_bytes()
subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
assert git('rev-parse','HEAD').decode().strip()==h and (P/TP).read_bytes()==merged and (P/JP).read_bytes()==mj
subprocess.run(['git','commit','-m','Record full correctness pass and start independent contribution review'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip() and git('show','HEAD:openai-proof-research/'+TP)==idx and (P/TP).read_bytes()==merged and git('show','HEAD:openai-proof-research/'+JP)==ij and (P/JP).read_bytes()==mj
assert snap(B/'arithmetic-r162cp-proof-r1')==json.loads((D/'private/proof-intake/root-before.json').read_bytes()) and snap(B/'fresh-arithmetic-discovery-r162cp')==json.loads((D/'private/proof-intake/author-before.json').read_bytes())
print(json.dumps(dict(commit=git('rev-parse','HEAD').decode().strip(),changed_old_tasks=[853,854],new_task_index=new_index,staged_paths=11,foreign_edits_preserved=foreign,foreign_journal_preserved=wj!=hj,count=19,author_and_review_unchanged=True)))
