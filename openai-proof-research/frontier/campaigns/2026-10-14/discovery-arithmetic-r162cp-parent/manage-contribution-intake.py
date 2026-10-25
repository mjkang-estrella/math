"""Close CP as PASS/TECHNICAL and register fresh discovery; preserve foreign edits."""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent;N=B/'discovery-arithmetic-r162cq-parent'
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
assert len(base['tasks'])==len(work['tasks'])==856 and all(base['tasks'][i]==work['tasks'][i] for i in [853,855])
assert base['newAccepted']==work['newAccepted']==19 and base['latestAcceptance']==work['latestAcceptance']=='R041'
assert base['gpt_subagent_preferences']==work['gpt_subagent_preferences'] and work['gpt_subagent_preferences']['serviceTier']=='default'
assert base['tasks'][853]['correctness_gate']=='PASS' and base['tasks'][854]['verdict']=='PASS'
foreign=[i for i,(a,b) in enumerate(zip(base['tasks'],work['tasks'])) if a!=b];foreign_top=[k for k in base if k!='tasks' and base[k]!=work[k]]
term=json.loads((D/'contribution-task-status.json').read_bytes())['structuredContent'];assert term['taskId']==base['tasks'][855]['taskId'] and term['status']=='completed' and term['workState']=='result_available'
assert not term['hasPendingChildRuns'] and not term['hasPendingQuestion'] and term['pendingApproval'] is None
intake=json.loads((D/'contribution-intake.json').read_bytes());v=json.loads((D/'contribution-verification.json').read_bytes());assert intake['disposition']=='CLOSED_PASS_TECHNICAL' and intake['condition_discharged'] and v['status']=='MATCH'
assert snap(B/'arithmetic-r162cp-contribution-r1')==json.loads((D/'private/contribution-intake/root-before.json').read_bytes()) and snap(B/'fresh-arithmetic-discovery-r162cp')==json.loads((D/'private/contribution-intake/author-before.json').read_bytes())
prep=json.loads((N/'brief-preparation.json').read_bytes());brief=(P/prep['brief']).read_bytes();assert len(brief)==prep['bytes'] and sha(brief)==prep['sha256'] and len(brief.decode())<120000 and prep['all_previous_literal_guards_retained'] and prep['all_extra_guard_literals_verified']
dispatch=json.loads((N/'dispatch.json').read_bytes())['structuredContent'];assert dispatch['status']=='running' and dispatch['workState']=='working' and dispatch['providerInstanceId']=='codex' and dispatch['model']=='gpt-6-astra'
assert {x['id']:x['value'] for x in dispatch['options']}==dict(reasoningEffort='high',serviceTier='default') and not dispatch['hasPendingQuestion'] and dispatch['pendingApproval'] is None
client='twenty-20261025-fresh-arithmetic-r162cq-codex-astra-r1';assert not any(x.get('clientRequestId')==client for x in work['tasks'])
now=datetime.now(timezone.utc).isoformat();new_index=len(base['tasks']);fresh=copy.deepcopy(dispatch)
fresh.update(observed_utc=now,role='research',round=1,title='Arithmetic162cq: confirmed deterministic Ramanujan operative-proof discovery',clientRequestId=client,parent_thread='6742db91-d35c-44d0-a762-e5d9232f5177',target=dict(providerInstanceId='codex',model='gpt-6-astra',options=dict(reasoningEffort='high',serviceTier='default')),output='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cq/',brief=prep['brief'],brief_bytes=prep['bytes'],brief_sha256=prep['sha256'],submitted_prompt_contains_full_brief=True,source_index=178,source_family_navigation='Catalogue[280658,281794),one14000-byte window,178/179titles and only178body;179body unread. One deterministic Ramanujan manuscript;15blobs19entries14texts300708bytes. Actual build/main.tex2498/Gitc6568de074695fd21855546a71c75ba6aeb4ab52. Parent proof unread.',round_namespace='Distinct canonical manuscript from Source177. Full all-large-even-order strict nonbipartite construction and polynomial bit-time output paid. R162CP closed PASS/TECHNICAL;Structural175 full interior-gap scope preserved,no renamed retries.',all_previous_literal_guards_and5570_standing_bytes_retained=True,all_new_literal_guard_twins_verified_before_dispatch=True,completed_direct_inputs=5,dispatch_receipt='discovery-arithmetic-r162cq-parent/dispatch.json',prospective_isolation='discovery-arithmetic-r162cq-parent/prospective-isolation.json',distinct_canonical_manuscript=True,distinct_from_previous_mathematical_family=True,new_author_conversation=True,independent_review=False,accepted=False,count_change=0,parent_count_at_dispatch=19,publication='STOPPED',status_provenance='Fresh async receipt,Codex/GPT-6 Astra/high/default;no polling or foreign liveness query.')
def update(original):
 x=copy.deepcopy(original)
 x['tasks'][853].update(observed_utc=now,disposition='CLOSED_PASS_TECHNICAL',correctness_gate='PASS',contribution_gate='TECHNICAL',contribution_condition_discharged=True,contribution_review='arithmetic-r162cp-contribution-r1/private/REVIEW.md',contribution_parent_assessment='discovery-arithmetic-r162cp-parent/contribution-assessment.md',accepted=False,count_change=0,no_retry=True)
 r=x['tasks'][855];r.update(term);r.update(observed_utc=now,verdict='TECHNICAL',review_dimension='substantial_contribution',conditional_on_correctness=True,condition_discharged_by_parent=True,entire_unchanged_scope=True,essential_comparison_unresolved=False,author_inputs_unchanged=True,parent_intake='discovery-arithmetic-r162cp-parent/contribution-intake.json',parent_assessment='discovery-arithmetic-r162cp-parent/contribution-assessment.md',artifact_status='MATCH',artifact_verification='discovery-arithmetic-r162cp-parent/contribution-verification.json',canonical_texts=9,canonical_text_bytes=52577,primary_pages=142,primary_pdfs=6,primary_complete_papers=0,primary_visual_checks=6,optional_history_traversals=0,accepted=False,count_change=0,correctness_gate=None)
 x['tasks'].append(copy.deepcopy(fresh))
 adds={'arithmetic_r162cp_final_disposition':dict(observed_utc=now,author_task_index=853,correctness='PASS',contribution='TECHNICAL',condition_discharged=True,entire_unchanged_scope=True,accepted=False,count_change=0,no_retry=True,newAccepted=19,latestAcceptance='R041',publication='STOPPED'),'arithmetic_r162cq_dispatch':dict(task_index=new_index,taskId=dispatch['taskId'],status='running',serviceTier='default',source=178,catalogue_extent=[280658,281794],canonical_blobs=15,canonical_entries=19,canonical_texts=14,canonical_text_bytes=300708,completed_direct_inputs=5,count_change=0)}
 for k,value in adds.items():assert k not in x['current_work_snapshot'];x['current_work_snapshot'][k]=value
 assert [i for i,(a,b) in enumerate(zip(original['tasks'],x['tasks'])) if a!=b]==[853,855]
 assert all(x[k]==original[k] for k in original if k not in {'tasks','current_work_snapshot'}) and all(x['current_work_snapshot'][k]==a for k,a in original['current_work_snapshot'].items())
 return x
idx=enc(update(base));merged=enc(update(work))
note=('\n\n### R162CP closed PASS/TECHNICAL; Ramanujan discovery — '+now+'\n\n'
'[Contribution intake](campaigns/2026-10-14/discovery-arithmetic-r162cp-parent/contribution-assessment.md):entire unchanged R162CP is TECHNICAL conditional on correctness;independent full-scope PASS discharges condition. Character-twisted KN Fourier support/Parseval,source weighted cut Poincare,tree-path dualization,type-orbit averaging and common uniform-coset shift cover every conclusion. No unresolved comparison,repair,renaming or count increment. Parent full contribution REVIEW/DERIVATION/LIMITS/handoff/report/verifier reads;reviewer9source texts52577bytes,142primarypages6partialpapers,6visualchecks,history0. DDdisplay discrepancy resolved from actual proof;ancestry limits disclosed. Artifact MATCH38payloads7721590bytes40files7dirs,6PDFbindings,68authorfilesunchanged,3wronganchorsrejected. New Source178 deterministic Ramanujan author Codex/GPT-6 Astra/high/default. Onecataloguewindow280658..294658,178/179titles+only178body;179bodyunread.15blobs19entries14texts300708bytes,actualwrapper2498/Gitc6568de074695fd21855546a71c75ba6aeb4ab52. Full existence/strict spectrum/polybit construction paid;Structural175 scope preserved. All guards and standing5570bytes retained;three oversized precreation attempts corrected. Campaign19/20,latestR041;publication/downstreamSTOPPED.\n').encode()
ij=hj+note;mj=wj+note
baseline=json.loads((D/'intake-baseline.json').read_bytes())
for n,s in baseline['protected'].items():assert sha((P/n).read_bytes())==s
for e in json.loads((N/'private/completed-direct-inputs.json').read_bytes()):
 p=P/e['path'];a=p.read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256'] and p.stat().st_mode==e['mode']
(D/'contribution-coordination-rebase.json').write_bytes(enc(dict(integration_head=h,changed_old_tasks=[853,855],new_task_index=new_index,foreign_uncommitted_task_indices=foreign,foreign_uncommitted_top_fields=foreign_top,foreign_edits_preserved_and_excluded=True,foreign_journal_preserved_and_excluded=wj!=hj,index_tasks_sha256=sha(idx),working_tasks_sha256=sha(merged),index_journal_sha256=sha(ij),working_journal_sha256=sha(mj),count_change=0)))
(N/'registration.json').write_bytes(enc(dict(task_index=new_index,taskId=dispatch['taskId'],status_at_dispatch='running',model_options_verified=True,count_change=0,publication='STOPPED')))
names=['contribution-intake-baseline.json','contribution-task-status.json','verify-contribution-intake.py','contribution-verification.json','contribution-assessment.md','contribution-intake.json','prepare-next.py','next-integration-guard.json','manage-contribution-intake.py','contribution-coordination-rebase.json']
paths=[(D/n).relative_to(P).as_posix() for n in names]+[(N/n).relative_to(P).as_posix() for n in ['brief-preparation.json','capabilities.json','dispatch.json','prospective-isolation.json','registration.json']]+[prep['brief'],TP,JP];assert len(paths)==len(set(paths))==18
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
subprocess.run(['git','commit','-m','Close primitive sensitivity as technical and continue Ramanujan discovery'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip() and git('show','HEAD:openai-proof-research/'+TP)==idx and (P/TP).read_bytes()==merged and git('show','HEAD:openai-proof-research/'+JP)==ij and (P/JP).read_bytes()==mj
assert snap(B/'arithmetic-r162cp-contribution-r1')==json.loads((D/'private/contribution-intake/root-before.json').read_bytes()) and snap(B/'fresh-arithmetic-discovery-r162cp')==json.loads((D/'private/contribution-intake/author-before.json').read_bytes())
print(json.dumps(dict(commit=git('rev-parse','HEAD').decode().strip(),changed_old_tasks=[853,855],new_task_index=new_index,staged_paths=18,foreign_edits_preserved=foreign,foreign_journal_preserved=wj!=hj,count=19,author_and_review_unchanged=True)))
