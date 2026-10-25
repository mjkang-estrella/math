"""Register a frozen nominee and its first independent review, no count increment."""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent;R=B/'fresh-arithmetic-discovery-r162cp'
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
assert len(base['tasks'])==len(work['tasks'])==854 and base['tasks'][853]==work['tasks'][853]
assert base['newAccepted']==work['newAccepted']==19 and base['latestAcceptance']==work['latestAcceptance']=='R041'
assert base['gpt_subagent_preferences']==work['gpt_subagent_preferences'] and work['gpt_subagent_preferences']['serviceTier']=='default'
foreign=[i for i,(a,b) in enumerate(zip(base['tasks'],work['tasks'])) if a!=b];foreign_top=[k for k in base if k!='tasks' and base[k]!=work[k]]
term=json.loads((D/'task-status.json').read_bytes())['structuredContent'];assert term['taskId']==base['tasks'][853]['taskId'] and term['status']=='completed' and term['workState']=='result_available'
assert not term['hasPendingChildRuns'] and not term['hasPendingQuestion'] and term['pendingApproval'] is None
intake=json.loads((D/'intake.json').read_bytes());v=json.loads((D/'verification.json').read_bytes());baseline=json.loads((D/'intake-baseline.json').read_bytes())
assert intake['disposition']=='FROZEN_AUTHOR_PROOF_NOMINEE_REVIEW_PENDING' and v['status']=='MATCH' and snap(R)==json.loads((D/'private/intake/root-before.json').read_bytes())
prep=json.loads((D/'review-preparation.json').read_bytes());p=next(x for x in prep['reviews'] if x['role']=='proof');c=next(x for x in prep['reviews'] if x['role']=='contribution')
for x in prep['reviews']:
 a=(P/x['brief']).read_bytes();assert len(a)==x['bytes'] and sha(a)==x['sha256'] and len(a.decode())<120000 and x['all_inherited_literal_guards_retained'] and x['original_standing_bytes']==5570
dispatch=json.loads((D/'correctness-dispatch.json').read_bytes())['structuredContent'];assert dispatch['status']=='running' and dispatch['workState']=='working' and dispatch['model']=='gpt-6-astra' and dispatch['providerInstanceId']=='codex'
assert {x['id']:x['value'] for x in dispatch['options']}==dict(reasoningEffort='high',serviceTier='default') and not dispatch['hasPendingQuestion'] and dispatch['pendingApproval'] is None
client='twenty-20261025-arithmetic-r162cp-proof-codex-astra-r1';assert not any(x.get('clientRequestId')==client for x in work['tasks'])
now=datetime.now(timezone.utc).isoformat();new_index=len(base['tasks']);fresh=copy.deepcopy(dispatch)
fresh.update(observed_utc=now,role='review',review_dimension='correctness',round=1,title='R162CP: independent full correctness review',clientRequestId=client,parent_thread='6742db91-d35c-44d0-a762-e5d9232f5177',target=dict(providerInstanceId='codex',model='gpt-6-astra',options=dict(reasoningEffort='high',serviceTier='default')),output=p['root']+'/',brief=p['brief'],brief_bytes=p['bytes'],brief_sha256=p['sha256'],submitted_prompt_contains_full_brief=True,source_index=177,nominee='R162CP',frozen_statement_sha256=intake['statement_sha256'],frozen_proof_sha256=intake['proof_sha256'],author_input_count=68,author_input_manifest='discovery-arithmetic-r162cp-parent/private/review-inputs.json',independent_review=True,peer_review_inspection=False,accepted=False,count_change=0,parent_count_at_dispatch=19,publication='STOPPED',dispatch_receipt='discovery-arithmetic-r162cp-parent/correctness-dispatch.json',status_provenance='Fresh async receipt;Codex/GPT-6 Astra/high/default. Separate contribution review prepared but not dispatched;serial same-model work. No polling or peer query.')
def update(original):
 x=copy.deepcopy(original);r=x['tasks'][853];r.update(term)
 r.update(observed_utc=now,disposition=intake['disposition'],theorem_frozen=True,correctness_gate=None,contribution_gate=None,parent_intake='discovery-arithmetic-r162cp-parent/intake.json',parent_assessment='discovery-arithmetic-r162cp-parent/assessment.md',artifact_status='MATCH',artifact_verification='discovery-arithmetic-r162cp-parent/verification.json',author_inputs_unchanged=True,accepted=False,count_change=0,frozen_statement_sha256=intake['statement_sha256'],frozen_proof_sha256=intake['proof_sha256'],canonical_texts=9,canonical_text_bytes=52577,primary_pages=133,primary_pdfs_acquired=8,primary_pdfs_read=6,primary_complete_papers=1,primary_visual_checks=3,author_optional_history_traversals=0,all_old_scopes_preserved=True,status_provenance='Own completed result queried once. Full frozen statement/proof/comparison and author records read. Artifact66payloads68files13dirs unchanged;10blobs5trees8PDFs checked. Nominee pending both independent reviews,no mathematical grade/count.')
 x['tasks'].append(copy.deepcopy(fresh))
 adds={'arithmetic_r162cp_nominee_intake':dict(observed_utc=now,task_index=853,disposition=intake['disposition'],statement_sha256=intake['statement_sha256'],proof_sha256=intake['proof_sha256'],correctness=None,contribution=None,accepted=False,count_change=0,newAccepted=19,latestAcceptance='R041',publication='STOPPED'),'arithmetic_r162cp_correctness_dispatch':dict(task_index=new_index,taskId=dispatch['taskId'],status='running',serviceTier='default',entire_unchanged_scope=True,count_change=0),'arithmetic_r162cp_contribution_prepared':dict(status='prepared_not_dispatched',brief=c['brief'],brief_sha256=c['sha256'],entire_unchanged_scope=True,peer_verdict_not_supplied=True,serial_after_correctness=True,count_change=0)}
 for k,value in adds.items():assert k not in x['current_work_snapshot'];x['current_work_snapshot'][k]=value
 assert [i for i,(a,b) in enumerate(zip(original['tasks'],x['tasks'])) if a!=b]==[853]
 assert all(x[k]==original[k] for k in original if k not in {'tasks','current_work_snapshot'}) and all(x['current_work_snapshot'][k]==a for k,a in original['current_work_snapshot'].items())
 return x
idx=enc(update(base));merged=enc(update(work))
note=('\n\n### R162CP frozen nominee; independent review begins — '+now+'\n\n'
'[Parent intake](campaigns/2026-10-14/discovery-arithmetic-r162cp-parent/assessment.md):one full author proof claims sharp logarithmic common primitive-section sensitivity on unchanged Source177 complexes,including arbitrary nonlinear-section laws and matching exact-uniform-fiber affine upper law. Statement ebbecfde0342e866f1401764980ccaf1f3f0c08bc1aea5269e217021774594c9;proof7331535f72a9c9dbab2da0396af34c78eb0a1065afb5e96d4cfc618a22a052b6. Parent full statement/proof/comparison,private feasibility/derivation/reading records and verifier read. Artifact MATCH66payloads9372207bytes68files13dirs;10blobs5trees8PDFs,frozen anchors and original copies unchanged;wrong-anchor controls rejected. Author9texts52577bytes,133primarypages6readPDFs,onefullpaper,3visualchecks;8PDFs acquired,two bodies unread,ancestry incomplete,history0. Correctness review is running Codex/GPT-6 Astra/high/default on entire unchanged scope. Separate contribution brief prepared without peer verdict;will run serially. No correctness/contribution grade,acceptance or count yet. All previous scopes,guards and foreign edits preserved. Campaign19/20,latestR041;publication/downstreamSTOPPED.\n').encode()
ij=hj+note;mj=wj+note
for n,s in baseline['protected'].items():assert sha((P/n).read_bytes())==s
(D/'coordination-rebase.json').write_bytes(enc(dict(intake_head=baseline['head'],integration_head=h,changed_old_tasks=[853],new_task_index=new_index,foreign_uncommitted_task_indices=foreign,foreign_uncommitted_top_fields=foreign_top,foreign_edits_preserved_and_excluded=True,journal_prefix_preserved=True,foreign_journal_edit_preserved_and_excluded=wj!=hj,index_journal_after_sha256=sha(ij),working_journal_after_sha256=sha(mj),index_tasks_after_sha256=sha(idx),working_tasks_after_sha256=sha(merged),count_change=0)))
(D/'review-registration.json').write_bytes(enc(dict(task_index=new_index,taskId=dispatch['taskId'],status_at_dispatch='running',review_dimension='correctness',contribution_status='prepared_not_dispatched',model_options_verified=True,count_change=0,publication='STOPPED')))
names=['baseline.py','intake-baseline.json','intake-prospective-isolation.json','verify-intake.py','verification.json','task-status.json','assessment.md','intake.json','prepare-reviews.py','review-preparation.json','correctness-dispatch.json','manage-intake.py','coordination-rebase.json','review-registration.json']
paths=[(D/n).relative_to(P).as_posix() for n in names]+[p['brief'],c['brief'],TP,JP];assert len(paths)==len(set(paths))==18
assert git('rev-parse','HEAD').decode().strip()==h and (P/TP).read_bytes()==wt and (P/JP).read_bytes()==wj and not git('diff','--cached','--name-only').strip()
(P/TP).write_bytes(merged);(P/JP).write_bytes(mj)
subprocess.run(['git','add','--',*[n for n in paths if n not in {TP,JP}]],cwd=P,check=True)
for path,content in [(TP,idx),(JP,ij)]:
 blob=git('hash-object','-w','--stdin',input=content).decode().strip();subprocess.run(['git','update-index','--add','--cacheinfo','100644',blob,'openai-proof-research/'+path],cwd=P,check=True)
assert {n for n in git('diff','--cached','--name-only','-z').decode().split('\0') if n}=={'openai-proof-research/'+n for n in paths}
assert git('show',':openai-proof-research/'+TP)==idx and git('show',':openai-proof-research/'+JP)==ij
for n in paths:
 if n not in {TP,JP}:assert git('show',':openai-proof-research/'+n)==(P/n).read_bytes()
subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
assert git('rev-parse','HEAD').decode().strip()==h and (P/TP).read_bytes()==merged and (P/JP).read_bytes()==mj
subprocess.run(['git','commit','-m','Register primitive sensitivity nominee and independent correctness review'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip() and git('show','HEAD:openai-proof-research/'+TP)==idx and (P/TP).read_bytes()==merged and git('show','HEAD:openai-proof-research/'+JP)==ij and (P/JP).read_bytes()==mj
assert snap(R)==json.loads((D/'private/intake/root-before.json').read_bytes())
for n,s in baseline['protected'].items():assert sha((P/n).read_bytes())==s
print(json.dumps(dict(commit=git('rev-parse','HEAD').decode().strip(),changed_old_tasks=[853],new_task_index=new_index,staged_paths=18,foreign_edits_preserved=foreign,foreign_journal_preserved=wj!=hj,count=19,author_seal_unchanged=True,contribution='prepared_not_dispatched')))
