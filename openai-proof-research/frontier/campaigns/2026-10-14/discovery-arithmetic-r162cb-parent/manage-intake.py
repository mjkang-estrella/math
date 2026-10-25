#!/usr/bin/env python3
"""Register a frozen nominee and isolated reviews without adopting their gates."""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
R=B/'fresh-arithmetic-discovery-r162cb'
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
base=json.loads(ht);work=json.loads(wt);assert len(base['tasks'])==len(work['tasks']) and base['tasks'][837]==work['tasks'][837]
assert base['newAccepted']==work['newAccepted']==19 and base['latestAcceptance']==work['latestAcceptance']=='R041'
assert base['gpt_subagent_preferences']==work['gpt_subagent_preferences'] and work['gpt_subagent_preferences']['serviceTier']=='default'
foreign=[i for i,(a,b) in enumerate(zip(base['tasks'],work['tasks'])) if a!=b];foreign_top=[k for k in base if k!='tasks' and base[k]!=work[k]]
term=json.loads((D/'task-status.json').read_bytes())['structuredContent']
assert term['taskId']==base['tasks'][837]['taskId'] and term['status']=='completed' and term['workState']=='result_available'
assert not term['hasPendingChildRuns'] and not term['hasPendingQuestion'] and term['pendingApproval'] is None
intake=json.loads((D/'intake.json').read_bytes());baseline=json.loads((D/'intake-baseline.json').read_bytes())
assert intake['disposition']=='FULL_AUTHOR_PROOF_NOMINEE_REVIEW_PENDING' and intake['theorem_frozen'] and intake['verification']['status']=='MATCH'
assert snap(R)==json.loads((D/'private/intake/root-before.json').read_bytes())
prep=json.loads((D/'review-preparation.json').read_bytes());allow=(P/prep['author_input_allowlist']).read_bytes()
assert sha(allow)==prep['author_input_allowlist_sha256'] and prep['author_files']==61
for e in json.loads(allow):
 p=P/e['path'];a=p.read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256'] and p.stat().st_mode==e['mode']
now=datetime.now(timezone.utc).isoformat();fresh=[];registrations=[]
for j,x in enumerate(prep['reviews']):
 role=x['role'];a=(P/x['brief']).read_bytes();assert len(a)==x['bytes'] and sha(a)==x['sha256'] and len(a.decode())<120000
 assert x['all_author_literal_guards_retained'] and x['standing_bytes_preserved']==5570
 dispatch=json.loads((D/(role+'-dispatch.json')).read_bytes())['structuredContent']
 assert dispatch['status']=='running' and dispatch['workState']=='working' and dispatch['model']=='gpt-6-astra' and dispatch['providerInstanceId']=='codex'
 assert {o['id']:o['value'] for o in dispatch['options']}==dict(reasoningEffort='high',serviceTier='default')
 assert not dispatch['hasPendingQuestion'] and dispatch['pendingApproval'] is None
 client='twenty-20261025-arithmetic-r162cb-'+role+'-codex-astra-r1'
 assert not any(t.get('clientRequestId')==client for t in work['tasks'])
 rec=copy.deepcopy(dispatch)
 rec.update(observed_utc=now,role='review',review_role=('correctness' if role=='proof' else 'substantial_contribution'),round=1,title=('R162CB: independent full correctness review' if role=='proof' else 'R162CB: independent full substantial-contribution review'),clientRequestId=client,parent_thread='6742db91-d35c-44d0-a762-e5d9232f5177',target=dict(providerInstanceId='codex',model='gpt-6-astra',options=dict(reasoningEffort='high',serviceTier='default')),output=x['root']+'/',brief=x['brief'],brief_bytes=x['bytes'],brief_sha256=x['sha256'],submitted_prompt_contains_full_brief=True,review_of='R162CB',entire_unchanged_scope=True,frozen_statement_sha256=intake['statement']['sha256'],author_proof_sha256=intake['proof']['sha256'],conditional_on_correctness=(role=='contribution'),author_input_allowlist=prep['author_input_allowlist'],author_input_allowlist_sha256=prep['author_input_allowlist_sha256'],author_files=61,semantic_author_files=prep['semantic_author_files'],other_review_inspection=False,optional_history_traversals=0,all_author_literal_guards_retained=True,standing_bytes_preserved=5570,independent_review=True,accepted=False,count_change=0,parent_count_at_dispatch=19,publication='STOPPED',dispatch_receipt=(D/(role+'-dispatch.json')).relative_to(B).as_posix(),status_provenance='Fresh async receipt confirms Codex/GPT-6 Astra/high/default. Other review hidden; no polling or foreign liveness query.')
 fresh.append(rec);registrations.append(dict(role=role,task_index=len(base['tasks'])+j,taskId=dispatch['taskId'],status_at_dispatch='running'))
def update(original):
 x=copy.deepcopy(original);r=x['tasks'][837];r.update(term)
 r.update(observed_utc=now,disposition='FULL_AUTHOR_PROOF_NOMINEE_REVIEW_PENDING',theorem_frozen=True,diagnostic_frozen=False,frozen_statement_sha256=intake['statement']['sha256'],author_proof_sha256=intake['proof']['sha256'],correctness_gate=None,contribution_gate=None,parent_intake='discovery-arithmetic-r162cb-parent/intake.json',parent_assessment='discovery-arithmetic-r162cb-parent/assessment.md',artifact_status='MATCH',artifact_verification='discovery-arithmetic-r162cb-parent/verification.json',author_inputs_unchanged=True,accepted=False,count_change=0,canonical_texts=18,canonical_text_bytes=291598,primary_pages=63,primary_complete_papers=5,primary_complete_pages=53,primary_partial_pages=10,primary_visual_checks=2,author_optional_history_traversals=0,all_old_scopes_preserved=True,status_provenance='Own terminal queried once. Full frozen statement,proof,derivation,interfaces,limits,handoffs/verifier read. Artifact59payloads61files21dirs unchanged. Two independent whole-scope reviews commissioned; no parent gate or count.')
 x['tasks'].extend(copy.deepcopy(fresh))
 additions={'arithmetic_r162cb_author_nomination':dict(task_index=837,status='FULL_AUTHOR_PROOF_NOMINEE_REVIEW_PENDING',frozen_statement_sha256=intake['statement']['sha256'],author_proof_sha256=intake['proof']['sha256'],correctness_gate=None,contribution_gate=None,count_change=0),'arithmetic_r162cb_reviews':dict(observed_utc=now,registrations=registrations,entire_unchanged_scope=True,independent=True,other_review_inspection=False,serviceTier='default',count_change=0,publication='STOPPED')}
 for k,v in additions.items():assert k not in x['current_work_snapshot'];x['current_work_snapshot'][k]=v
 assert [i for i,(a,b) in enumerate(zip(original['tasks'],x['tasks'])) if a!=b]==[837]
 assert all(x[k]==original[k] for k in original if k not in {'tasks','current_work_snapshot'})
 assert all(x['current_work_snapshot'][k]==v for k,v in original['current_work_snapshot'].items())
 return x
idx=enc(update(base));merged=enc(update(work))
note=('\n\n### R162CB frozen author nominee; independent reviews — '+now+'\n\n'
+'R162CB supplies a [frozen author statement](campaigns/2026-10-14/fresh-arithmetic-discovery-r162cb/STATEMENT.md): for every sufficiently large prime s=2mod3 and every sufficiently large odd n depending on s,rank r=s^n+1,there is a finite simple r-partite r-uniform hypergraph with exactly r nonisolated vertices per part,integral cover r,and distinct-edge intersections of size1or2. Statement SHA256b69dd8585357682a27bb327cfcd789ebab99c828c00f928ec79322e1b525f53a;proof SHA256c8e2cf054d11162c11b4e2eb0e042820caa493d7d039bee86f670fa33415a25e. The author uses simultaneous omitted-line/special-label identifications on one source placement and accounts for infinite,internal and external pencil covers. No parent correctness/contribution gate or count is assigned. Complete parent intake reads the statement,proof,derivation,interfaces,limits and verifier;author reports18canonicaltexts291598bytes,5fullprimarypapers53pages plus10DKMSpages,2postfreezevisuals,history0,with limits disclosed. Artifact MATCH59payloads4790725bytes61files21dirs,20sourceblobs6trees,6primaryPDFs5completedpairs;wronganchorsrejected,allauthorbytes/modesunchanged. Separate whole-scope correctness and contribution reviews now run Codex/GPT-6 Astra/high/default,with peer findings hidden and semantic/raw author-input permissions separated. All guards,5570standingbytes,older scopes and foreign edits preserved. Campaign19/20,latestR041;publication/downstreamSTOPPED.\n').encode();nj=hj+note
for n,s in baseline['protected'].items():assert sha((P/n).read_bytes())==s
(D/'coordination-rebase.json').write_bytes(enc(dict(intake_head=baseline['head'],integration_head=h,changed_old_tasks=[837],new_task_indices=[r['task_index'] for r in registrations],foreign_uncommitted_task_indices=foreign,foreign_uncommitted_top_fields=foreign_top,foreign_edits_preserved_and_excluded=True,journal_prefix_preserved=True,index_tasks_after_sha256=sha(idx),working_tasks_after_sha256=sha(merged),count_change=0)))
(D/'review-registration.json').write_bytes(enc(dict(reviews=registrations,frozen_scope_unchanged=True,model_options_verified=True,count_change=0,publication='STOPPED')))
names=['intake-baseline.json','intake-prospective-isolation.json','verify-intake.py','verification.json','task-status.json','assessment.md','intake.json','prepare-reviews.py','review-preparation.json','review-isolation.json','review-capabilities.json','proof-dispatch.json','contribution-dispatch.json','manage-intake.py','coordination-rebase.json','review-registration.json']
paths=[(D/n).relative_to(P).as_posix() for n in names]+[x['brief'] for x in prep['reviews']]+[TP,JP]
assert len(paths)==len(set(paths))==20
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
subprocess.run(['git','commit','-m','Register frozen Ryser nominee and independent full-scope reviews'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip() and git('show','HEAD:openai-proof-research/'+TP)==idx and (P/TP).read_bytes()==merged
assert snap(R)==json.loads((D/'private/intake/root-before.json').read_bytes())
for n,s in baseline['protected'].items():assert sha((P/n).read_bytes())==s
print(json.dumps(dict(commit=git('rev-parse','HEAD').decode().strip(),changed_old_tasks=[837],new_reviews=registrations,staged_paths=20,foreign_edits_preserved=foreign,count=19,author_seal_unchanged=True)))
