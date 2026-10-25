"""Archive own result and register child; preserve unrelated index/worktree edits."""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
N=B/'discovery-arithmetic-r162cr-parent';R=B/'fresh-arithmetic-discovery-r162cq'
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
assert len(base['tasks'])==len(work['tasks'])==857 and base['tasks'][856]==work['tasks'][856]
assert base['newAccepted']==work['newAccepted']==19 and base['latestAcceptance']==work['latestAcceptance']=='R041'
assert base['gpt_subagent_preferences']==work['gpt_subagent_preferences'] and work['gpt_subagent_preferences']['serviceTier']=='default'
foreign=[i for i,(a,b) in enumerate(zip(base['tasks'],work['tasks'])) if a!=b];foreign_top=[k for k in base if k!='tasks' and base[k]!=work[k]]
term=json.loads((D/'task-status.json').read_bytes())['structuredContent'];assert term['taskId']==base['tasks'][856]['taskId'] and term['status']=='completed' and term['workState']=='result_available'
assert not term['hasPendingChildRuns'] and not term['hasPendingQuestion'] and term['pendingApproval'] is None
intake=json.loads((D/'intake.json').read_bytes());v=json.loads((D/'verification.json').read_bytes());baseline=json.loads((D/'intake-baseline.json').read_bytes())
assert intake['disposition']=='PREFREEZE_NO_NOMINEE' and v['status']=='MATCH' and snap(R)==json.loads((D/'private/intake/root-before.json').read_bytes())
prep=json.loads((N/'brief-preparation.json').read_bytes());brief=(P/prep['brief']).read_bytes();assert len(brief)==prep['bytes'] and sha(brief)==prep['sha256'] and len(brief.decode())<120000
dispatch=json.loads((N/'dispatch.json').read_bytes())['structuredContent'];assert dispatch['status']=='running' and dispatch['workState']=='working' and dispatch['model']=='gpt-6-astra' and dispatch['providerInstanceId']=='codex'
assert {x['id']:x['value'] for x in dispatch['options']}==dict(reasoningEffort='high',serviceTier='default') and not dispatch['hasPendingQuestion'] and dispatch['pendingApproval'] is None
assert prep['all_previous_literal_guards_retained'] and prep['all_extra_guard_literals_verified'] and prep['standing_bytes_preserved']==5570
client='twenty-20261025-fresh-arithmetic-r162cr-codex-astra-r1';assert not any(x.get('clientRequestId')==client for x in work['tasks'])
now=datetime.now(timezone.utc).isoformat();new_index=len(base['tasks']);fresh=copy.deepcopy(dispatch)
fresh.update(observed_utc=now,role='research',round=1,title='Arithmetic162cr: confirmed circulant-Hadamard and Barker discovery',clientRequestId=client,parent_thread='6742db91-d35c-44d0-a762-e5d9232f5177',target=dict(providerInstanceId='codex',model='gpt-6-astra',options=dict(reasoningEffort='high',serviceTier='default')),output='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cr/',brief=prep['brief'],brief_bytes=prep['bytes'],brief_sha256=prep['sha256'],submitted_prompt_contains_full_brief=True,source_index=179,source_family_navigation='Catalogue[281794,282674),one14000-byte window,179/180titles and only179body,180bodyunread. One circulant-Hadamard/Barker manuscript:10blobs13entries9texts50986bytes. Actual build/main.tex1868/Gitcc0ab49aa3f2c8080a7a4f48bfd52f49d5278c5a. Parent proof unread.',round_namespace='Distinct canonical manuscript from Source178. Full circulant-Hadamard and Barker classifications and stronger source/primary operations paid. All older scopes remain unchanged,no renamed retries.',all_previous_literal_guards_and5570_standing_bytes_retained=True,all_new_literal_guard_twins_verified_before_dispatch=True,completed_direct_inputs=5,dispatch_receipt='discovery-arithmetic-r162cr-parent/dispatch.json',prospective_isolation='discovery-arithmetic-r162cr-parent/prospective-isolation.json',prompt_length_checked_before_dispatch=True,distinct_canonical_manuscript=True,distinct_from_previous_mathematical_family=True,new_author_conversation=True,independent_review=False,accepted=False,count_change=0,parent_count_at_dispatch=19,publication='STOPPED',status_provenance='Fresh async receipt,Codex/GPT-6 Astra/high/default;no polling or foreign liveness query.')

def update(original):
 x=copy.deepcopy(original);r=x['tasks'][856];r.update(term)
 r.update(observed_utc=now,disposition='PREFREEZE_NO_NOMINEE',theorem_frozen=False,diagnostic_frozen=False,correctness_gate=None,contribution_gate=None,parent_intake='discovery-arithmetic-r162cq-parent/intake.json',parent_assessment='discovery-arithmetic-r162cq-parent/assessment.md',artifact_status='MATCH',artifact_verification='discovery-arithmetic-r162cq-parent/verification.json',author_inputs_unchanged=True,accepted=False,count_change=0,author_comparisons=intake['closed_author_comparisons'],unproved_directions=intake['unproved_directions'],canonical_texts=14,canonical_text_bytes=300708,primary_pages=220,primary_pdfs_acquired=11,primary_pdfs_read=10,primary_complete_papers=7,primary_partial_papers=3,primary_visual_checks=2,author_optional_history_traversals=0,all_old_scopes_preserved=True,status_provenance='Own completed result queried once. Full WORKLOG,COMPARISON,READING-LIMITS,handoffs/verifier/controls read. Girth preservation paid;signing/cover attempts unclosed. Artifact60payloads62files11dirs,15blobs4trees11PDFs5completedpairs verified unchanged. No math gates. Foreign edits preserved and excluded.')
 x['tasks'].append(copy.deepcopy(fresh))
 additions={'arithmetic_r162cq_final_disposition':dict(observed_utc=now,task_index=856,disposition='PREFREEZE_NO_NOMINEE',closed_comparisons=intake['closed_author_comparisons'],unproved_directions=intake['unproved_directions'],accepted=False,count_change=0,newAccepted=19,latestAcceptance='R041',publication='STOPPED'),'arithmetic_r162cr_dispatch':dict(task_index=new_index,taskId=dispatch['taskId'],source=179,status='running',serviceTier='default',distinct_canonical_manuscript=True,distinct_from_previous_mathematical_family=True,catalogue_extent=[281794,282674],canonical_folders=1,canonical_blobs=10,canonical_entries=13,canonical_texts=9,canonical_text_bytes=50986,completed_direct_inputs=5,count_change=0,publication='STOPPED')}
 for k,value in additions.items():assert k not in x['current_work_snapshot'];x['current_work_snapshot'][k]=value
 assert [i for i,(a,b) in enumerate(zip(original['tasks'],x['tasks'])) if a!=b]==[856]
 assert all(x[k]==original[k] for k in original if k not in {'tasks','current_work_snapshot'}) and all(x['current_work_snapshot'][k]==a for k,a in original['current_work_snapshot'].items())
 return x
idx=enc(update(base));merged=enc(update(work))
note=('\n\n### R162CQ archived; circulant-Hadamard/Barker discovery — '+now+'\n\n'
+'R162CQ is PREFREEZE/no nominee. [Parent intake](campaigns/2026-10-14/discovery-arithmetic-r162cq-parent/assessment.md) preserves paid same-law logarithmic-girth repair/finite-seed comparison. Fixed-base signing and finite-cover attempts remain unclosed;triangle3-cycle response rejects a specific transplant only. Stronger signing/covering/mixed-moment primaries credited. Parent full WORKLOG4079,COMPARISON13461,LIMITS9654,FINAL2085,REPORT1871,verifier5093bytes read. Author14texts300708bytes,220primarypages10of11PDFs,7completepapers3partial,2visualchecks;history0,ancestry incomplete. Artifact MATCH60payloads12904974bytes62files11dirs,15blobs4trees11PDFs5completedpairs,3wronganchorsrejected;allauthorbytes/modesunchanged. New Source179 Codex/GPT-6 Astra/high/default:onewindow281794..295794,179/180titles+only179body;180bodyunread.10blobs13entries9texts50986bytes,actualwrapper1868/Gitcc0ab49aa3f2c8080a7a4f48bfd52f49d5278c5a. Full classifications and stronger operations paid. All guards,standing5570bytes and old scopes retained;two oversized precreation attempts shortened without namespace creation. Foreign edits preserved/excluded. Campaign19/20,latestR041;publication/downstreamSTOPPED.\n').encode()
ij=hj+note;mj=wj+note
for e in json.loads((N/'private/completed-direct-inputs.json').read_bytes()):
 p=P/e['path'];a=p.read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256'] and p.stat().st_mode==e['mode']
for n,s in baseline['protected'].items():assert sha((P/n).read_bytes())==s
(D/'coordination-rebase.json').write_bytes(enc(dict(intake_head=baseline['head'],integration_head=h,changed_old_tasks=[856],new_task_index=new_index,foreign_uncommitted_task_indices=foreign,foreign_uncommitted_top_fields=foreign_top,foreign_edits_preserved_and_excluded=True,journal_prefix_preserved=True,foreign_journal_edit_preserved_and_excluded=wj!=hj,index_journal_after_sha256=sha(ij),working_journal_after_sha256=sha(mj),index_tasks_after_sha256=sha(idx),working_tasks_after_sha256=sha(merged),count_change=0)))
(N/'registration.json').write_bytes(enc(dict(task_index=new_index,taskId=dispatch['taskId'],status_at_dispatch='running',distinct_family=True,model_options_verified=True,count_change=0,publication='STOPPED')))
names=['baseline.py','intake-baseline.json','intake-prospective-isolation.json','verify-intake.py','verification.json','task-status.json','assessment.md','intake.json','prepare-next.py','integration-guard.json','manage-intake.py','coordination-rebase.json']
paths=[(D/n).relative_to(P).as_posix() for n in names]+[(N/n).relative_to(P).as_posix() for n in ['brief-preparation.json','capabilities.json','dispatch.json','prospective-isolation.json','registration.json']]+[prep['brief'],TP,JP];assert len(paths)==len(set(paths))==20
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
subprocess.run(['git','commit','-m','Archive Ramanujan comparison and start circulant-Hadamard discovery'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip() and git('show','HEAD:openai-proof-research/'+TP)==idx and (P/TP).read_bytes()==merged and git('show','HEAD:openai-proof-research/'+JP)==ij and (P/JP).read_bytes()==mj
assert snap(R)==json.loads((D/'private/intake/root-before.json').read_bytes())
for n,s in baseline['protected'].items():assert sha((P/n).read_bytes())==s
print(json.dumps(dict(commit=git('rev-parse','HEAD').decode().strip(),changed_old_tasks=[856],new_task_index=new_index,staged_paths=20,foreign_edits_preserved=foreign,foreign_journal_preserved=wj!=hj,count=19,author_seal_unchanged=True)))
