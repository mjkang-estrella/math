"""Archive own result and register child; preserve unrelated index/worktree edits."""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
N=B/'discovery-arithmetic-r162cn-parent';R=B/'fresh-arithmetic-discovery-r162cm'
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
assert len(base['tasks'])==len(work['tasks'])==851 and base['tasks'][850]==work['tasks'][850]
assert base['newAccepted']==work['newAccepted']==19 and base['latestAcceptance']==work['latestAcceptance']=='R041'
assert base['gpt_subagent_preferences']==work['gpt_subagent_preferences'] and work['gpt_subagent_preferences']['serviceTier']=='default'
foreign=[i for i,(a,b) in enumerate(zip(base['tasks'],work['tasks'])) if a!=b];foreign_top=[k for k in base if k!='tasks' and base[k]!=work[k]]
term=json.loads((D/'task-status.json').read_bytes())['structuredContent'];assert term['taskId']==base['tasks'][850]['taskId'] and term['status']=='completed' and term['workState']=='result_available'
assert not term['hasPendingChildRuns'] and not term['hasPendingQuestion'] and term['pendingApproval'] is None
intake=json.loads((D/'intake.json').read_bytes());v=json.loads((D/'verification.json').read_bytes());baseline=json.loads((D/'intake-baseline.json').read_bytes())
assert intake['disposition']=='PREFREEZE_NO_NOMINEE' and v['status']=='MATCH' and snap(R)==json.loads((D/'private/intake/root-before.json').read_bytes())
prep=json.loads((N/'brief-preparation.json').read_bytes());brief=(P/prep['brief']).read_bytes();assert len(brief)==prep['bytes'] and sha(brief)==prep['sha256'] and len(brief.decode())<120000
dispatch=json.loads((N/'dispatch.json').read_bytes())['structuredContent'];assert dispatch['status']=='running' and dispatch['workState']=='working' and dispatch['model']=='gpt-6-astra' and dispatch['providerInstanceId']=='codex'
assert {x['id']:x['value'] for x in dispatch['options']}==dict(reasoningEffort='high',serviceTier='default') and not dispatch['hasPendingQuestion'] and dispatch['pendingApproval'] is None
assert prep['all_previous_literal_guards_retained'] and prep['all_extra_guard_literals_verified'] and prep['standing_bytes_preserved']==5570
client='twenty-20261025-fresh-arithmetic-r162cn-codex-astra-r1';assert not any(x.get('clientRequestId')==client for x in work['tasks'])
now=datetime.now(timezone.utc).isoformat();new_index=len(base['tasks']);fresh=copy.deepcopy(dispatch)
fresh.update(observed_utc=now,role='research',round=1,title='Arithmetic162cn: confirmed expectation-threshold and graph-decomposition discovery',clientRequestId=client,parent_thread='6742db91-d35c-44d0-a762-e5d9232f5177',target=dict(providerInstanceId='codex',model='gpt-6-astra',options=dict(reasoningEffort='high',serviceTier='default')),output='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cn/',brief=prep['brief'],brief_bytes=prep['bytes'],brief_sha256=prep['sha256'],submitted_prompt_contains_full_brief=True,source_index=175,source_family_navigation='Exact catalogue[276357,278505) contains all three Source175 manuscripts. One bounded14000-byte window decoded175/176titles and only175body;176body unread,thirdheader boundaryonly. Initial header-pattern mismatch recovered before semantic decoding. Three roots22blobs35entries19nonPDFtexts105743bytes. Actual build/main.tex33491/Git928bb7e06d85629e06b700bc69080b179bacbb96; build/source/main.tex1558/Git054ce9a4ce3c8f98345045192ccbcd3932905557; build/source/main.tex1566/Git24802358a8941d5d277f4447bd16ebab8fdb4dc8. All source texts/includes required; parent operativeproof unread.',round_namespace='Distinct from Source174. Integral/fractional threshold equivalence,discrete convexity,fixed graph-edge decompositions and stronger source/primary operations are paid. Same family/ground set/density/budget/graph and embedding quantifiers required. No exhaustive family-history clearance; old scopes unchanged.',all_previous_literal_guards_and5570_standing_bytes_retained=True,all_new_literal_guard_twins_verified_before_dispatch=True,completed_direct_inputs=5,dispatch_receipt='discovery-arithmetic-r162cn-parent/dispatch.json',prospective_isolation='discovery-arithmetic-r162cn-parent/prospective-isolation.json',prompt_length_checked_before_dispatch=True,distinct_family=True,new_author_conversation=True,independent_review=False,accepted=False,count_change=0,parent_count_at_dispatch=19,publication='STOPPED',status_provenance='Fresh async receipt confirms Codex/GPT-6 Astra/high/default; no polling,watcher or foreign liveness query.')
def update(original):
 x=copy.deepcopy(original);r=x['tasks'][850];r.update(term)
 r.update(observed_utc=now,disposition='PREFREEZE_NO_NOMINEE',theorem_frozen=False,diagnostic_frozen=False,correctness_gate=None,contribution_gate=None,parent_intake='discovery-arithmetic-r162cm-parent/intake.json',parent_assessment='discovery-arithmetic-r162cm-parent/assessment.md',artifact_status='MATCH',artifact_verification='discovery-arithmetic-r162cm-parent/verification.json',author_inputs_unchanged=True,accepted=False,count_change=0,author_comparisons=intake['closed_author_comparisons'],unproved_directions=intake['unproved_directions'],canonical_texts=36,canonical_text_bytes=339166,primary_pages=143,primary_pdfs_acquired=7,primary_complete_papers=4,primary_partial_papers=3,primary_visual_checks=3,author_optional_history_traversals=0,all_old_scopes_preserved=True,status_provenance='Own completed result queried once. Complete DERIVATION,WORKING,READING-LIMITS,FINAL,actual REPORT.json/private verifier read. No mathematics gate/review retry. Artifact71payloads73files20dirs unchanged;38sourceblobs11trees7primaryPDFs5original/copy bindings checked. Exact-marginal direction remains unproved;triangle rejects one inference only. Foreign journal/task edits preserved and excluded.')
 x['tasks'].append(copy.deepcopy(fresh))
 additions={'arithmetic_r162cm_final_disposition':dict(observed_utc=now,task_index=850,disposition='PREFREEZE_NO_NOMINEE',closed_comparisons=intake['closed_author_comparisons'],unproved_directions=intake['unproved_directions'],accepted=False,count_change=0,newAccepted=19,latestAcceptance='R041',publication='STOPPED'),'arithmetic_r162cn_dispatch':dict(task_index=new_index,taskId=dispatch['taskId'],source=175,status='running',serviceTier='default',distinct_from_previous_family=True,catalogue_extent=[276357,278505],canonical_folders=3,canonical_blobs=22,canonical_entries=35,canonical_texts=19,canonical_text_bytes=105743,completed_direct_inputs=5,count_change=0,publication='STOPPED')}
 for k,value in additions.items():assert k not in x['current_work_snapshot'];x['current_work_snapshot'][k]=value
 assert [i for i,(a,b) in enumerate(zip(original['tasks'],x['tasks'])) if a!=b]==[850]
 assert all(x[k]==original[k] for k in original if k not in {'tasks','current_work_snapshot'}) and all(x['current_work_snapshot'][k]==a for k,a in original['current_work_snapshot'].items())
 return x
idx=enc(update(base));merged=enc(update(work))
note=('\n\n### R162CM archived; expectation-threshold discovery — '+now+'\n\n'
'R162CM is PREFREEZE/no nominee. [Parent intake](campaigns/2026-10-14/discovery-arithmetic-r162cm-parent/assessment.md) retains same-labelled-graph exact-marginal exploration. Stronger metric-cone/source rounding,finite hull separation,dominated marginals,Lagrangian weighted lower condition,rank-slack/base complement criteria,boundary strongly Rayleigh laws and label restoration are paid. Uniformly thin support with prescribed mean remains unproved. Exact complementary-base/cut-budget repair or common face-and-weighted-lower rounding are sufficient routes,not necessary characterizations. Triangle rejects a peeling inference only and has the desired law. Parent read full DERIVATION18669,WORKING2396,LIMITS9606,FINAL2662,REPORT.json741 and verifier;expected .md/root verifier absent,actuals read. Author36texts339166bytes,143primarypages7PDF4full3partial,3visualchecks;ancestry incomplete,history0. Initial permission-only bindings later full-mode checked. Artifact MATCH71payloads5960738bytes73files20dirs,38blobs11trees7PDFs5completedpairs;3wronganchorsrejected,sealedbytes/modesunchanged. New Source175 author task Codex/GPT-6 Astra/high/default:one cataloguewindow276357..290357,175/176titles and only175body;headerpatternrecovery,176bodyunread. Three roots22blobs35entries19texts105743bytes;all actual wrappers/includes required. Threshold equivalence,discrete convexity and fixed graph decompositions already paid. Full standing5570bytes/all guards and old scopes preserved;one precreation120492-character rejection corrected without creating directories. Foreign working edits excluded. Campaign19/20,latestR041;publication/downstreamSTOPPED.\n').encode()
ij=hj+note;mj=wj+note
for e in json.loads((N/'private/completed-direct-inputs.json').read_bytes()):
 p=P/e['path'];a=p.read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256'] and p.stat().st_mode==e['mode']
for n,s in baseline['protected'].items():assert sha((P/n).read_bytes())==s
(D/'coordination-rebase.json').write_bytes(enc(dict(intake_head=baseline['head'],integration_head=h,changed_old_tasks=[850],new_task_index=new_index,foreign_uncommitted_task_indices=foreign,foreign_uncommitted_top_fields=foreign_top,foreign_edits_preserved_and_excluded=True,journal_prefix_preserved=True,foreign_journal_edit_preserved_and_excluded=wj!=hj,index_journal_after_sha256=sha(ij),working_journal_after_sha256=sha(mj),index_tasks_after_sha256=sha(idx),working_tasks_after_sha256=sha(merged),count_change=0)))
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
subprocess.run(['git','commit','-m','Archive thin-tree marginal exploration and start threshold discovery'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip() and git('show','HEAD:openai-proof-research/'+TP)==idx and (P/TP).read_bytes()==merged and git('show','HEAD:openai-proof-research/'+JP)==ij and (P/JP).read_bytes()==mj
assert snap(R)==json.loads((D/'private/intake/root-before.json').read_bytes())
for n,s in baseline['protected'].items():assert sha((P/n).read_bytes())==s
print(json.dumps(dict(commit=git('rev-parse','HEAD').decode().strip(),changed_old_tasks=[850],new_task_index=new_index,staged_paths=20,foreign_edits_preserved=foreign,foreign_journal_preserved=wj!=hj,count=19,author_seal_unchanged=True)))
