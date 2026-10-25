#!/usr/bin/env python3
"""Close the technical result, start distinct discovery, preserve foreign edits."""
from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,subprocess
P=Path(__file__).resolve().parents[5];D=Path(__file__).resolve().parent;B=D.parent.parent
N=B/'discovery-arithmetic-r162bn-parent';R=B/'arithmetic-r162bm-contribution-r1';AR=B/'fresh-arithmetic-discovery-r162bm'
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
for n in [817,820]:assert base['tasks'][n]==work['tasks'][n]
assert base['newAccepted']==work['newAccepted']==19 and base['latestAcceptance']==work['latestAcceptance']=='R041'
assert base['gpt_subagent_preferences']==work['gpt_subagent_preferences'] and work['gpt_subagent_preferences']['serviceTier']=='default'
foreign=[i for i,(a,b) in enumerate(zip(base['tasks'],work['tasks'])) if a!=b];foreign_top=[k for k in base if k!='tasks' and base[k]!=work[k]]
term=json.loads((D/'task-status.json').read_bytes())['structuredContent'];assert term['taskId']==base['tasks'][820]['taskId'] and term['status']=='completed' and term['workState']=='result_available'
assert not term['hasPendingChildRuns'] and not term['hasPendingQuestion'] and term['pendingApproval'] is None
intake=json.loads((D/'intake.json').read_bytes());proof=json.loads((D.parent/'proof-intake/intake.json').read_bytes());v=json.loads((D/'verification.json').read_bytes())
assert intake['contribution']=='TECHNICAL' and proof['verdict']=='PASS' and intake['statement_sha256']==proof['statement_sha256'] and intake['proof_sha256']==proof['proof_sha256']
assert v['status']=='MATCH' and snap(R)==json.loads((D/'review-before.json').read_bytes()) and snap(AR)==json.loads((D/'author-before.json').read_bytes())
prep=json.loads((N/'brief-preparation.json').read_bytes());brief=(P/prep['brief']).read_bytes();assert len(brief)==prep['bytes'] and sha(brief)==prep['sha256'] and len(brief.decode())<120000
dispatch=json.loads((N/'dispatch.json').read_bytes())['structuredContent']
assert dispatch['status']=='running' and dispatch['workState']=='working' and dispatch['model']=='gpt-6-astra' and dispatch['providerInstanceId']=='codex'
assert {x['id']:x['value'] for x in dispatch['options']}==dict(reasoningEffort='high',serviceTier='default')
assert not dispatch['hasPendingQuestion'] and dispatch['pendingApproval'] is None
assert prep['all_previous_literal_guards_retained'] and prep['all_extra_guard_literals_verified'] and prep['standing_bytes_preserved']==5570
client='twenty-20261024-fresh-arithmetic-r162bn-codex-astra-r1';assert not any(x.get('clientRequestId')==client for x in work['tasks'])
now=datetime.now(timezone.utc).isoformat();new_index=len(base['tasks'])
fresh=copy.deepcopy(dispatch)
fresh.update(observed_utc=now,role='research',round=1,title='Arithmetic162bn: confirmed near-boundary billiard-rigidity discovery',clientRequestId=client,parent_thread='6742db91-d35c-44d0-a762-e5d9232f5177',target=dict(providerInstanceId='codex',model='gpt-6-astra',options=dict(reasoningEffort='high',serviceTier='default')),output='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bn/',brief=prep['brief'],brief_bytes=prep['bytes'],brief_sha256=prep['sha256'],submitted_prompt_contains_full_brief=True,source_index=147,source_family_navigation='Catalogue[242223,243744) includes BOTH named billiard manuscripts. One bounded14000byte window decoded147/148titles and only147body;148body unread,thirdheading boundaryonly. Two roots30blobs39entries28texts601146bytes,2compiledPDFs. Actual build/main.tex wrappers1976/Git9ba0372372381121bc3aac78c9271aedbea2357c and3364/Gitd405bd326b15aecee71b3544dfa03c772a9daf33. Parent operative proof not read.',round_namespace='Distinct near-boundary Birkhoff family. Entire smooth positive-curvature table/full continuous grazing foliation=>analytic boundary,joint analytic caustic collar,ellipse,and continuous physical caustic collar rigidity are paid. All stronger operative source/primary results must be read. No full-foliation/Cantor-family or leaf/transverse-regularity substitution. R162BM closed correct/technical,not reopened.',all_previous_literal_guards_and5570_standing_bytes_retained=True,all_new_literal_guard_twins_verified_before_dispatch=True,completed_direct_inputs=5,dispatch_receipt='discovery-arithmetic-r162bn-parent/dispatch.json',prospective_isolation='discovery-arithmetic-r162bn-parent/prospective-isolation.json',prompt_length_checked_before_dispatch=True,distinct_family=True,new_author_conversation=True,independent_review=False,accepted=False,count_change=0,parent_count_at_dispatch=19,publication='STOPPED',status_provenance='Fresh async receipt confirms Codex/GPT-6 Astra/high/default. No polling,watcher or foreign liveness query.')
def update(original):
 x=copy.deepcopy(original);r=x['tasks'][820];r.update(term)
 r.update(observed_utc=now,verdict='TECHNICAL',contribution_gate='TECHNICAL',conditional_on_full_correctness=True,condition_discharged_by_independent_correctness=True,entire_unchanged_scope=True,statement_sha256=intake['statement_sha256'],author_proof_sha256=intake['proof_sha256'],parent_intake='discovery-arithmetic-r162bm-parent/contribution-intake/intake.json',parent_assessment='discovery-arithmetic-r162bm-parent/contribution-intake/assessment.md',artifact_status='MATCH',artifact_verification='discovery-arithmetic-r162bm-parent/contribution-intake/verification.json',author_inputs_unchanged=True,sealed_review_root_unchanged=True,correctness_gate=None,accepted=False,count_change=0,status_provenance='Own terminal result queried once. Full assessment,primary comparison,reading limits,working/handoffs/verifier read. Complete compatible source/classical reduction covers unchanged theorem. No contribution re-review or peer-body query.')
 a=x['tasks'][817];a.update(disposition='CLOSED_CORRECT_TECHNICAL',correctness_gate='PASS',contribution_gate='TECHNICAL',contribution_correctness_condition_discharged=True,contribution_review_intake='discovery-arithmetic-r162bm-parent/contribution-intake/intake.json',accepted=False,count_change=0,no_desired_grade_retry=True,all_old_scopes_preserved=True)
 x['tasks'].append(copy.deepcopy(fresh))
 additions={'arithmetic_r162bm_final_disposition':dict(observed_utc=now,candidate='R162BM',author_task_index=817,correctness_task_index=819,contribution_task_index=820,correctness='PASS',contribution='TECHNICAL',condition_discharged=True,accepted=False,count_change=0,newAccepted=19,latestAcceptance='R041',publication='STOPPED'),'arithmetic_r162bn_dispatch':dict(task_index=new_index,taskId=dispatch['taskId'],source=147,status='running',serviceTier='default',distinct_family=True,catalogue_extent=[242223,243744],canonical_folders=2,canonical_blobs=30,canonical_entries=39,canonical_texts=28,canonical_text_bytes=601146,completed_direct_inputs=5,count_change=0,publication='STOPPED')}
 for k,value in additions.items():assert k not in x['current_work_snapshot'];x['current_work_snapshot'][k]=value
 assert [i for i,(a,b) in enumerate(zip(original['tasks'],x['tasks'])) if a!=b]==[817,820]
 assert all(x[k]==original[k] for k in original if k not in {'tasks','current_work_snapshot'})
 assert all(x['current_work_snapshot'][k]==a for k,a in original['current_work_snapshot'].items())
 return x
idx=enc(update(base));merged=enc(update(work));baseline=json.loads((D/'baseline.json').read_bytes())
note=('\n\n### R162BM closed correct/technical; distinct billiard discovery — '+now+'\n\n'
'R162BM receives full-scope correctness PASS relative to stipulated Source146 and full-scope contribution TECHNICAL. The correctness condition is discharged;ZERO substantial-result increment. The [final disposition](campaigns/2026-10-14/discovery-arithmetic-r162bm-parent/contribution-intake/assessment.md) preserves the unchanged theorem h_m(f_k)=log(pi*k)+o(1) across every sufficiently large positive real parameter. The contribution review supplies a full alternative source/classical derivation using ORIGINAL arrays,small initial second moments,and matching initial/terminal cap subtraction through one terminal Cauchy–Schwarz and positive weak-measure comparison. No joint multiscale compensation is necessary. Parent read entire20517byte assessment,10775byteprimarycomparison,8127bytelimits,working/handoffs/verifier;no independent parent source rereview. Reviewer read11texts145989bytes12blobs16entries,fourfullprimarypapers+errata+Blumenthal1–3,98pages15images;remaining sections/transitive ancestry unread. Post-freeze/pre-drafting BXY timing preserved,history0,no peer inspection. Parent/bundled artifact MATCH23payloads1433189bytes25files4dirs;all69author files/fullmodes unchanged,3wronganchorsrejected,restoredfixturepassed. Artifact tests do not grade mathematics. No retry,renaming or narrowing of closed candidate. New Arithmetic162bn Source147 near-boundary billiard-rigidity discovery dispatched Codex/GPT-6 Astra/high/default. Two named manuscripts selected from exact catalogue242223..243744,one boundedwindowdecoded147/148titles and only147body;148bodyunread. Two roots30blobs39entries28texts601146bytes,actualmainwrappers1976/3364bytes authenticated by pinned metadata. Entire continuous-phase/physical-caustic rigidity and analytic regularity already paid;parent operativeproofnotread. Five exact completed exceptions,ALL literalguards and5570standingbytes retained. Campaign19/20,latestR041;publication/downstreamSTOPPED. Unrelated uncommitted coordination remains preserved and unstaged.\n').encode();nj=hj+note
for e in json.loads((N/'private/completed-direct-inputs.json').read_bytes()):
 p=P/e['path'];a=p.read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256'] and p.stat().st_mode==e['mode']
for n,s in baseline['protected'].items():assert sha((P/n).read_bytes())==s
(D/'coordination-rebase.json').write_bytes(enc(dict(intake_head=baseline['head'],integration_head=h,changed_old_tasks=[817,820],new_task_index=new_index,foreign_uncommitted_task_indices=foreign,foreign_uncommitted_top_fields=foreign_top,foreign_edits_preserved_and_excluded=True,journal_prefix_preserved=True,index_tasks_after_sha256=sha(idx),working_tasks_after_sha256=sha(merged),count_change=0)))
(N/'registration.json').write_bytes(enc(dict(task_index=new_index,taskId=dispatch['taskId'],status_at_dispatch='running',distinct_family=True,model_options_verified=True,count_change=0,publication='STOPPED')))
names=['baseline.json','prospective-isolation.json','verify-intake.py','verification.json','task-status.json','assessment.md','intake.json','prepare-next.py','integration-guard.json','manage.py','coordination-rebase.json']
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
subprocess.run(['git','commit','-m','Close standard-map result as technical and start billiard discovery'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip() and git('show','HEAD:openai-proof-research/'+TP)==idx and (P/TP).read_bytes()==merged
assert snap(R)==json.loads((D/'review-before.json').read_bytes()) and snap(AR)==json.loads((D/'author-before.json').read_bytes())
for n,s in baseline['protected'].items():assert sha((P/n).read_bytes())==s
print(json.dumps(dict(commit=git('rev-parse','HEAD').decode().strip(),changed_old_tasks=[817,820],new_task_index=new_index,staged_paths=19,foreign_edits_preserved=foreign,correctness='PASS',contribution='TECHNICAL',count=19,author_and_review_seals_unchanged=True)))
