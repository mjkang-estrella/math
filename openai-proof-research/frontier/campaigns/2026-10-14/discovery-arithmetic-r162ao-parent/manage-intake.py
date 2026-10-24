#!/usr/bin/env python3
"""Scoped compare-and-swap registration; preserve every foreign task and seal."""
from pathlib import Path
from datetime import datetime,timezone
import copy,fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[4];B=P/'frontier/campaigns/2026-10-14';D=Path(__file__).resolve().parent;N=B/'discovery-arithmetic-r162ap-parent'
TP='frontier/campaigns/2026-10-14/tasks.json';JP='frontier/NEW-TEN-2026-10-14.md'
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def snapshot(root):
 out={}
 for f in root.rglob('*'):
  assert not f.is_symlink()
  if f.is_file():
   a=f.read_bytes();out[f.relative_to(root).as_posix()]=dict(bytes=len(a),sha256=sha(a),mode=f.stat().st_mode)
 return out
assert not git('diff','--cached','--name-only').strip()
head=git('rev-parse','HEAD').decode().strip();raw_t=git('show',head+':openai-proof-research/'+TP);raw_j=git('show',head+':openai-proof-research/'+JP)
assert (P/TP).read_bytes()==raw_t and (P/JP).read_bytes()==raw_j,'Concurrent uncommitted coordination; no overwrite.'
old=json.loads(raw_t);new=copy.deepcopy(old)
assert old['newAccepted']==19 and old['target']==20 and old['latestAcceptance']=='R041'
own=next(i for i,x in enumerate(old['tasks']) if x.get('clientRequestId')=='twenty-20261023-fresh-arithmetic-r162ao-codex-astra-r1');assert own==741 and old['tasks'][own]['status']=='running'
assert not any(x.get('clientRequestId')=='twenty-20261024-fresh-arithmetic-r162ap-codex-astra-r1' for x in old['tasks'])
baseline=json.loads((D/'intake-baseline.json').read_text())
for n,h in baseline['protected'].items():assert sha((P/n).read_bytes())==h
checks=[];guard=json.loads((N/'prospective-isolation.json').read_text())
for i,x in enumerate(old['tasks']):
 if i==own or x.get('status') not in {'running','queued','waiting'} or not x.get('brief'):continue
 a=(P/x['brief']).read_bytes();patterns=[z for z in re.findall(r'\*[^\s,;()]*\*',a.decode()) if z not in {'*','**'}]
 ms={n:[z for z in patterns if fnmatch.fnmatchcase(n.casefold(),z.casefold())] for n in guard['namespaces']};assert all(ms.values())
 checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=ms))
terminal=json.loads((D/'task-status.json').read_text())['structuredContent'];dispatch=json.loads((N/'dispatch.json').read_text())['structuredContent']
assert terminal['taskId']==old['tasks'][own]['taskId'] and terminal['status']=='completed' and terminal['workState']=='result_available'
assert not terminal['hasPendingChildRuns'] and not terminal['hasPendingQuestion'] and terminal['pendingApproval'] is None
assert dispatch['status']=='running' and dispatch['workState']=='working' and dispatch['providerInstanceId']=='codex' and dispatch['model']=='gpt-6-astra'
assert {x['id']:x['value'] for x in dispatch['options']}==dict(reasoningEffort='high',serviceTier='default')
assert not dispatch['hasPendingQuestion'] and dispatch['pendingApproval'] is None
prep=json.loads((N/'brief-preparation.json').read_text());brief=(P/prep['brief']).read_bytes();assert len(brief)==prep['bytes'] and sha(brief)==prep['sha256']
assert prep['all_previous_literal_guards_retained'] and prep['all_extra_guard_literals_verified'] and prep['standing_bytes_preserved']==5570
v=json.loads((D/'verification.json').read_text());intake=json.loads((D/'intake.json').read_text());assert v['status']=='MATCH' and intake['disposition']=='PREFREEZE_NO_NOMINEE'
now=datetime.now(timezone.utc).isoformat();record=new['tasks'][own];record.update(terminal)
record.update(observed_utc=now,disposition='PREFREEZE_NO_NOMINEE',parent_intake='discovery-arithmetic-r162ao-parent/intake.json',parent_assessment='discovery-arithmetic-r162ao-parent/assessment.md',artifact_verification='discovery-arithmetic-r162ao-parent/verification.json',full_diagnostic_preserved=True,full_scopes_preserved=True,frozen_statement=False,author_proof_nominee=False,correctness_gate=None,contribution_gate=None,accepted=False,count_change=0,full_diagnostic=intake['full_diagnostic'],diagnostic_record=intake['diagnostic_record'],diagnostic_record_sha256=intake['diagnostic_record_sha256'],neither_diagnostic_nor_negation_proved=True,paid_reduction=intake['paid_reduction'],retained_mathematics=intake['retained_mathematics'],unpaid_obligation=intake['unpaid_obligation'],canonical_text_objects_read_and_authenticated=11,canonical_folder_blobs=13,transitive_primary_reading_complete=False,optional_original_history_traversals=0,parent_full_intake_pending=False,status_provenance='Own completed task_status receipt retained from initial intake; resumed artifact authentication/integration. No duplicate status query, foreign liveness query or watcher.')
fresh=copy.deepcopy(dispatch)
fresh.update(observed_utc=now,role='research',round=1,target=dict(providerInstanceId='codex',model='gpt-6-astra',options=dict(reasoningEffort='high',serviceTier='default')),title='Arithmetic162ap: confirmed perfect-matching counting and entropy discovery',clientRequestId='twenty-20261024-fresh-arithmetic-r162ap-codex-astra-r1',parent_thread='6742db91-d35c-44d0-a762-e5d9232f5177',output='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ap/',brief=prep['brief'],brief_sha256=prep['sha256'],brief_bytes=prep['bytes'],submitted_prompt_contains_full_brief=True,source_index=113,source_family_navigation='Exact catalogue[186982,189149); two confirmed canonical folders,21 blobs/28 entries. Actual build/main.tex wrappers153001 and2704 bytes. One bounded14000-byte window, only first2 numeric-bold titles113/114 decoded, only113 body selected. Parent source-proof reading NONE.',round_namespace='Distinct perfect-matching counting and entropy family; both full FPRAS/zero detection and boundary entropy/face-dimension theorems plus stronger compatible internal operations are paid. Approximate-circuit AC, all earlier full targets and closed dispositions remain unchanged.',all_previous_literal_guards_and5570_standing_bytes_retained=True,all_new_literal_guard_twins_verified_before_dispatch=True,dispatch_receipt='discovery-arithmetic-r162ap-parent/dispatch.json',prospective_isolation='discovery-arithmetic-r162ap-parent/prospective-isolation.json',distinct_family=True,new_author_conversation=True,independent_review=False,accepted=False,count_change=0,parent_count_at_dispatch=19,publication='STOPPED',status_provenance='Actual fresh async delegate_task receipt verified as Astra/high/default; no polling/watcher or foreign liveness query.')
new_index=len(new['tasks']);new['tasks'].append(fresh)
note='Arithmetic162ao archived PREFREEZE/no nominee. Full all-length uniform two-sided error-1/3 depth-three circuit diagnostic AC remains unfrozen and unproved; neither AC nor its negation established. Individual all-input CNF bounds and adaptive subcube robustness are paid; one joint same approximate-cover budget remains unpaid. No grades/count. Arithmetic162ap distinct Source113 perfect-matching counting and entropy discovery dispatched on Codex/GPT-6 Astra/high/default. Both supplied complete theorems and stronger compatible operations credited. All old scopes/dispositions and foreign work preserved. Campaign19/20,latestR041;publication STOPPED.'
new['last_parent_progress']=note;snap=new['current_work_snapshot'];snap.update(observed_utc=now,note=note)
snap['arithmetic_r162ao_archive']=dict(task_index=own,intake='discovery-arithmetic-r162ao-parent/intake.json',disposition='PREFREEZE_NO_NOMINEE',frozen_statement=False,full_diagnostic_preserved=True,neither_diagnostic_nor_negation_proved=True,correctness_gate=None,contribution_gate=None,accepted=False,count_change=0)
snap['arithmetic_r162ap_dispatch']=dict(task_index=new_index,taskId=dispatch['taskId'],status=dispatch['status'],brief=prep['brief'],source=113,catalogue_extent=[186982,189149],distinct_family=True,original_brief_guards_checked_before_creation=True,both_new_literal_twins_verified=True,new_family_screens=1,private_local_inputs_and_metadata_retained=True,foreign_live_queries=False,publication='STOPPED',count_change=0)
changed=[i for i,(a,b) in enumerate(zip(old['tasks'],new['tasks'])) if a!=b];assert changed==[own]
assert all(new[k]==old[k] for k in old if k not in {'tasks','last_parent_progress','current_work_snapshot'})
allowed={'observed_utc','note','arithmetic_r162ao_archive','arithmetic_r162ap_dispatch'};assert all(snap[k]==x for k,x in old['current_work_snapshot'].items() if k not in allowed)
addition=('\n\n### Arithmetic162ao archive and distinct perfect-matching research dispatch — '+now+'\n\n'+note+'\n\nParent [assessment](campaigns/2026-10-14/discovery-arithmetic-r162ao-parent/assessment.md) preserves every language,machine,all-length,total-gate and whole-cube constant-error quantifier. Complete author mathematics,comparison,limits and handoffs were read at initial intake;resumed verification matched55 payloads/5039387 bytes,58 whole-root identities/full modes,11 pinned textual bindings,19 tree entries and5 unchanged direct inputs. Four existing copied cases behaved as expected;artifact authentication is not a mathematical gate. Canonical text reading complete;transitive primary reading incomplete,late visual pages disclosed,no optional original-history traversal. Particular-evaluator and abstract-moment counterexamples do not refute existential AC. No sealed bytes changed or source/private bodies staged. New brief preserves all inherited literal guards and5570 standing bytes;five exact completed exceptions supply scope/payment context only. Source113 two actual wrappers confirmed;no parent proof reading. Foreign original brief checked before creation and integration;no foreign liveness query,public action or downstream work.\n').encode()
next_t=(json.dumps(new,ensure_ascii=False,indent=2)+'\n').encode();next_j=raw_j+addition
dump(D/'coordination-rebase.json',dict(intake_head=baseline['head'],integration_head=head,head_advanced=head!=baseline['head'],before_task_count=len(old['tasks']),after_task_count=len(new['tasks']),changed_old_task_indices=changed,new_task_index=new_index,all_other_tasks_preserved=True,all_other_top_fields_preserved=True,journal_prefix_preserved=True,protected_modifications_preserved=True,tasks_before_sha256=sha(raw_t),tasks_after_sha256=sha(next_t),journal_before_sha256=sha(raw_j),journal_after_sha256=sha(next_j),integration_original_brief_guard_checks=checks,no_foreign_live_queries=True))
dump(N/'registration.json',dict(task_index=new_index,taskId=dispatch['taskId'],status_at_dispatch=dispatch['status'],distinct_family=True,model_options_verified=True,count_change=0,publication='STOPPED'))
(D/'private/intake/our-tasks-after.json').write_bytes(next_t);(D/'private/intake/our-journal-after.md').write_bytes(next_j)
assert snapshot(B/'fresh-arithmetic-discovery-r162ao')==json.loads((D/'private/intake/root-before.json').read_text())
for x in json.loads((N/'private/completed-direct-inputs.json').read_text()):
 f=P/x['path'];a=f.read_bytes();assert len(a)==x['bytes'] and sha(a)==x['sha256'] and f.stat().st_mode==x['mode']
assert git('rev-parse','HEAD').decode().strip()==head and (P/TP).read_bytes()==raw_t and (P/JP).read_bytes()==raw_j
(P/TP).write_bytes(next_t);(P/JP).write_bytes(next_j)
names=['assessment.md','intake.json','verification.json','verify-intake.py','task-status.json','intake-baseline.json','intake-prospective-isolation.json','resume-prospective-isolation.json','integration-guard.json','prepare-next.py','manage-intake.py','coordination-rebase.json']
paths=[(D/x).relative_to(P).as_posix() for x in names]+[(N/x).relative_to(P).as_posix() for x in ['brief-preparation.json','capabilities.json','dispatch.json','prospective-isolation.json','registration.json']]+[prep['brief'],TP,JP]
assert len(paths)==len(set(paths))==20
assert git('rev-parse','HEAD').decode().strip()==head and (P/TP).read_bytes()==next_t and (P/JP).read_bytes()==next_j
subprocess.run(['git','add','--',*paths],cwd=P,check=True)
assert {x for x in git('diff','--cached','--name-only','-z').decode().split('\0') if x}=={'openai-proof-research/'+x for x in paths}
for n in paths:assert git('show',':openai-proof-research/'+n)==(P/n).read_bytes()
subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True);assert git('rev-parse','HEAD').decode().strip()==head
subprocess.run(['git','commit','-m','Archive approximate circuit gap and resume matching research'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip()
assert git('show','HEAD:openai-proof-research/'+TP)==next_t and git('show','HEAD:openai-proof-research/'+JP)==next_j
for n,h in baseline['protected'].items():assert sha((P/n).read_bytes())==h
print(json.dumps(dict(commit=git('rev-parse','HEAD').decode().strip(),changed_old_tasks=changed,new_task_index=new_index,all_other_tasks_preserved=True,staged_allowed_paths=20,campaign_count=19,index_empty=True,protected_modifications_preserved=True)))
