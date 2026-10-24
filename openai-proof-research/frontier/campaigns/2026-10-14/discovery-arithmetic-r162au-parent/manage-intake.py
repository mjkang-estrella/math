#!/usr/bin/env python3
"""Scoped compare-and-swap registration; preserve every foreign task and seal."""
from pathlib import Path
from datetime import datetime,timezone
import copy,fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[4];B=P/'frontier/campaigns/2026-10-14';D=Path(__file__).resolve().parent;N=B/'discovery-arithmetic-r162av-parent'
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
own=next(i for i,x in enumerate(old['tasks']) if x.get('clientRequestId')=='twenty-20261024-fresh-arithmetic-r162au-codex-astra-r1');assert own==774 and old['tasks'][own]['status']=='running'
assert not any(x.get('clientRequestId')=='twenty-20261024-fresh-arithmetic-r162av-codex-astra-r1' for x in old['tasks'])
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
v=json.loads((D/'verification.json').read_text());intake=json.loads((D/'intake.json').read_text());assert v['status']=='MATCH_WITH_BUNDLED_VERIFIER_DEFECT' and intake['disposition']=='PREFREEZE_NO_NOMINEE'
now=datetime.now(timezone.utc).isoformat();record=new['tasks'][own];record.update(terminal)
record.update(observed_utc=now,disposition='PREFREEZE_NO_NOMINEE',parent_intake='discovery-arithmetic-r162au-parent/intake.json',parent_assessment='discovery-arithmetic-r162au-parent/assessment.md',artifact_verification='discovery-arithmetic-r162au-parent/verification.json',artifact_status=v['status'],bundled_verifier_defect_preserved=True,no_new_diagnostic_selected=True,full_scopes_preserved=True,frozen_statement=False,author_proof_nominee=False,correctness_gate=None,contribution_gate=None,accepted=False,count_change=0,full_diagnostic=intake['full_diagnostic'],diagnostic_record=intake['diagnostic_record'],diagnostic_record_sha256=intake['diagnostic_record_sha256'],diagnostic_selected=False,paid_reduction=intake['paid_reduction'],retained_mathematics=intake['retained_mathematics'],unpaid_obligation=intake['unpaid_obligation'],canonical_text_objects_read_and_authenticated=15,canonical_folder_blobs=16,transitive_primary_reading_complete=False,optional_original_history_traversals=0,parent_full_intake_pending=False,status_provenance='Own completed task_status queried once and persisted; complete mathematical handoffs and reading limits read. No foreign liveness query or watcher.')
fresh=copy.deepcopy(dispatch)
fresh.update(observed_utc=now,role='research',round=1,target=dict(providerInstanceId='codex',model='gpt-6-astra',options=dict(reasoningEffort='high',serviceTier='default')),title='Arithmetic162av: confirmed three-machine-scheduling discovery',clientRequestId='twenty-20261024-fresh-arithmetic-r162av-codex-astra-r1',parent_thread='6742db91-d35c-44d0-a762-e5d9232f5177',output='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162av/',brief=prep['brief'],brief_sha256=prep['sha256'],brief_bytes=prep['bytes'],submitted_prompt_contains_full_brief=True,source_index=124,source_family_navigation='Exact catalogue[205987,207322);one folder,69 blobs/86 entries,including55 vendored runtime blobs and13 non-PDF nonvendor texts. Actual build/paper.tex25458 bytes/blob00a3e5fed881652cd68cc6a522602f6a66e5a3ab. One bounded14000-byte window at202797 decoded only122/124 numeric-bold titles and124 body;122 body/remainder unread,next heading boundary only. One body screen,no parent proof reading. Source122 title skipped on known completed Structural163 paid context,not fresh body reading.',round_namespace='Three-machine scheduling family distinct from preceding weighted edit task,without global history-clearance claim. Entire uniform deterministic polynomial-time minimum makespan,exact deadline feasibility and constructive scheduling for nonpreemptive unit-length jobs with arbitrary explicit precedence constraints on three identical machines already paid,including stronger internal mechanisms. All older scopes/dispositions unchanged.',all_previous_literal_guards_and5570_standing_bytes_retained=True,all_new_literal_guard_twins_verified_before_dispatch=True,dispatch_receipt='discovery-arithmetic-r162av-parent/dispatch.json',prospective_isolation='discovery-arithmetic-r162av-parent/prospective-isolation.json',distinct_family=True,new_author_conversation=True,independent_review=False,accepted=False,count_change=0,parent_count_at_dispatch=19,publication='STOPPED',status_provenance='Actual fresh async delegate_task receipt verified as Astra/high/default; no polling/watcher or foreign liveness query.')
new_index=len(new['tasks']);new['tasks'].append(fresh)
note='Arithmetic162au archived PREFREEZE/no nominee. Retained fixed-C/fixed-epsilon integer metric-oracle edit comparison costs expected N^(8/5+o(1));same-domain almost-linear weighted seed remains unconstructed. No theorem/diagnostic selected or graded. Unchanged bundled verifier rejects unsorted unique manifest order;independent exact membership/hash/mode authentication and single-assertion in-memory correction passed,all sealed bytes preserved. Arithmetic162av Source124 three-machine scheduling discovery dispatched on Codex/GPT-6 Astra/high/default;entire stipulated source and stronger operations credited. All older scopes/dispositions preserved. Campaign19/20,latestR041;publication STOPPED.'
new['last_parent_progress']=note;snap=new['current_work_snapshot'];snap.update(observed_utc=now,note=note)
snap['arithmetic_r162au_archive']=dict(task_index=own,intake='discovery-arithmetic-r162au-parent/intake.json',disposition='PREFREEZE_NO_NOMINEE',frozen_statement=False,no_new_diagnostic_selected=True,diagnostic_selected=False,correctness_gate=None,contribution_gate=None,accepted=False,count_change=0)
snap['arithmetic_r162av_dispatch']=dict(task_index=new_index,taskId=dispatch['taskId'],status=dispatch['status'],brief=prep['brief'],source=124,catalogue_extent=[205987,207322],distinct_family=True,original_brief_guards_checked_before_creation=True,both_new_literal_twins_verified=True,new_family_screens=1,private_local_inputs_and_metadata_retained=True,foreign_live_queries=False,publication='STOPPED',count_change=0)
changed=[i for i,(a,b) in enumerate(zip(old['tasks'],new['tasks'])) if a!=b];assert changed==[own]
assert all(new[k]==old[k] for k in old if k not in {'tasks','last_parent_progress','current_work_snapshot'})
allowed={'observed_utc','note','arithmetic_r162au_archive','arithmetic_r162av_dispatch'};assert all(snap[k]==x for k,x in old['current_work_snapshot'].items() if k not in allowed)
addition=('\n\n### Arithmetic162au archive and three-machine scheduling discovery dispatch — '+now+'\n\n'+note+'\n\nParent [assessment](campaigns/2026-10-14/discovery-arithmetic-r162au-parent/assessment.md) retains the exact metric-oracle model,fixed-C/fixed-epsilon expected cost,value certification,irregular-grid/leaf-frontier compatibility and unconstructed fast seed. Complete mathematics,source comparison,reading limits,chronology and handoffs read. Independent read-only authentication matched49 payloads/4561569 bytes,51 whole-root identities/full modes,15 pinned text bindings,20 tree entries and5 unchanged completed inputs. The ORIGINAL bundled verifier still rejects unique unsorted manifest order;only its ordering assertion was changed IN MEMORY to uniqueness for a separate run. Exact membership/duplicates independently checked;three wrong anchors rejected;original verifier and sealed root remain untouched. Artifact checks assign no mathematical gate. Canonical15 text objects fully read by author;DKK complete,other primary extents partial,transitive ancestry incomplete. Late recovery/visual-reading limits disclosed;no optional history traversal. Finite net/metric/leaf/atomic probes are sanity evidence only,no complete algorithm executed. Private source/primary bodies,copied exceptions and named metadata unstaged. New brief retains all inherited literal guards and5570 standing bytes;five exact completed exceptions supply context only. Source124 actual wrapper confirmed;69 blobs/86 entries include55 vendor runtime blobs,13 operative non-PDF nonvendor texts. One bounded body screen,no parent proof reading;122 trace-reconstruction title skipped on known completed context without its body. All older scopes/dispositions,foreign records and original seals preserved. No foreign liveness query,public action,downstream work,polling or watcher.\n').encode()
next_t=(json.dumps(new,ensure_ascii=False,indent=2)+'\n').encode();next_j=raw_j+addition
dump(D/'coordination-rebase.json',dict(intake_head=baseline['head'],integration_head=head,head_advanced=head!=baseline['head'],before_task_count=len(old['tasks']),after_task_count=len(new['tasks']),changed_old_task_indices=changed,new_task_index=new_index,all_other_tasks_preserved=True,all_other_top_fields_preserved=True,journal_prefix_preserved=True,protected_modifications_preserved=True,tasks_before_sha256=sha(raw_t),tasks_after_sha256=sha(next_t),journal_before_sha256=sha(raw_j),journal_after_sha256=sha(next_j),integration_original_brief_guard_checks=checks,no_foreign_live_queries=True))
dump(N/'registration.json',dict(task_index=new_index,taskId=dispatch['taskId'],status_at_dispatch=dispatch['status'],distinct_family=True,model_options_verified=True,count_change=0,publication='STOPPED'))
(D/'private/intake/our-tasks-after.json').write_bytes(next_t);(D/'private/intake/our-journal-after.md').write_bytes(next_j)
assert snapshot(B/'fresh-arithmetic-discovery-r162au')==json.loads((D/'private/intake/root-before.json').read_text())
for x in json.loads((N/'private/completed-direct-inputs.json').read_text()):
 f=P/x['path'];a=f.read_bytes();assert len(a)==x['bytes'] and sha(a)==x['sha256'] and f.stat().st_mode==x['mode']
assert git('rev-parse','HEAD').decode().strip()==head and (P/TP).read_bytes()==raw_t and (P/JP).read_bytes()==raw_j
(P/TP).write_bytes(next_t);(P/JP).write_bytes(next_j)
names=['assessment.md','intake.json','verification.json','verify-intake.py','task-status.json','intake-baseline.json','intake-prospective-isolation.json','integration-guard.json','prepare-next.py','manage-intake.py','coordination-rebase.json']
paths=[(D/x).relative_to(P).as_posix() for x in names]+[(N/x).relative_to(P).as_posix() for x in ['brief-preparation.json','capabilities.json','dispatch.json','prospective-isolation.json','registration.json']]+[prep['brief'],TP,JP]
assert len(paths)==len(set(paths))==19
assert git('rev-parse','HEAD').decode().strip()==head and (P/TP).read_bytes()==next_t and (P/JP).read_bytes()==next_j
subprocess.run(['git','add','--',*paths],cwd=P,check=True)
assert {x for x in git('diff','--cached','--name-only','-z').decode().split('\0') if x}=={'openai-proof-research/'+x for x in paths}
for n in paths:assert git('show',':openai-proof-research/'+n)==(P/n).read_bytes()
subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True);assert git('rev-parse','HEAD').decode().strip()==head
subprocess.run(['git','commit','-m','Archive weighted edit comparison and start scheduling research'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip()
assert snapshot(B/'fresh-arithmetic-discovery-r162au')==json.loads((D/'private/intake/root-before.json').read_text())
assert git('show','HEAD:openai-proof-research/'+TP)==next_t and git('show','HEAD:openai-proof-research/'+JP)==next_j
for n,h in baseline['protected'].items():assert sha((P/n).read_bytes())==h
print(json.dumps(dict(commit=git('rev-parse','HEAD').decode().strip(),changed_old_tasks=changed,new_task_index=new_index,all_other_tasks_preserved=True,staged_allowed_paths=19,campaign_count=19,index_empty=True,protected_modifications_preserved=True)))
