#!/usr/bin/env python3
"""Register this intake and dispatch, then commit only explicit parent paths."""
from pathlib import Path
from datetime import datetime, timezone
import copy
import fnmatch
import hashlib
import json
import re
import subprocess

P=Path(__file__).resolve().parents[4]
B=P/'frontier/campaigns/2026-10-14'
D=Path(__file__).resolve().parent
N=B/'discovery-arithmetic-r162ad-parent'
TP='frontier/campaigns/2026-10-14/tasks.json'
JP='frontier/NEW-TEN-2026-10-14.md'
def git(*args,**kw):
    return subprocess.check_output(['git',*args],cwd=P,**kw)
def sha(data):
    return hashlib.sha256(data).hexdigest()
def dump(path,value):
    path.write_text(json.dumps(value,ensure_ascii=False,indent=2)+'\n')
assert not git('diff','--cached','--name-only').strip()
head=git('rev-parse','HEAD').decode().strip()
raw_t=git('show',head+':openai-proof-research/'+TP)
raw_j=git('show',head+':openai-proof-research/'+JP)
assert (P/TP).read_bytes()==raw_t and (P/JP).read_bytes()==raw_j, 'Concurrent uncommitted coordination; leave every working byte untouched.'
old=json.loads(raw_t);new=copy.deepcopy(old)
assert old['newAccepted']==19 and old['target']==20
own_index=next(i for i,t in enumerate(old['tasks']) if t.get('clientRequestId')=='twenty-20261023-fresh-arithmetic-r162ac-codex-astra-r1')
assert old['tasks'][own_index]['status']=='running'
assert not any(t.get('clientRequestId')=='twenty-20261023-fresh-arithmetic-r162ad-codex-astra-r1' for t in old['tasks'])
baseline=json.loads((D/'intake-baseline.json').read_text())
for name,anchor in baseline['protected'].items():
    assert sha((P/name).read_bytes())==anchor

guard=json.loads((N/'prospective-isolation.json').read_text())
guardchecks=[]
for i,t in enumerate(old['tasks']):
    if i==own_index or t.get('status') not in {'running','queued','waiting'} or 'brief' not in t:
        continue
    raw=(P/t['brief']).read_bytes()
    patterns=[g for g in re.findall(r'\*[^\s,;()]*\*',raw.decode()) if g not in {'*','**'}]
    matches={name:[g for g in patterns if fnmatch.fnmatchcase(name.casefold(),g.casefold())] for name in guard['namespaces']}
    assert all(matches.values()), (i,matches)
    guardchecks.append(dict(task_index=i,original_brief=t['brief'],sha256=sha(raw),matches=matches))
terminal=json.loads((D/'task-status.json').read_text())['structuredContent']
dispatch=json.loads((N/'dispatch.json').read_text())['structuredContent']
assert terminal['taskId']==old['tasks'][own_index]['taskId']
assert terminal['status']=='completed' and terminal['workState']=='result_available'
assert not terminal['hasPendingChildRuns'] and not terminal['hasPendingQuestion'] and terminal['pendingApproval'] is None
assert dispatch['status'] in {'running','queued'} and dispatch['providerInstanceId']=='codex' and dispatch['model']=='gpt-6-astra'
assert {x['id']:x['value'] for x in dispatch['options']}==dict(reasoningEffort='high',serviceTier='default')
supplement=json.loads((N/'supplement-delivery.json').read_text())['structuredContent']
assert supplement['delivery']=='steered' and supplement['runId']==dispatch['childRunId']
assert supplement['threadId']==dispatch['childThreadId']
now=datetime.now(timezone.utc).isoformat()
own=new['tasks'][own_index]
own.update(terminal)
own.update(observed_utc=now,disposition='ARCHIVED_PREFREEZE_NO_NOMINEE',parent_intake='discovery-arithmetic-r162ac-parent/intake.json',parent_assessment='discovery-arithmetic-r162ac-parent/assessment.md',artifact_verification='discovery-arithmetic-r162ac-parent/verification.json',frozen_statement=False,correctness_gate=None,contribution_gate=None,accepted=False,count_change=0,full_scope_preserved=True,mathematical_gap='ONE uniform finite real affine PSD pencil size for EVERY PSD-valued ternary3-by-3 quadratic map and its SAME degree20 polynomial,ENTIRE closed23-coordinate cone. Pointwise simultaneous matching and conditional singular-boundary assembly are paid; one uniformly bounded common matching-function space remains a sufficient unpaid bridge,not necessary to every possible proof.',status_provenance='Own terminal task_status intake only; no watcher,child polling or foreign live query.')
prep=json.loads((N/'brief-preparation.json').read_text())
brief_path=P/prep['brief'];brief=brief_path.read_bytes()
assert len(brief)==prep['bytes'] and sha(brief)==prep['sha256']
record=copy.deepcopy(dispatch)
record.update(observed_utc=now,role='research',round=1,target=dict(providerInstanceId='codex',model='gpt-6-astra',options=dict(reasoningEffort='high',serviceTier='default')),title='Arithmetic162ad: confirmed Euclidean-Steinitz operative-proof discovery',clientRequestId='twenty-20261023-fresh-arithmetic-r162ad-codex-astra-r1',parent_thread='6742db91-d35c-44d0-a762-e5d9232f5177',output='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ad/',brief=prep['brief'],brief_sha256=prep['sha256'],brief_bytes=prep['bytes'],submitted_prompt_contains_full_brief=True,source_index=97,source_family_navigation='DISTINCT Source097; exact catalogue[160713,161938),one confirmed folder,11 blobs/13 complete-tree entries including roots,actual build/main.tex. Source096 body not decoded. Parent metadata only.',round_namespace='Distinct Euclidean-Steinitz signing/rearrangement family. Entire stipulated prescribed-order all-prefix signing and zero-sum reordering sqrt(d) theorems and stronger actual proof operations are paid. Full D33,modified log-Sobolev and all previous scopes preserved.',all_previous_literal_guards_and5570_standing_bytes_retained=True,dispatch_receipt='discovery-arithmetic-r162ad-parent/dispatch.json',prospective_isolation='discovery-arithmetic-r162ad-parent/prospective-isolation.json',accepted=False,count_change=0,parent_count_at_dispatch=19,publication='STOPPED',status_provenance='Actual async delegate_task dispatch; explicit high/default options verified. No polling or watcher.')
record['supplemental_isolation']=dict(instruction='discovery-arithmetic-r162ad-parent/supplemental-isolation.txt',sha256=sha((N/'supplemental-isolation.txt').read_bytes()),delivery='discovery-arithmetic-r162ad-parent/supplement-delivery.json',same_running_turn=True,original_brief_unchanged=True,parent_limitation='discovery-arithmetic-r162ac-parent/brief-validation-limit.json',explicit_no_r_twin_added_by_steer=True,broader_exclusions_already_binding=True,no_backdated_timing_claim=True)
new_index=len(new['tasks']);new['tasks'].append(record)
note='Arithmetic162ac archived PREFREEZE/no nominee; full uniform ternary-family lift diagnostic remains unproved. Distinct Arithmetic162ad dispatched on Source097 Euclidean Steinitz-Bergstrom signing/rearrangement, Codex/GPT-6 Astra/high/default. Explicit new no-r guard corrected by a same-running-turn steer; timing limits recorded. Campaign19/20 latestR041 one remains; publicationSTOPPED. All foreign task records preserved.'
new['last_parent_progress']=note
snapshot=new['current_work_snapshot'];snapshot.update(observed_utc=now,note=note)
snapshot['arithmetic_r162ac_archive']=dict(task_index=own_index,status='PREFREEZE_NO_NOMINEE',intake='discovery-arithmetic-r162ac-parent/intake.json',full_diagnostic='ONE universal finite pencil size for EVERY real PSD-valued homogeneous Q:R3->Sym3 and its SAME source p_Q/direction e,ENTIRE closed23-coordinate cone;zero maps,kernels,rank changes,singular X and arbitrary real coefficients included. No jointly coefficient-affine,algorithmic,approximate or minimality claim.',unpaid_operation=own['mathematical_gap'],correctness_gate=None,contribution_gate=None,accepted=False,count_change=0)
snapshot['arithmetic_r162ad_dispatch']=dict(task_index=new_index,taskId=dispatch['taskId'],status=dispatch['status'],brief=prep['brief'],source='097',catalogue_extent=[160713,161938],original_brief_guards_checked_before_creation=True,private_local_inputs_and_metadata_retained=True,foreign_live_queries=False,publication='STOPPED')
changed=[i for i,(a,b) in enumerate(zip(old['tasks'],new['tasks'])) if a!=b]
assert changed==[own_index]
assert all(new[k]==old[k] for k in old if k not in {'tasks','last_parent_progress','current_work_snapshot'})
assert all(snapshot[k]==v for k,v in old['current_work_snapshot'].items() if k not in {'observed_utc','note','arithmetic_r162ac_archive','arithmetic_r162ad_dispatch'})
addition=('\n\n### Arithmetic162ac intake and distinct Arithmetic162ad dispatch — '+now+'\n\n'+note+'\n\nParent assessment: [discovery-arithmetic-r162ac-parent/assessment.md](campaigns/2026-10-14/discovery-arithmetic-r162ac-parent/assessment.md). Read-only artifact checks matched79 selected files,33 canonical bindings and the unchanged82-file root; these are not mathematical gates. No theorem was frozen. The full D33 uniform lift scope,paid simultaneous matching,and sufficient common-space bridge remain unchanged. Actual primary/transitive reading and isolation limits are recorded. The next full brief requires the complete Source097 operative proof,including its prescribed-order signing and stronger actual proof operations. An omitted explicit no-r namespace twin was corrected by a same-running-task process steer;broader guards were already binding,original brief bytes unchanged,and timing limits are recorded. All previous literal guards and5570 standing bytes retained. Asynchronous research only; no polling,watcher,public action or count change.\n').encode()
next_t=(json.dumps(new,ensure_ascii=False,indent=2)+'\n').encode();next_j=raw_j+addition
dump(D/'coordination-rebase.json',dict(intake_head=baseline['head'],integration_head=head,head_advanced=head!=baseline['head'],before_task_count=len(old['tasks']),after_task_count=len(new['tasks']),changed_old_task_indices=changed,new_task_index=new_index,all_other_tasks_preserved=True,all_other_top_fields_preserved=True,journal_prefix_preserved=True,protected_modifications_preserved=True,tasks_before_sha256=sha(raw_t),tasks_after_sha256=sha(next_t),journal_before_sha256=sha(raw_j),journal_after_sha256=sha(next_j),integration_original_brief_guard_checks=guardchecks,no_foreign_live_queries=True))
dump(N/'registration.json',dict(task_index=new_index,taskId=dispatch['taskId'],status_at_dispatch=dispatch['status'],provider_model_options_verified=True,count_change=0,publication='STOPPED'))
(D/'private/intake/our-tasks-after.json').write_bytes(next_t)
(D/'private/intake/our-journal-after.md').write_bytes(next_j)
subprocess.run(['python3','-I','-B',str(D/'verify-intake.py')],cwd=P,check=True,stdout=subprocess.DEVNULL)
for x in json.loads((N/'private/completed-direct-inputs.json').read_text()):
    p=P/x['path'];data=p.read_bytes()
    assert len(data)==x['bytes'] and sha(data)==x['sha256'] and p.stat().st_mode==x['mode']
assert git('rev-parse','HEAD').decode().strip()==head
assert (P/TP).read_bytes()==raw_t and (P/JP).read_bytes()==raw_j
(P/TP).write_bytes(next_t);(P/JP).write_bytes(next_j)
paths=[(D/x).relative_to(P).as_posix() for x in ['assessment.md','intake.json','verification.json','verify-intake.py','manage.py','intake-baseline.json','intake-prospective-isolation.json','task-status.json','coordination-rebase.json','integration-guard.json','prepare-next.py','brief-validation-limit.json']]
paths += [(N/x).relative_to(P).as_posix() for x in ['brief-preparation.json','capabilities.json','dispatch.json','prospective-isolation.json','registration.json','supplemental-isolation.txt','supplement-delivery.json']]
paths += [prep['brief'],TP,JP]
assert len(paths)==len(set(paths))==22
subprocess.run(['git','add','--',*paths],cwd=P,check=True)
expected={'openai-proof-research/'+x for x in paths}
assert {x for x in git('diff','--cached','--name-only','-z').decode().split('\0') if x}==expected
for name in paths:
    assert git('show',':openai-proof-research/'+name)==(P/name).read_bytes()
subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
assert git('rev-parse','HEAD').decode().strip()==head
subprocess.run(['git','commit','-m','Archive hyperbolicity research and start Euclidean signing discovery'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip()
assert git('show','HEAD:openai-proof-research/'+TP)==next_t and git('show','HEAD:openai-proof-research/'+JP)==next_j
for name,anchor in baseline['protected'].items():
    assert sha((P/name).read_bytes())==anchor
print(json.dumps(dict(commit=git('rev-parse','HEAD').decode().strip(),archived_task_index=own_index,new_task_index=new_index,changed_old_tasks=changed,staged_allowed_paths=22,campaign_count=19,index_empty=True,protected_modifications_preserved=True)))
