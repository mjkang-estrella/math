#!/usr/bin/env python3
"""Register immutable nominee and two independent reviews with a scoped local commit."""
from pathlib import Path
from datetime import datetime,timezone
import copy
import fnmatch
import hashlib
import json
import re
import subprocess

P=Path(__file__).resolve().parents[4]
B=P/'frontier/campaigns/2026-10-14'
D=Path(__file__).resolve().parent
TP='frontier/campaigns/2026-10-14/tasks.json'
JP='frontier/NEW-TEN-2026-10-14.md'
def git(*args):return subprocess.check_output(['git',*args],cwd=P)
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
assert not git('diff','--cached','--name-only').strip()
head=git('rev-parse','HEAD').decode().strip()
raw_t=git('show',head+':openai-proof-research/'+TP)
raw_j=git('show',head+':openai-proof-research/'+JP)
assert (P/TP).read_bytes()==raw_t and (P/JP).read_bytes()==raw_j,'Concurrent uncommitted coordination; nothing overwritten.'
old=json.loads(raw_t);new=copy.deepcopy(old);assert old['newAccepted']==19 and old['target']==20
own_index=next(i for i,x in enumerate(old['tasks']) if x.get('clientRequestId')=='twenty-20261023-fresh-arithmetic-r162aj-codex-astra-r1')
assert old['tasks'][own_index]['status']=='running'
terminal=json.loads((D/'task-status.json').read_text())['structuredContent']
assert terminal['taskId']==old['tasks'][own_index]['taskId'] and terminal['status']=='completed' and terminal['workState']=='result_available'
assert not terminal['hasPendingChildRuns'] and not terminal['hasPendingQuestion'] and terminal['pendingApproval'] is None
baseline=json.loads((D/'intake-baseline.json').read_text())
for name,h in baseline['protected'].items():assert sha((P/name).read_bytes())==h
guard=json.loads((D/'review-prospective-isolation.json').read_text());checks=[]
for i,x in enumerate(old['tasks']):
    if i==own_index or x.get('status') not in {'running','queued','waiting'} or 'brief' not in x:continue
    raw=(P/x['brief']).read_bytes();patterns=[g for g in re.findall(r'\*[^\s,;()]*\*',raw.decode()) if g not in {'*','**'}]
    matches={n:[g for g in patterns if fnmatch.fnmatchcase(n.casefold(),g.casefold())] for n in guard['namespaces']}
    assert all(matches.values()),(i,matches)
    checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(raw),matches=matches))
prep=json.loads((D/'review-preparation.json').read_text());assert prep['independent_fresh_rounds'] and prep['prior_review_findings'] is None
now=datetime.now(timezone.utc).isoformat()
own=new['tasks'][own_index];own.update(terminal)
own.update(observed_utc=now,disposition='FULL_AUTHOR_PROOF_NOMINEE_REVIEWS_PENDING',parent_intake='discovery-arithmetic-r162aj-parent/intake.json',parent_assessment='discovery-arithmetic-r162aj-parent/assessment.md',artifact_verification='discovery-arithmetic-r162aj-parent/verification.json',frozen_statement=True,statement='fresh-arithmetic-discovery-r162aj/packet/STATEMENT.md',statement_sha256=prep['statement_sha256'],author_proof='fresh-arithmetic-discovery-r162aj/packet/AUTHOR-PROOF.md',author_proof_sha256=prep['author_proof_sha256'],correctness_gate=None,contribution_gate=None,accepted=False,count_change=0,full_scope_preserved=True,declared_author_gap=None,independent_review_obligations='Full correctness and full conditional substantial-contribution assessments outstanding;no mathematical gates adopted.',status_provenance='Own terminal task_status intake only;no polling,watcher or foreign live query.')
registrations=[];snap=new['current_work_snapshot'];changed_snap={'observed_utc','note','arithmetic_r162aj_nominee'}
for item in prep['reviews']:
    assert not any(x.get('clientRequestId')==item['clientRequestId'] for x in old['tasks'])
    raw=(P/item['brief']).read_bytes();assert len(raw)==item['bytes'] and sha(raw)==item['sha256']
    role=item['role'];dispatch=json.loads((D/f'{role}-dispatch.json').read_text())['structuredContent']
    assert dispatch['status'] in {'running','queued'} and dispatch['providerInstanceId']=='codex' and dispatch['model']=='gpt-6-astra'
    assert {x['id']:x['value'] for x in dispatch['options']}==dict(reasoningEffort='high',serviceTier='default')
    assert not dispatch['hasPendingQuestion'] and dispatch['pendingApproval'] is None
    assert dispatch['childThreadId']!=terminal['childThreadId']
    record=copy.deepcopy(dispatch)
    kind='correctness' if role=='proof' else 'substantial_contribution'
    record.update(observed_utc=now,role='review',review_kind=kind,round=1,target=dict(providerInstanceId='codex',model='gpt-6-astra',options=dict(reasoningEffort='high',serviceTier='default')),title=item['title'],clientRequestId=item['clientRequestId'],parent_thread='6742db91-d35c-44d0-a762-e5d9232f5177',output=item['root']+'/',brief=item['brief'],brief_sha256=item['sha256'],brief_bytes=item['bytes'],source_index=104,nominee_taskId=terminal['taskId'],statement_sha256=prep['statement_sha256'],author_proof_sha256=prep['author_proof_sha256'],entire_unchanged_frozen_scope=True,full_original_discovery_brief_embedded=True,full_statement_and_proof_embedded=True,completed_readonly_inputs=79,all_previous_literal_guards_retained=True,independent_fresh_conversation=True,other_review_uninspected=True,contribution_conditioned_on_entire_correctness=role=='contribution',prior_review_findings=None,dispatch_receipt=f'discovery-arithmetic-r162aj-parent/{role}-dispatch.json',prospective_isolation='discovery-arithmetic-r162aj-parent/review-prospective-isolation.json',accepted=False,count_change=0,parent_count_at_dispatch=19,publication='STOPPED',status_provenance='Actual fresh async delegate_task review;explicit Astra/high/default receipt verified. No thread-send continuation,polling or watcher.')
    index=len(new['tasks']);new['tasks'].append(record)
    registrations.append(dict(role=role,task_index=index,taskId=dispatch['taskId'],childThreadId=dispatch['childThreadId'],status_at_dispatch=dispatch['status'],model_options_verified=True))
    key=f'arithmetic_r162aj_{role}_r1';changed_snap.add(key)
    snap[key]=dict(task_index=index,taskId=dispatch['taskId'],status=dispatch['status'],brief=item['brief'],full_unchanged_frozen_scope=True,independent=True,publication='STOPPED',count_change=0)
assert len({x['childThreadId'] for x in registrations})==2
own['independent_review_tasks']={x['role']:x['taskId'] for x in registrations}
note='Arithmetic162aj full author-proof nominee received for deterministic quasipolynomial BIT computation of almost-sure stochastic non-strict liminf mean-payoff/parity winning sets,including zero endpoints,arbitrary behavioral opponents and unrestricted binary numerical data. Decision-only scope,not finite-memory/strategy-output complexity. Statement and proof immutable. Separate fresh full correctness and conditional full substantial-contribution reviews are running on Astra/high/default,with79 exact readonly author inputs each and no cross-review access. No mathematical gate,acceptance or count assigned. Campaign19/20,latestR041;publication STOPPED.'
new['last_parent_progress']=note;snap.update(observed_utc=now,note=note)
snap['arithmetic_r162aj_nominee']=dict(task_index=own_index,intake='discovery-arithmetic-r162aj-parent/intake.json',status='AUTHOR_PROOF_REVIEWS_PENDING',statement=own['statement'],statement_sha256=prep['statement_sha256'],author_proof=own['author_proof'],author_proof_sha256=prep['author_proof_sha256'],correctness_gate=None,contribution_gate=None,accepted=False,count_change=0)
changed=[i for i,(a,b) in enumerate(zip(old['tasks'],new['tasks'])) if a!=b];assert changed==[own_index]
assert all(new[k]==old[k] for k in old if k not in {'tasks','last_parent_progress','current_work_snapshot'})
assert all(snap[k]==v for k,v in old['current_work_snapshot'].items() if k not in changed_snap)
addition=('\n\n### Arithmetic162aj full author-proof nominee and independent reviews — '+now+'\n\n'+note+'\n\nParent assessment: [discovery-arithmetic-r162aj-parent/assessment.md](campaigns/2026-10-14/discovery-arithmetic-r162aj-parent/assessment.md). Frozen statement SHA256 '+prep['statement_sha256']+';author proof SHA256 '+prep['author_proof_sha256']+'. Read-only artifact checks matched81 packet files,7158871 bytes,91 unchanged root-file identities/modes,52 complete-tree Git bindings and5 unchanged admitted originals. These and450 small examples are not mathematical gates. Canonical text reading is complete;actual primary/transitive/history and parent display-recovery limits are recorded. Each review receives the complete original discovery brief plus the entire unchanged statement/proof,all retained isolation guards and79 narrow readonly inputs in a fresh conversation. No other review is admitted. Parent integrates results later;no downstream work,polling,watcher,public action or count change.\n').encode()
next_t=(json.dumps(new,ensure_ascii=False,indent=2)+'\n').encode();next_j=raw_j+addition
dump(D/'review-registration.json',dict(reviews=registrations,separate_fresh_conversations=True,original_author_task_preserved=True,correctness_gate=None,contribution_gate=None,count_change=0,campaign_count=19,publication='STOPPED'))
dump(D/'coordination-rebase.json',dict(intake_head=baseline['head'],integration_head=head,head_advanced=head!=baseline['head'],before_task_count=len(old['tasks']),after_task_count=len(new['tasks']),changed_old_task_indices=changed,new_task_indices=[x['task_index'] for x in registrations],all_other_tasks_preserved=True,all_other_top_fields_preserved=True,journal_prefix_preserved=True,protected_modifications_preserved=True,tasks_before_sha256=sha(raw_t),tasks_after_sha256=sha(next_t),journal_before_sha256=sha(raw_j),journal_after_sha256=sha(next_j),integration_original_brief_guard_checks=checks,no_foreign_live_queries=True))
(D/'private/intake/our-tasks-after.json').write_bytes(next_t);(D/'private/intake/our-journal-after.md').write_bytes(next_j)
before=json.loads((D/'private/intake/root-before.json').read_text());root=B/'fresh-arithmetic-discovery-r162aj';actual={}
for p in root.rglob('*'):
    assert not p.is_symlink()
    if p.is_file():
        raw=p.read_bytes();actual[p.relative_to(root).as_posix()]=dict(bytes=len(raw),mode=p.stat().st_mode,sha256=sha(raw))
assert actual==before
for x in json.loads((D/'private/review-inputs.json').read_text()):
    p=P/x['path'];raw=p.read_bytes();assert len(raw)==x['bytes'] and sha(raw)==x['sha256'] and p.stat().st_mode==x['mode']
assert git('rev-parse','HEAD').decode().strip()==head
assert (P/TP).read_bytes()==raw_t and (P/JP).read_bytes()==raw_j
(P/TP).write_bytes(next_t);(P/JP).write_bytes(next_j)
names=['assessment.md','verification.json','verify-intake.py','task-status.json','intake-baseline.json','intake-prospective-isolation.json','intake.json','prepare-reviews.py','review-prospective-isolation.json','review-preparation.json','review-capabilities.json','proof-dispatch.json','contribution-dispatch.json','review-registration.json','coordination-rebase.json','manage-reviews.py']
paths=[(D/x).relative_to(P).as_posix() for x in names]+[x['brief'] for x in prep['reviews']]+[TP,JP]
assert len(paths)==len(set(paths))==20
subprocess.run(['git','add','--',*paths],cwd=P,check=True)
assert {x for x in git('diff','--cached','--name-only','-z').decode().split('\0') if x}=={'openai-proof-research/'+x for x in paths}
for name in paths:assert git('show',':openai-proof-research/'+name)==(P/name).read_bytes()
subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
assert git('rev-parse','HEAD').decode().strip()==head
subprocess.run(['git','commit','-m','Register stochastic mean-payoff parity nominee and independent reviews'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip()
assert git('show','HEAD:openai-proof-research/'+TP)==next_t and git('show','HEAD:openai-proof-research/'+JP)==next_j
for name,h in baseline['protected'].items():assert sha((P/name).read_bytes())==h
print(json.dumps(dict(commit=git('rev-parse','HEAD').decode().strip(),nominee_task_index=own_index,review_task_indices=[x['task_index'] for x in registrations],changed_old_tasks=changed,staged_allowed_paths=20,campaign_count=19,index_empty=True,protected_modifications_preserved=True)))
