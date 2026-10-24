#!/usr/bin/env python3
"""Scoped intake and same-conversation research registration; explicit local commit."""
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
N=B/'discovery-arithmetic-r162ai-parent'
TP='frontier/campaigns/2026-10-14/tasks.json'
JP='frontier/NEW-TEN-2026-10-14.md'
def git(*args):
    return subprocess.check_output(['git',*args],cwd=P)
def sha(raw):
    return hashlib.sha256(raw).hexdigest()
def dump(path,value):
    path.write_text(json.dumps(value,ensure_ascii=False,indent=2)+'\n')
assert not git('diff','--cached','--name-only').strip()
head=git('rev-parse','HEAD').decode().strip()
raw_t=git('show',head+':openai-proof-research/'+TP)
raw_j=git('show',head+':openai-proof-research/'+JP)
assert (P/TP).read_bytes()==raw_t and (P/JP).read_bytes()==raw_j,'Concurrent uncommitted coordination; nothing overwritten.'
old=json.loads(raw_t);new=copy.deepcopy(old)
assert old['newAccepted']==19 and old['target']==20
own_index=next(i for i,t in enumerate(old['tasks']) if t.get('clientRequestId')=='twenty-20261023-fresh-arithmetic-r162ah-codex-astra-r1')
assert old['tasks'][own_index]['status']=='running'
assert not any(t.get('clientRequestId')=='twenty-20261023-fresh-arithmetic-r162ai-codex-astra-r1' for t in old['tasks'])
baseline=json.loads((D/'intake-baseline.json').read_text())
for name,anchor in baseline['protected'].items():
    assert sha((P/name).read_bytes())==anchor
guard=json.loads((N/'prospective-isolation.json').read_text());guardchecks=[]
for i,t in enumerate(old['tasks']):
    if i==own_index or t.get('status') not in {'running','queued','waiting'} or 'brief' not in t:
        continue
    raw=(P/t['brief']).read_bytes();patterns=[g for g in re.findall(r'\*[^\s,;()]*\*',raw.decode()) if g not in {'*','**'}]
    matches={name:[g for g in patterns if fnmatch.fnmatchcase(name.casefold(),g.casefold())] for name in guard['namespaces']}
    assert all(matches.values()),(i,matches)
    guardchecks.append(dict(task_index=i,original_brief=t['brief'],sha256=sha(raw),matches=matches))
terminal=json.loads((D/'task-status.json').read_text())['structuredContent']
dispatch=json.loads((N/'dispatch.json').read_text())['structuredContent']
assert terminal['taskId']==old['tasks'][own_index]['taskId'] and terminal['status']=='completed' and terminal['workState']=='result_available'
assert not terminal['hasPendingChildRuns'] and not terminal['hasPendingQuestion'] and terminal['pendingApproval'] is None
assert dispatch['status'] in {'running','queued'} and dispatch['providerInstanceId']=='codex' and dispatch['model']=='gpt-6-astra'
assert {x['id']:x['value'] for x in dispatch['options']}==dict(reasoningEffort='high',serviceTier='default')
assert not dispatch['hasPendingQuestion'] and dispatch['pendingApproval'] is None
now=datetime.now(timezone.utc).isoformat()
gap='Full universal entropy-overlap C remains unproved. Random-allocation route lacks a uniform joint interior overlap gain after off-diagonal information costs; source route lacks control of the actual source-field correction and final dimension-uniform original-overlap coercivity from one entropy remainder. Neither C nor its negation proved.'
own=new['tasks'][own_index];own.update(terminal)
own.update(observed_utc=now,disposition='ARCHIVED_PREFREEZE_NO_NOMINEE',parent_intake='discovery-arithmetic-r162ah-parent/intake.json',parent_assessment='discovery-arithmetic-r162ah-parent/assessment.md',artifact_verification='discovery-arithmetic-r162ah-parent/verification.json',frozen_statement=False,correctness_gate=None,contribution_gate=None,accepted=False,count_change=0,full_scope_preserved=True,mathematical_gap=gap,status_provenance='Own terminal task_status intake before follow-up; completed original result preserved. No watcher,polling or foreign live query.')
prep=json.loads((N/'brief-preparation.json').read_text());brief=(P/prep['brief']).read_bytes()
assert len(brief)==prep['bytes'] and sha(brief)==prep['sha256'] and prep['all_extra_guard_literals_verified'] and prep['distinct_family']
record=copy.deepcopy(dispatch)
record.update(observed_utc=now,role='research',round=1,target=dict(providerInstanceId='codex',model='gpt-6-astra',options=dict(reasoningEffort='high',serviceTier='default')),title='Arithmetic162ai: confirmed log-space derandomization discovery',clientRequestId='twenty-20261023-fresh-arithmetic-r162ai-codex-astra-r1',parent_thread='6742db91-d35c-44d0-a762-e5d9232f5177',output='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ai/',brief=prep['brief'],brief_sha256=prep['sha256'],brief_bytes=prep['bytes'],submitted_prompt_contains_full_brief=True,source_index=103,source_family_navigation='Distinct Source103; exact catalogue[172167,173031),one confirmed folder,20 blobs/24 complete-tree entries. ACTUAL build/main.tex808 bytes/blobcd8c7672e9ecd868652f0103481e0770a58ee7c3. Initial regex failure and three headline-description overreads disclosed;102/104 operative bodies not read. Parent metadata only.',round_namespace='Distinct logarithmic-space derandomization family. Entire stipulated L=RL=BPL and effective polynomial-time deterministic log-space compiler,plus all stronger operative source operations,are paid. Exact entropy-overlap C and every older scope/disposition remain archived unchanged. Five exact readonly completed originals only.',all_previous_literal_guards_and5570_standing_bytes_retained=True,all_new_literal_guard_twins_verified_before_dispatch=True,dispatch_receipt='discovery-arithmetic-r162ai-parent/dispatch.json',prospective_isolation='discovery-arithmetic-r162ai-parent/prospective-isolation.json',distinct_family=True,new_author_conversation=True,independent_review=False,accepted=False,count_change=0,parent_count_at_dispatch=19,publication='STOPPED',status_provenance='Actual async delegate_task dispatch; explicit Astra/high/default options verified from receipt. No status polling,watcher or supplemental turn.')
new_index=len(new['tasks']);new['tasks'].append(record)
note='Arithmetic162ah archived PREFREEZE/no nominee: full entropy-overlap C remains unchanged and unproved; no admissible counterexample emerged. Joint allocation,posterior curvature,global lift and source-field correction calculations are preserved with their unpaid uniform coercivity obligations. Arithmetic162ai is running as a distinct confirmed Source103 logarithmic-space derandomization discovery in a fresh author conversation. Effective compiler and class-collapse results are stipulated paid. Actual Astra/high/default verified. Navigation limits disclosed;old scopes unchanged,no count change or public action. Campaign19/20,latestR041;publication STOPPED.'
new['last_parent_progress']=note
snap=new['current_work_snapshot'];snap.update(observed_utc=now,note=note)
archive_key='arithmetic_r162ah_archive';dispatch_key='arithmetic_r162ai_dispatch'
snap[archive_key]=dict(task_index=own_index,status='PREFREEZE_NO_NOMINEE',intake='discovery-arithmetic-r162ah-parent/intake.json',full_diagnostic='ONE universal c: h(X+Y)-n-logdet(CovX+CovY)/2>=c tr(M(I-M)) for EVERY dimension and independent log-concave pair,including singular summands,with positive total covariance.',unpaid_operation=gap,correctness_gate=None,contribution_gate=None,accepted=False,count_change=0)
snap[dispatch_key]=dict(task_index=new_index,taskId=dispatch['taskId'],status=dispatch['status'],brief=prep['brief'],source=103,catalogue_extent=[172167,173031],distinct_family=True,new_author_conversation=True,new_root=True,no_extra_catalogue_screens=True,at_most_one_pruned_original_history_traversal=True,original_brief_guards_checked_before_creation=True,both_new_literal_twins_verified=True,private_local_inputs_and_metadata_retained=True,foreign_live_queries=False,publication='STOPPED')
changed=[i for i,(a,b) in enumerate(zip(old['tasks'],new['tasks'])) if a!=b]
assert changed==[own_index]
assert all(new[k]==old[k] for k in old if k not in {'tasks','last_parent_progress','current_work_snapshot'})
assert all(snap[k]==v for k,v in old['current_work_snapshot'].items() if k not in {'observed_utc','note',archive_key,dispatch_key})
addition=('\n\n### Arithmetic162ah intake and distinct Arithmetic162ai dispatch — '+now+'\n\n'+note+'\n\nParent assessment: [discovery-arithmetic-r162ah-parent/assessment.md](campaigns/2026-10-14/discovery-arithmetic-r162ah-parent/assessment.md). Read-only artifact checks matched8 selected files,the unchanged11-file current root,43 admitted originals and both prior54/12-file roots;these are not mathematical gates. Full C retains all original quantifiers and neither it nor its negation is proved. New brief requires complete Source103 operative source reading from actual build/main.tex808-byte wrapper and strongest primary/companion comparison,retains every old scope,all literal guards and5570 standing bytes. Catalogue navigation recovery displayed three complete headline-description lines;only103 exact body was selected,and102/104 operative bodies were not read. This limit is disclosed. Five narrow completed inputs do not propagate any previous exception. New async delegate_task receipt verifies explicit Astra/high/default;no polling,watcher,public action or count change.\n').encode()
next_t=(json.dumps(new,ensure_ascii=False,indent=2)+'\n').encode();next_j=raw_j+addition
dump(D/'coordination-rebase.json',dict(intake_head=baseline['head'],integration_head=head,head_advanced=head!=baseline['head'],before_task_count=len(old['tasks']),after_task_count=len(new['tasks']),changed_old_task_indices=changed,new_task_index=new_index,all_other_tasks_preserved=True,all_other_top_fields_preserved=True,journal_prefix_preserved=True,protected_modifications_preserved=True,tasks_before_sha256=sha(raw_t),tasks_after_sha256=sha(next_t),journal_before_sha256=sha(raw_j),journal_after_sha256=sha(next_j),integration_original_brief_guard_checks=guardchecks,no_foreign_live_queries=True))
dump(N/'registration.json',dict(task_index=new_index,taskId=dispatch['taskId'],status_at_dispatch=dispatch['status'],distinct_family=True,provider_model_options_verified=True,count_change=0,publication='STOPPED'))
(D/'private/intake/our-tasks-after.json').write_bytes(next_t);(D/'private/intake/our-journal-after.md').write_bytes(next_j)
before=json.loads((D/'private/intake/root-before.json').read_text());root=B/'fresh-arithmetic-discovery-r162ah';actual={}
for p in root.rglob('*'):
    assert not p.is_symlink()
    if p.is_file():
        raw=p.read_bytes();actual[p.relative_to(root).as_posix()]=dict(bytes=len(raw),mode=p.stat().st_mode,sha256=sha(raw))
assert actual==before
for x in json.loads((N/'private/completed-direct-inputs.json').read_text()):
    p=P/x['path'];raw=p.read_bytes();assert len(raw)==x['bytes'] and sha(raw)==x['sha256'] and p.stat().st_mode==x['mode']
assert git('rev-parse','HEAD').decode().strip()==head
assert (P/TP).read_bytes()==raw_t and (P/JP).read_bytes()==raw_j
(P/TP).write_bytes(next_t);(P/JP).write_bytes(next_j)
paths=[(D/x).relative_to(P).as_posix() for x in ['assessment.md','intake.json','verification.json','verify-intake.py','manage.py','intake-baseline.json','intake-prospective-isolation.json','task-status.json','coordination-rebase.json','integration-guard.json','prepare-next.py']]
paths += [(N/x).relative_to(P).as_posix() for x in ['brief-preparation.json','capabilities.json','dispatch.json','prospective-isolation.json','registration.json']]
paths += [prep['brief'],TP,JP]
assert len(paths)==len(set(paths))==19
subprocess.run(['git','add','--',*paths],cwd=P,check=True)
assert {x for x in git('diff','--cached','--name-only','-z').decode().split('\0') if x}=={'openai-proof-research/'+x for x in paths}
for name in paths:
    assert git('show',':openai-proof-research/'+name)==(P/name).read_bytes()
subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
assert git('rev-parse','HEAD').decode().strip()==head
subprocess.run(['git','commit','-m','Archive entropy-overlap r162ah and open log-space discovery r162ai'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip()
assert git('show','HEAD:openai-proof-research/'+TP)==next_t and git('show','HEAD:openai-proof-research/'+JP)==next_j
for name,anchor in baseline['protected'].items():
    assert sha((P/name).read_bytes())==anchor
print(json.dumps(dict(commit=git('rev-parse','HEAD').decode().strip(),archived_task_index=own_index,new_task_index=new_index,changed_old_tasks=changed,staged_allowed_paths=19,campaign_count=19,index_empty=True,protected_modifications_preserved=True)))
