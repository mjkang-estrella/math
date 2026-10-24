#!/usr/bin/env python3
"""Integrate conditional contribution only,preserve correctness,and register distinct research."""
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
N=B/'discovery-arithmetic-r162ak-parent'
TP='frontier/campaigns/2026-10-14/tasks.json'
JP='frontier/NEW-TEN-2026-10-14.md'
def git(*args):return subprocess.check_output(['git',*args],cwd=P)
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
assert not git('diff','--cached','--name-only').strip()
head=git('rev-parse','HEAD').decode().strip();raw_t=git('show',head+':openai-proof-research/'+TP);raw_j=git('show',head+':openai-proof-research/'+JP)
assert (P/TP).read_bytes()==raw_t and (P/JP).read_bytes()==raw_j,'Concurrent uncommitted coordination;no overwrite.'
old=json.loads(raw_t);new=copy.deepcopy(old);assert old['newAccepted']==19 and old['target']==20
own_index=next(i for i,x in enumerate(old['tasks']) if x.get('clientRequestId')=='twenty-20261023-arithmetic-r162aj-contribution-codex-astra-r1')
author_index=next(i for i,x in enumerate(old['tasks']) if x.get('clientRequestId')=='twenty-20261023-fresh-arithmetic-r162aj-codex-astra-r1')
assert old['tasks'][own_index]['status']=='running' and old['tasks'][author_index]['correctness_gate'] is None
assert not any(x.get('clientRequestId')=='twenty-20261023-fresh-arithmetic-r162ak-codex-astra-r1' for x in old['tasks'])
baseline=json.loads((D/'contribution-intake-baseline.json').read_text())
for name,h in baseline['protected'].items():assert sha((P/name).read_bytes())==h
guard=json.loads((N/'prospective-isolation.json').read_text());checks=[]
for i,x in enumerate(old['tasks']):
    if i==own_index or x.get('status') not in {'running','queued','waiting'} or 'brief' not in x:continue
    raw=(P/x['brief']).read_bytes();patterns=[g for g in re.findall(r'\*[^\s,;()]*\*',raw.decode()) if g not in {'*','**'}]
    matches={n:[g for g in patterns if fnmatch.fnmatchcase(n.casefold(),g.casefold())] for n in guard['namespaces']}
    assert all(matches.values()),(i,matches)
    checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(raw),matches=matches))
terminal=json.loads((D/'contribution-task-status.json').read_text())['structuredContent'];dispatch=json.loads((N/'dispatch.json').read_text())['structuredContent']
assert terminal['taskId']==old['tasks'][own_index]['taskId'] and terminal['status']=='completed' and terminal['workState']=='result_available'
assert not terminal['hasPendingChildRuns'] and not terminal['hasPendingQuestion'] and terminal['pendingApproval'] is None
assert dispatch['status'] in {'running','queued'} and dispatch['providerInstanceId']=='codex' and dispatch['model']=='gpt-6-astra'
assert {x['id']:x['value'] for x in dispatch['options']}==dict(reasoningEffort='high',serviceTier='default')
assert not dispatch['hasPendingQuestion'] and dispatch['pendingApproval'] is None
prep=json.loads((N/'brief-preparation.json').read_text());brief=(P/prep['brief']).read_bytes()
assert len(brief)==prep['bytes'] and sha(brief)==prep['sha256'] and prep['all_extra_guard_literals_verified'] and prep['distinct_family']
now=datetime.now(timezone.utc).isoformat()
own=new['tasks'][own_index];own.update(terminal)
own.update(observed_utc=now,disposition='FULL_SCOPE_TECHNICAL_CONDITIONAL_ON_CORRECTNESS',review_grade='TECHNICAL',conditional_on_correctness_of_entire_unchanged_statement=True,contribution_condition_discharged=False,essential_comparison_remaining=False,parent_intake='discovery-arithmetic-r162aj-parent/contribution-intake.json',parent_assessment='discovery-arithmetic-r162aj-parent/contribution-assessment.md',artifact_verification='discovery-arithmetic-r162aj-parent/contribution-verification.json',correctness_gate=None,accepted=False,count_change=0,full_scope_preserved=True,other_review_status_or_body_not_queried=True,status_provenance='Own completed contribution task_status intake only;no correctness-task query,polling or watcher.')
author=new['tasks'][author_index]
author.update(observed_utc=now,disposition='CONTRIBUTION_TECHNICAL_CORRECTNESS_PENDING',contribution_gate='TECHNICAL',contribution_conditional_on_correctness_of_entire_statement=True,contribution_condition_discharged=False,parent_contribution_intake='discovery-arithmetic-r162aj-parent/contribution-intake.json',parent_contribution_assessment='discovery-arithmetic-r162aj-parent/contribution-assessment.md',remaining_review_obligations='Independent full correctness result not yet integrated. Full contribution TECHNICAL conditional on entire frozen theorem;no acceptance/count or downstream work.',accepted=False,count_change=0)
assert author['correctness_gate'] is None
record=copy.deepcopy(dispatch)
record.update(observed_utc=now,role='research',round=1,target=dict(providerInstanceId='codex',model='gpt-6-astra',options=dict(reasoningEffort='high',serviceTier='default')),title='Arithmetic162ak: confirmed perfect-completeness 2-to-1 discovery',clientRequestId='twenty-20261023-fresh-arithmetic-r162ak-codex-astra-r1',parent_thread='6742db91-d35c-44d0-a762-e5d9232f5177',output='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ak/',brief=prep['brief'],brief_sha256=prep['sha256'],brief_bytes=prep['bytes'],submitted_prompt_contains_full_brief=True,source_index=105,source_family_navigation='Distinct Source105;only first2 title strings105/106 decoded from one bounded window at176416;only105 body[176416,177336) selected.106 body not read. One folder,13 blobs/16 entries,actual build/main.tex2286 bytes/blob281661b221e6e51e19658cad1b6df225cf7077fd. Parent metadata only.',round_namespace='Distinct perfect-completeness2-to-1 family. Entire stipulated fixed-delta NP-hardness,exact two-preimage constraints,unweighted explicit multiset and stronger operative proof operations are paid. R162AJ full scope and conditionalTECHNICAL disposition preserved,correctness not queried;all previous scopes unchanged.',all_previous_literal_guards_and5570_standing_bytes_retained=True,all_new_literal_guard_twins_verified_before_dispatch=True,dispatch_receipt='discovery-arithmetic-r162ak-parent/dispatch.json',prospective_isolation='discovery-arithmetic-r162ak-parent/prospective-isolation.json',distinct_family=True,new_author_conversation=True,accepted=False,count_change=0,parent_count_at_dispatch=19,publication='STOPPED',status_provenance='Actual fresh async delegate_task;explicit Astra/high/default receipt verified,no polling/watcher or correctness-review interference.')
new_index=len(new['tasks']);new['tasks'].append(record)
note='R162AJ independent full-scope contribution adopted TECHNICAL,conditional on correctness of the ENTIRE unchanged frozen theorem. Full payment covers source gain-bias/MDP endpoint flow,GK attainment/transfer,CDGO monotone boundary equations and HS with all oracle/bit costs. No essential comparison gap reported. Correctness result not queried or integrated;condition remains undischarged,no count or downstream work. Arithmetic162ak is running as distinct Source105 perfect-completeness2-to-1 discovery on Astra/high/default. Frozen game scope,HP,entropy C and all old dispositions unchanged. Campaign19/20,latestR041;publication STOPPED.'
new['last_parent_progress']=note;snap=new['current_work_snapshot'];snap.update(observed_utc=now,note=note)
changed_snap={'observed_utc','note','arithmetic_r162aj_contribution_r1','arithmetic_r162aj_nominee','arithmetic_r162ak_dispatch'}
snap['arithmetic_r162aj_contribution_r1']=dict(task_index=own_index,taskId=terminal['taskId'],status='completed',grade='TECHNICAL',conditional_on_entire_correctness=True,condition_discharged=False,intake='discovery-arithmetic-r162aj-parent/contribution-intake.json',count_change=0)
nom=copy.deepcopy(snap['arithmetic_r162aj_nominee']);nom.update(status='CONTRIBUTION_TECHNICAL_CORRECTNESS_PENDING',contribution_gate='TECHNICAL',contribution_condition_discharged=False,contribution_intake='discovery-arithmetic-r162aj-parent/contribution-intake.json',accepted=False,count_change=0);snap['arithmetic_r162aj_nominee']=nom
snap['arithmetic_r162ak_dispatch']=dict(task_index=new_index,taskId=dispatch['taskId'],status=dispatch['status'],brief=prep['brief'],source=105,catalogue_extent=[176416,177336],distinct_family=True,original_brief_guards_checked_before_creation=True,both_new_literal_twins_verified=True,other_review_status_or_body_not_queried=True,publication='STOPPED',count_change=0)
changed=[i for i,(a,b) in enumerate(zip(old['tasks'],new['tasks'])) if a!=b];assert changed==sorted([own_index,author_index])
assert all(new[k]==old[k] for k in old if k not in {'tasks','last_parent_progress','current_work_snapshot'})
assert all(snap[k]==v for k,v in old['current_work_snapshot'].items() if k not in changed_snap)
addition=('\n\n### R162AJ contribution intake and distinct Arithmetic162ak dispatch — '+now+'\n\n'+note+'\n\nFull assessment: [discovery-arithmetic-r162aj-parent/contribution-assessment.md](campaigns/2026-10-14/discovery-arithmetic-r162aj-parent/contribution-assessment.md). Independent review read completely,including strongest endpoint/attainment and monotone-acceleration payment. Its condition is not discharged,and no correctness verdict is inferred. Artifact checks matched13 selected review files,125257 bytes,17 unchanged review-root identities/modes,45 exact input objects and91 unchanged author files;these are not mathematical gates. Only journal[4801,6347) was read. No correctness status/body was queried or grade communicated to that reviewer. New Source105 full brief retains all older scopes,all literal guards and5570 standing bytes. Five exact completed exceptions do not widen namespaces. Source106 title only,no body selected. Fresh async research dispatch receipt verifies Astra/high/default;no polling,watcher,public action or count change.\n').encode()
next_t=(json.dumps(new,ensure_ascii=False,indent=2)+'\n').encode();next_j=raw_j+addition
dump(D/'contribution-coordination-rebase.json',dict(intake_head=baseline['head'],integration_head=head,head_advanced=head!=baseline['head'],before_task_count=len(old['tasks']),after_task_count=len(new['tasks']),changed_old_task_indices=changed,new_task_index=new_index,all_other_tasks_preserved=True,other_review_entry_preserved=True,all_other_top_fields_preserved=True,journal_prefix_preserved=True,protected_modifications_preserved=True,tasks_before_sha256=sha(raw_t),tasks_after_sha256=sha(next_t),journal_before_sha256=sha(raw_j),journal_after_sha256=sha(next_j),integration_original_brief_guard_checks=checks,no_foreign_live_queries=True))
dump(N/'registration.json',dict(task_index=new_index,taskId=dispatch['taskId'],status_at_dispatch=dispatch['status'],distinct_family=True,model_options_verified=True,count_change=0,publication='STOPPED'))
(D/'private/contribution-intake/our-tasks-after.json').write_bytes(next_t);(D/'private/contribution-intake/our-journal-after.md').write_bytes(next_j)
def snapshot(root):
    result={}
    for p in root.rglob('*'):
        assert not p.is_symlink()
        if p.is_file():
            raw=p.read_bytes();result[p.relative_to(root).as_posix()]=dict(bytes=len(raw),mode=p.stat().st_mode,sha256=sha(raw))
    return result
assert snapshot(B/'arithmetic-r162aj-contribution-r1')==json.loads((D/'private/contribution-intake/root-before.json').read_text())
assert snapshot(B/'fresh-arithmetic-discovery-r162aj')==json.loads((D/'private/intake/root-before.json').read_text())
for x in json.loads((N/'private/completed-direct-inputs.json').read_text()):
    p=P/x['path'];raw=p.read_bytes();assert len(raw)==x['bytes'] and sha(raw)==x['sha256'] and p.stat().st_mode==x['mode']
assert git('rev-parse','HEAD').decode().strip()==head and (P/TP).read_bytes()==raw_t and (P/JP).read_bytes()==raw_j
(P/TP).write_bytes(next_t);(P/JP).write_bytes(next_j)
names=['contribution-assessment.md','contribution-intake.json','contribution-verification.json','verify-contribution-intake.py','contribution-task-status.json','contribution-intake-baseline.json','contribution-intake-prospective-isolation.json','contribution-integration-guard.json','prepare-next.py','manage-contribution.py','contribution-coordination-rebase.json']
paths=[(D/x).relative_to(P).as_posix() for x in names]+[(N/x).relative_to(P).as_posix() for x in ['brief-preparation.json','capabilities.json','dispatch.json','prospective-isolation.json','registration.json']]+[prep['brief'],TP,JP]
assert len(paths)==len(set(paths))==19
subprocess.run(['git','add','--',*paths],cwd=P,check=True)
assert {x for x in git('diff','--cached','--name-only','-z').decode().split('\0') if x}=={'openai-proof-research/'+x for x in paths}
for name in paths:assert git('show',':openai-proof-research/'+name)==(P/name).read_bytes()
subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True);assert git('rev-parse','HEAD').decode().strip()==head
subprocess.run(['git','commit','-m','Record conditional technical review and open 2-to-1 discovery'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip() and git('show','HEAD:openai-proof-research/'+TP)==next_t and git('show','HEAD:openai-proof-research/'+JP)==next_j
for name,h in baseline['protected'].items():assert sha((P/name).read_bytes())==h
print(json.dumps(dict(commit=git('rev-parse','HEAD').decode().strip(),contribution_task_index=own_index,nominee_task_index=author_index,new_task_index=new_index,changed_old_tasks=changed,all_other_tasks_preserved=True,staged_allowed_paths=19,campaign_count=19,index_empty=True,protected_modifications_preserved=True)))
