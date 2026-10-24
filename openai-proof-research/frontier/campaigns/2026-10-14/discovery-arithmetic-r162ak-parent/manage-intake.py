#!/usr/bin/env python3
"""Archive full R unchanged and register distinct matrix-multiplication discovery."""
from pathlib import Path
from datetime import datetime,timezone
import copy,fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[4]
B=P/'frontier/campaigns/2026-10-14';D=Path(__file__).resolve().parent
N=B/'discovery-arithmetic-r162al-parent'
TP='frontier/campaigns/2026-10-14/tasks.json';JP='frontier/NEW-TEN-2026-10-14.md'
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
def sha(raw):return hashlib.sha256(raw).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def snapshot(root):
    out={}
    for f in root.rglob('*'):
        assert not f.is_symlink()
        if f.is_file():
            raw=f.read_bytes();out[f.relative_to(root).as_posix()]=dict(bytes=len(raw),sha256=sha(raw),mode=f.stat().st_mode)
    return out
assert not git('diff','--cached','--name-only').strip()
head=git('rev-parse','HEAD').decode().strip()
raw_t=git('show',head+':openai-proof-research/'+TP);raw_j=git('show',head+':openai-proof-research/'+JP)
assert (P/TP).read_bytes()==raw_t and (P/JP).read_bytes()==raw_j,'Concurrent coordination;no overwrite.'
old=json.loads(raw_t);new=copy.deepcopy(old)
assert old['newAccepted']==19 and old['target']==20 and old['latestAcceptance']=='R041'
own=next(i for i,x in enumerate(old['tasks']) if x.get('clientRequestId')=='twenty-20261023-fresh-arithmetic-r162ak-codex-astra-r1');assert own==735
assert old['tasks'][own]['status']=='running'
assert not any(x.get('clientRequestId')=='twenty-20261023-fresh-arithmetic-r162al-codex-astra-r1' for x in old['tasks'])
baseline=json.loads((D/'intake-baseline.json').read_text())
for n,h in baseline['protected'].items():assert sha((P/n).read_bytes())==h
checks=[];guard=json.loads((N/'prospective-isolation.json').read_text())
for i,x in enumerate(old['tasks']):
    if i==own or x.get('status') not in {'running','queued','waiting'} or not x.get('brief'):continue
    raw=(P/x['brief']).read_bytes();patterns=[z for z in re.findall(r'\*[^\s,;()]*\*',raw.decode()) if z not in {'*','**'}]
    matches={n:[z for z in patterns if fnmatch.fnmatchcase(n.casefold(),z.casefold())] for n in guard['namespaces']}
    assert all(matches.values());checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(raw),matches=matches))
terminal=json.loads((D/'task-status.json').read_text())['structuredContent']
dispatch=json.loads((N/'dispatch.json').read_text())['structuredContent']
assert terminal['taskId']==old['tasks'][own]['taskId'] and terminal['status']=='completed' and terminal['workState']=='result_available'
assert not terminal['hasPendingChildRuns'] and not terminal['hasPendingQuestion'] and terminal['pendingApproval'] is None
assert dispatch['status'] in {'queued','running'} and dispatch['providerInstanceId']=='codex' and dispatch['model']=='gpt-6-astra'
assert {x['id']:x['value'] for x in dispatch['options']}==dict(reasoningEffort='high',serviceTier='default')
assert not dispatch['hasPendingQuestion'] and dispatch['pendingApproval'] is None
prep=json.loads((N/'brief-preparation.json').read_text());brief=(P/prep['brief']).read_bytes()
assert len(brief)==prep['bytes'] and sha(brief)==prep['sha256'] and prep['all_extra_guard_literals_verified'] and prep['all_previous_literal_guards_retained']
v=json.loads((D/'verification.json').read_text());intake=json.loads((D/'intake.json').read_text())
assert v['status']=='MATCH' and intake['disposition']=='PREFREEZE_NO_NOMINEE'
now=datetime.now(timezone.utc).isoformat()
record=new['tasks'][own];record.update(terminal)
record.update(observed_utc=now,disposition='PREFREEZE_NO_NOMINEE',
    parent_intake='discovery-arithmetic-r162ak-parent/intake.json',
    parent_assessment='discovery-arithmetic-r162ak-parent/assessment.md',
    artifact_verification='discovery-arithmetic-r162ak-parent/verification.json',
    full_scope_preserved=True,frozen_statement=False,author_proof_nominee=False,
    correctness_gate=None,contribution_gate=None,accepted=False,count_change=0,
    scope_record='fresh-arithmetic-discovery-r162ak/private/PREFREEZE-SCOPE.md',
    scope_record_sha256=intake['scope_record_sha256'],
    full_target_remains_unproved=True,neither_target_nor_negation_proved=True,
    unpaid_obligation=intake['unpaid_obligation'],canonical_operative_reading_complete=True,
    explicit_companion_reading_complete=True,transitive_primary_reading_complete=False,
    optional_original_history_traversals=0,
    status_provenance='Own completed task_status intake once;no foreign live query,polling or watcher.')
fresh=copy.deepcopy(dispatch)
fresh.update(observed_utc=now,role='research',round=1,
    target=dict(providerInstanceId='codex',model='gpt-6-astra',options=dict(reasoningEffort='high',serviceTier='default')),
    title='Arithmetic162al: confirmed matrix-multiplication discovery',
    clientRequestId='twenty-20261023-fresh-arithmetic-r162al-codex-astra-r1',
    parent_thread='6742db91-d35c-44d0-a762-e5d9232f5177',
    output='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162al/',
    brief=prep['brief'],brief_sha256=prep['sha256'],brief_bytes=prep['bytes'],
    submitted_prompt_contains_full_brief=True,source_index=107,
    source_family_navigation='Source107 exact catalogue[178483,180526),three confirmed folders,82 blobs/104 entries. Actual wrappers build/paper.tex43060,build/main.tex3238 and build/main.tex1977. Source106 already paid independent-set companion skipped. Initial locator printed170-byte106 prefix;corrected extraction recovered same bounded window. Disclosure in brief;no additional screens.',
    round_namespace='Distinct matrix-multiplication family. Full stipulated square/rectangular and stronger operative constructions paid;arithmetic/bit,field/characteristic,exact/border,uniformity and all costs must be tracked. Full R,HP,entropy C and every older target/disposition preserved. R162AJ remains PASS/TECHNICAL,condition discharged,zero count.',
    all_previous_literal_guards_and5570_standing_bytes_retained=True,
    all_new_literal_guard_twins_verified_before_dispatch=True,
    dispatch_receipt='discovery-arithmetic-r162al-parent/dispatch.json',
    prospective_isolation='discovery-arithmetic-r162al-parent/prospective-isolation.json',
    distinct_family=True,new_author_conversation=True,independent_review=False,
    accepted=False,count_change=0,parent_count_at_dispatch=19,publication='STOPPED',
    status_provenance='Actual fresh async delegate_task;explicit Astra/high/default receipt checked,no polling/watcher or foreign live query.')
new_index=len(new['tasks']);new['tasks'].append(fresh)
note=('Arithmetic162ak archived PREFREEZE/no nominee. Full perfect-completeness per-left uniform-all-pairings richification R remains unproved,neither R nor its negation established. '
    'Paid comparisons and specific-construction capacity/coarsening/square calculations preserved;one full sound construction/own-question decoder on the SAME complete matching law remains unpaid. '
    'No theorem freeze,mathematical gates or count. Arithmetic162al fresh distinct Source107 matrix-multiplication discovery running on Astra/high/default;all stronger source operations paid. '
    'Navigation170-byte Source106 prefix exposure disclosed;source106 already-paid companion skipped. R162AJ PASS/TECHNICAL condition discharged and all older full scopes unchanged. Campaign19/20,latestR041;publication STOPPED.')
new['last_parent_progress']=note;snap=new['current_work_snapshot'];snap.update(observed_utc=now,note=note)
snap['arithmetic_r162ak_archive']=dict(task_index=own,intake='discovery-arithmetic-r162ak-parent/intake.json',
    disposition='PREFREEZE_NO_NOMINEE',full_scope_preserved=True,full_R_unproved=True,
    correctness_gate=None,contribution_gate=None,accepted=False,count_change=0)
snap['arithmetic_r162al_dispatch']=dict(task_index=new_index,taskId=dispatch['taskId'],status=dispatch['status'],
    brief=prep['brief'],source=107,catalogue_extent=[178483,180526],distinct_family=True,
    original_brief_guards_checked_before_creation=True,both_new_literal_twins_verified=True,
    navigation_prefix_overread_disclosed=True,private_local_inputs_and_metadata_retained=True,
    foreign_live_queries=False,publication='STOPPED',count_change=0)
changed=[i for i,(a,b) in enumerate(zip(old['tasks'],new['tasks'])) if a!=b];assert changed==[own]
assert all(new[k]==old[k] for k in old if k not in {'tasks','last_parent_progress','current_work_snapshot'})
allowed={'observed_utc','note','arithmetic_r162ak_archive','arithmetic_r162al_dispatch'}
assert all(snap[k]==x for k,x in old['current_work_snapshot'].items() if k not in allowed)
addition=('\n\n### Arithmetic162ak archive and distinct matrix-multiplication dispatch — '+now+'\n\n'+note+
    '\n\nParent [assessment](campaigns/2026-10-14/discovery-arithmetic-r162ak-parent/assessment.md) preserves EVERY fixed-delta,exact-completeness,per-left uniform-all-matchings,local-information and explicit finite-bit quantifier. '
    'The parent read the full scope,notebook,reading limits and handoffs;it did not independently reread source/primary proofs. Exact verification matched41 payloads,7693691 bytes,45 unchanged root files/full modes,11 pinned canonical text objects,1 companion PDF and5 unchanged completed inputs. These are artifact checks only. '
    'The new full brief retains all older literal guards and5570 standing bytes,with5 exact completed originals as scope/payment context only. No exception propagates a containing namespace. No new child title hunt or additional family screen. '
    'All three Source107 wrappers were selected from the complete pinned tree;parent source-body reading NONE. Runtime receipt checks Codex/GPT-6 Astra/high/default. No foreign live query,polling,watcher,public action or downstream work.\n').encode()
next_t=(json.dumps(new,ensure_ascii=False,indent=2)+'\n').encode();next_j=raw_j+addition
dump(D/'coordination-rebase.json',dict(intake_head=baseline['head'],integration_head=head,head_advanced=head!=baseline['head'],
    before_task_count=len(old['tasks']),after_task_count=len(new['tasks']),changed_old_task_indices=changed,new_task_index=new_index,
    all_other_tasks_preserved=True,all_other_top_fields_preserved=True,journal_prefix_preserved=True,
    protected_modifications_preserved=True,tasks_before_sha256=sha(raw_t),tasks_after_sha256=sha(next_t),
    journal_before_sha256=sha(raw_j),journal_after_sha256=sha(next_j),integration_original_brief_guard_checks=checks,no_foreign_live_queries=True))
dump(N/'registration.json',dict(task_index=new_index,taskId=dispatch['taskId'],status_at_dispatch=dispatch['status'],
    distinct_family=True,model_options_verified=True,count_change=0,publication='STOPPED'))
(D/'private/intake/our-tasks-after.json').write_bytes(next_t);(D/'private/intake/our-journal-after.md').write_bytes(next_j)
assert snapshot(B/'fresh-arithmetic-discovery-r162ak')==json.loads((D/'private/intake/root-before.json').read_text())
for x in json.loads((N/'private/completed-direct-inputs.json').read_text()):
    f=P/x['path'];raw=f.read_bytes();assert len(raw)==x['bytes'] and sha(raw)==x['sha256'] and f.stat().st_mode==x['mode']
assert git('rev-parse','HEAD').decode().strip()==head and (P/TP).read_bytes()==raw_t and (P/JP).read_bytes()==raw_j
(P/TP).write_bytes(next_t);(P/JP).write_bytes(next_j)
names=['assessment.md','intake.json','verification.json','verify-intake.py','task-status.json','intake-baseline.json',
       'intake-prospective-isolation.json','integration-guard.json','prepare-next.py','manage-intake.py','coordination-rebase.json']
paths=[(D/x).relative_to(P).as_posix() for x in names]+[(N/x).relative_to(P).as_posix() for x in ['brief-preparation.json','capabilities.json','dispatch.json','prospective-isolation.json','registration.json']]+[prep['brief'],TP,JP]
assert len(paths)==len(set(paths))==19
assert git('rev-parse','HEAD').decode().strip()==head and (P/TP).read_bytes()==next_t and (P/JP).read_bytes()==next_j
subprocess.run(['git','add','--',*paths],cwd=P,check=True)
assert {x for x in git('diff','--cached','--name-only','-z').decode().split('\0') if x}=={'openai-proof-research/'+x for x in paths}
for name in paths:assert git('show',':openai-proof-research/'+name)==(P/name).read_bytes()
subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True);assert git('rev-parse','HEAD').decode().strip()==head
subprocess.run(['git','commit','-m','Archive full richification research and start matrix discovery'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip()
assert git('show','HEAD:openai-proof-research/'+TP)==next_t and git('show','HEAD:openai-proof-research/'+JP)==next_j
for name,h in baseline['protected'].items():assert sha((P/name).read_bytes())==h
print(json.dumps(dict(commit=git('rev-parse','HEAD').decode().strip(),changed_old_tasks=changed,new_task_index=new_index,
    all_other_tasks_preserved=True,staged_allowed_paths=19,campaign_count=19,index_empty=True,protected_modifications_preserved=True)))
