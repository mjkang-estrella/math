#!/usr/bin/env python3
"""One-time scoped adoption of full correctness and closure of R162AJ."""
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
TP='frontier/campaigns/2026-10-14/tasks.json'
JP='frontier/NEW-TEN-2026-10-14.md'

def git(*args):
    return subprocess.check_output(['git',*args],cwd=P)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def dump(path,value):
    path.write_text(json.dumps(value,ensure_ascii=False,indent=2)+'\n')

def snapshot(root):
    out={}
    for f in root.rglob('*'):
        assert not f.is_symlink()
        if f.is_file():
            raw=f.read_bytes()
            out[f.relative_to(root).as_posix()]=dict(bytes=len(raw),sha256=sha(raw),mode=f.stat().st_mode)
    return out

assert not git('diff','--cached','--name-only').strip()
head=git('rev-parse','HEAD').decode().strip()
raw_t=git('show',head+':openai-proof-research/'+TP)
raw_j=git('show',head+':openai-proof-research/'+JP)
assert (P/TP).read_bytes()==raw_t and (P/JP).read_bytes()==raw_j, 'Concurrent coordination; no overwrite.'
old=json.loads(raw_t); new=copy.deepcopy(old)
assert old['newAccepted']==19 and old['target']==20 and old['latestAcceptance']=='R041'
indices={}
for key,request in {
    'author':'twenty-20261023-fresh-arithmetic-r162aj-codex-astra-r1',
    'proof':'twenty-20261023-arithmetic-r162aj-proof-codex-astra-r1',
    'contribution':'twenty-20261023-arithmetic-r162aj-contribution-codex-astra-r1',
}.items():
    indices[key]=next(i for i,x in enumerate(old['tasks']) if x.get('clientRequestId')==request)
assert indices==dict(author=728,proof=732,contribution=733)
baseline=json.loads((D/'proof-intake-baseline.json').read_text())
for i in indices.values():
    assert old['tasks'][i]==json.loads((D/f'private/proof-intake/task-{i}.before.json').read_text())
assert old['tasks'][732]['status']=='running'
assert old['tasks'][728]['correctness_gate'] is None
assert old['tasks'][733]['review_grade']=='TECHNICAL'
assert old['tasks'][733]['contribution_condition_discharged'] is False
for name,expected in baseline['protected'].items():
    assert sha((P/name).read_bytes())==expected

checks=[]
namespace=D.relative_to(P).as_posix()
for i,x in enumerate(old['tasks']):
    if i==732 or x.get('status') not in {'running','queued','waiting'} or not x.get('brief'):
        continue
    raw=(P/x['brief']).read_bytes()
    patterns=[z for z in re.findall(r'\*[^\s,;()]*\*',raw.decode()) if z not in {'*','**'}]
    matches=[z for z in patterns if fnmatch.fnmatchcase(namespace.casefold(),z.casefold())]
    assert matches
    checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(raw),matches=matches))

terminal=json.loads((D/'proof-task-status.json').read_text())['structuredContent']
assert terminal['taskId']==old['tasks'][732]['taskId']
assert terminal['status']=='completed' and terminal['workState']=='result_available'
assert not terminal['hasPendingChildRuns'] and not terminal['hasPendingQuestion'] and terminal['pendingApproval'] is None
assert terminal['providerInstanceId']=='codex' and terminal['model']=='gpt-6-astra'
assert {x['id']:x['value'] for x in terminal['options']}==dict(reasoningEffort='high',serviceTier='default')
intake=json.loads((D/'proof-intake.json').read_text())
verified=json.loads((D/'proof-verification.json').read_text())
assert intake['correctness_gate']=='PASS' and intake['contribution_gate']=='TECHNICAL'
assert intake['contribution_condition_discharged'] and verified['status']=='MATCH'
now=datetime.now(timezone.utc).isoformat()
proof=new['tasks'][732]
proof.update(terminal)
proof.update(observed_utc=now,disposition='FULL_SCOPE_PASS_ADOPTED',review_grade='PASS',
    correctness_gate='PASS',full_scope_preserved=True,necessary_author_repairs=[],
    essential_correctness_obligations=[],relative_to_stipulated_upstream_truth=True,
    parent_intake='discovery-arithmetic-r162aj-parent/proof-intake.json',
    parent_assessment='discovery-arithmetic-r162aj-parent/proof-assessment.md',
    artifact_verification='discovery-arithmetic-r162aj-parent/proof-verification.json',
    accepted=False,count_change=0,
    status_provenance='Own completed correctness task_status read once; no foreign live query, polling or watcher.')
author=new['tasks'][728]
author.update(observed_utc=now,disposition='PASS_TECHNICAL_ZERO_COUNT',correctness_gate='PASS',
    contribution_gate='TECHNICAL',contribution_condition_discharged=True,
    parent_correctness_intake='discovery-arithmetic-r162aj-parent/proof-intake.json',
    parent_correctness_assessment='discovery-arithmetic-r162aj-parent/proof-assessment.md',
    parent_final_assessment='discovery-arithmetic-r162aj-parent/proof-assessment.md',
    independent_review_obligations='Both independent full-scope reviews adopted. Correctness PASS discharges the condition of TECHNICAL; no acceptance or count.',
    remaining_review_obligations='None for the two adopted reviews. Nominee closed TECHNICAL, zero increment; no retry or downstream work.',
    closed=True,accepted=False,count_change=0)
contribution=new['tasks'][733]
contribution.update(disposition='FULL_SCOPE_TECHNICAL_CONDITION_DISCHARGED',
    contribution_condition_discharged=True,
    parent_condition_discharge_utc=now,
    parent_condition_discharge='discovery-arithmetic-r162aj-parent/proof-intake.json',
    parent_condition_discharge_basis='Independent entire unchanged statement/proof PASS adopted by parent; contribution reviewer did not inspect the other review.',
    accepted=False,count_change=0)
assert contribution['correctness_gate'] is None  # Reviewer issued no correctness verdict.
assert author['statement_sha256']==intake['statement_sha256']
assert author['author_proof_sha256']==intake['author_proof_sha256']

note=('R162AJ entire unchanged frozen theorem/proof correctness PASS adopted, relative to stipulated upstream truth. '
      'Separate full-scope TECHNICAL contribution condition discharged; nominee closed PASS/TECHNICAL, zero increment. '
      'No repair, grade retry, restricted substitute or downstream work. Arithmetic162ak distinct Source105 perfect-completeness 2-to-1 discovery continues under its original brief; no live query or new dispatch. '
      'All older scopes/dispositions unchanged. Campaign19/20,latestR041;publication STOPPED.')
new['last_parent_progress']=note
snap=new['current_work_snapshot']
snap.update(observed_utc=now,note=note)
snap['arithmetic_r162aj_proof_r1']=dict(task_index=732,taskId=terminal['taskId'],status='completed',
    grade='PASS',full_unchanged_frozen_scope=True,independent=True,
    intake='discovery-arithmetic-r162aj-parent/proof-intake.json',publication='STOPPED',count_change=0)
cs=copy.deepcopy(snap['arithmetic_r162aj_contribution_r1'])
cs.update(condition_discharged=True,parent_discharge_intake='discovery-arithmetic-r162aj-parent/proof-intake.json')
snap['arithmetic_r162aj_contribution_r1']=cs
ns=copy.deepcopy(snap['arithmetic_r162aj_nominee'])
ns.update(status='PASS_TECHNICAL_ZERO_COUNT',correctness_gate='PASS',contribution_gate='TECHNICAL',
    contribution_condition_discharged=True,closed=True,accepted=False,count_change=0,
    correctness_intake='discovery-arithmetic-r162aj-parent/proof-intake.json',
    final_assessment='discovery-arithmetic-r162aj-parent/proof-assessment.md')
snap['arithmetic_r162aj_nominee']=ns
snap['arithmetic_r162aj_closed']=dict(correctness='PASS',contribution='TECHNICAL',
    condition_discharged=True,full_scope_preserved=True,accepted=False,count_change=0,
    assessment='discovery-arithmetic-r162aj-parent/proof-assessment.md',publication='STOPPED')
changed=[i for i,(a,b) in enumerate(zip(old['tasks'],new['tasks'])) if a!=b]
assert changed==[728,732,733] and len(old['tasks'])==len(new['tasks'])
assert all(new[k]==old[k] for k in old if k not in {'tasks','last_parent_progress','current_work_snapshot'})
allowed_snap={'observed_utc','note','arithmetic_r162aj_proof_r1','arithmetic_r162aj_contribution_r1',
              'arithmetic_r162aj_nominee','arithmetic_r162aj_closed'}
assert all(snap[k]==v for k,v in old['current_work_snapshot'].items() if k not in allowed_snap)
assert new['tasks'][735]==old['tasks'][735]

addition=('\n\n### R162AJ full correctness adoption and technical closure — '+now+'\n\n'+note+
    '\n\nThe independent review covers exact zero thresholds, behavioral opponents, attainment, predictable all-prefix martingale bounds, both monotone boundary equations, explicit universal-graph generation and the fully charged decision-only quasipolynomial bit bound. No necessary repair or essential correctness obligation remains. This discharges only the previously conditional full-scope TECHNICAL comparison; it does not earn a campaign increment. '
    'Parent assessment: [proof-assessment.md](campaigns/2026-10-14/discovery-arithmetic-r162aj-parent/proof-assessment.md). '
    'Read-only verification matched34 selected artifacts,73 readonly references,3 copied controls,exact37-file review membership/full modes,91 unchanged author files and17 unchanged contribution files. Artifact checks are not mathematical gates. '
    'The reviewer discloses nonessential ancestry/history omissions, incidental metadata exposure and recovered displays. Parent read the full review/limits, not upstream proofs independently. '
    'Only the own terminal result was queried; no foreign live query, watcher, duplicate discovery, public action or grade communication occurred. Earlier intake records and all frozen statement/proof bytes are preserved.\n').encode()
next_t=(json.dumps(new,ensure_ascii=False,indent=2)+'\n').encode()
next_j=raw_j+addition
coord=dict(intake_head=baseline['head'],integration_head=head,head_advanced=head!=baseline['head'],
    before_task_count=len(old['tasks']),after_task_count=len(new['tasks']),changed_old_task_indices=changed,
    no_new_task=True,all_other_tasks_preserved=True,existing_research735_preserved=True,
    all_other_top_fields_preserved=True,journal_prefix_preserved=True,protected_modifications_preserved=True,
    tasks_before_sha256=sha(raw_t),tasks_after_sha256=sha(next_t),
    journal_before_sha256=sha(raw_j),journal_after_sha256=sha(next_j),
    integration_original_brief_guard_checks=checks,no_foreign_live_queries=True)
dump(D/'proof-coordination-rebase.json',coord)
(D/'private/proof-intake/our-tasks-after.json').write_bytes(next_t)
(D/'private/proof-intake/our-journal-after.md').write_bytes(next_j)
for root,before in [
    (B/'arithmetic-r162aj-proof-r1',D/'private/proof-intake/root-before.json'),
    (B/'arithmetic-r162aj-contribution-r1',D/'private/contribution-intake/root-before.json'),
    (B/'fresh-arithmetic-discovery-r162aj',D/'private/intake/root-before.json')]:
    assert snapshot(root)==json.loads(before.read_text())
assert git('rev-parse','HEAD').decode().strip()==head
assert (P/TP).read_bytes()==raw_t and (P/JP).read_bytes()==raw_j
(P/TP).write_bytes(next_t)
(P/JP).write_bytes(next_j)
names=['proof-assessment.md','proof-intake.json','proof-verification.json','verify-proof-intake.py',
       'proof-task-status.json','proof-intake-baseline.json','proof-intake-prospective-isolation.json',
       'manage-proof.py','proof-coordination-rebase.json']
paths=[(D/x).relative_to(P).as_posix() for x in names]+[TP,JP]
assert len(paths)==len(set(paths))==11
assert git('rev-parse','HEAD').decode().strip()==head
assert (P/TP).read_bytes()==next_t and (P/JP).read_bytes()==next_j
subprocess.run(['git','add','--',*paths],cwd=P,check=True)
assert {x for x in git('diff','--cached','--name-only','-z').decode().split('\0') if x}=={'openai-proof-research/'+x for x in paths}
for name in paths:
    assert git('show',':openai-proof-research/'+name)==(P/name).read_bytes()
subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
assert git('rev-parse','HEAD').decode().strip()==head
subprocess.run(['git','commit','-m','Adopt R162AJ correctness and close technical nominee'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip()
assert git('show','HEAD:openai-proof-research/'+TP)==next_t
assert git('show','HEAD:openai-proof-research/'+JP)==next_j
for name,expected in baseline['protected'].items():
    assert sha((P/name).read_bytes())==expected
print(json.dumps(dict(commit=git('rev-parse','HEAD').decode().strip(),
    changed_old_task_indices=changed,all_other_tasks_preserved=True,staged_paths=11,
    disposition='PASS_TECHNICAL_ZERO_COUNT',campaign_count=19,index_empty=True,
    protected_modifications_preserved=True,publication='STOPPED')))
