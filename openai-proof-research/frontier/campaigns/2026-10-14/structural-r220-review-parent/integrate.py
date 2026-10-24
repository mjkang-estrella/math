#!/usr/bin/env python3
"""Register actual independent review dispatches; preserve every existing task."""
from pathlib import Path
import copy,datetime,hashlib,json,os
R=Path(__file__).resolve().parent;C=R.parent;PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest()
owner='164b1204-be68-4540-94bb-0b91055c4381';now=datetime.datetime.now(datetime.timezone.utc).isoformat()
runtime=read(R/'runtime.json');iso=read(R/'prospective-isolation.json');brief_record=read(R/'brief-records.json');briefs=brief_record['records']
assert runtime['parentThreadId']==owner and iso['foreign_parent_thread']=='6742db91-d35c-44d0-a762-e5d9232f5177'
assert len(iso['paths_absent_before_creation'])==5 and all(x['literal_present'] for x in iso['foreign_initial_brief_checks'])
registry=C/'tasks.json';ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md';raw=registry.read_bytes();lr=ledger.read_bytes();t=json.loads(raw);old=copy.deepcopy(t)
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
assert t['tasks'][751]['parent_disposition']=='AWAITING_INDEPENDENT_REVIEWS'
added=[]
for b in briefs:
    role=b['role'];d=read(R/(role+'-dispatch.json'))
    assert d['status'] in ['queued','running'] and d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra'
    assert {e['id']:e['value'] for e in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
    assert sha((PROJECT/b['brief']).read_bytes())==b['sha256']
    assert not any(e.get('taskId')==d['taskId'] or e.get('brief')==b['brief'] for e in t['tasks'])
    idx=len(t['tasks']);entry=dict(d,parent_thread=owner,role='correctness' if role=='proof' else 'contribution',round=1,structural_round=220,clientRequestId='twenty-20261024-structural-r220-'+role+'-codex-astra-r1',source_index=344,output=b['output'],brief=b['brief'],brief_sha256=b['sha256'],brief_bytes=b['bytes'],author_task_index=751,statement_sha256=brief_record['statement_sha256'],proof_sha256=brief_record['proof_sha256'],parent_count_at_dispatch=19,accepted=False,count_change=0,publication='STOPPED',dispatch_receipt='structural-r220-review-parent/'+role+'-dispatch.json',prospective_isolation='structural-r220-review-parent/prospective-isolation.json',status_provenance='Actual async dispatch response only; no subsequent liveness poll.',parent_full_intake_pending=True)
    t['tasks'].append(entry);added.append({'task_index':idx,'role':entry['role'],'taskId':d['taskId'],'status':d['status'],'brief':b['brief'],'brief_sha256':b['sha256'],'output':entry['output'],'dispatch_receipt':entry['dispatch_receipt']})
note='Structural220 full unchanged nominee is in separate independent correctness and contribution reviews, Codex/GPT-6 Astra/xhigh/default. Author packet and intake committed; no grades, acceptance or count. Campaign 19/20, latest R041, one remaining; publication STOPPED. Existing foreign records preserved.'
t['last_parent_progress']=note;s=t['current_work_snapshot'];s.update(observed_utc=now,note=note)
s['structural220_review_dispatches']=added;s['structural220_review_isolation']='structural-r220-review-parent/prospective-isolation.json'
if 'active_task_indices' in s:s['active_task_indices']=[*s['active_task_indices'],*(e['task_index'] for e in added)]
if 't3_last_polled_running' in s:s['t3_last_polled_running']=[*s['t3_last_polled_running'],*(e['taskId'] for e in added)]
assert t['tasks'][:-2]==old['tasks']
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in ['observed_utc','note','active_task_indices','t3_last_polled_running'])
heading='## Structural220 independent reviews dispatched';assert heading.encode() not in lr
append='\n## Structural220 independent reviews dispatched\n\nTwo fresh round-one tasks now review the entire unchanged frozen statement AND submitted proof: [correctness brief](campaigns/2026-10-14/expanded-target-2026-10-17/structural-r220-proof-r1-brief.txt) and [conditional contribution brief](campaigns/2026-10-14/expanded-target-2026-10-17/structural-r220-contribution-r1-brief.txt). Both actual async receipts confirm Codex / GPT-6 Astra / xhigh / default, matching fresh live descriptors. Each brief includes the complete original discovery instructions verbatim, exact sealed author-input admission and anchors computed from verified bytes. Neither reviewer reads the peer review or parent findings. No prior review findings or responses exist for this first round.\n\nCorrectness scrutiny covers the arbitrary endpoint orders, exact nonnegative decomposition and integrability, all matrix/coupling variance costs, calibration, free middle residue, one common shear, threshold/power calculations, derivative interpolation, zero defect and nonvacuity. Contribution scrutiny must execute the strongest compatible source/Kazdan/logdet/Schur/endpoint/interpolation construction through the entire same scope and isolate any indispensable nonroutine step. Correctness of the entire statement AND proof remains UNDISCHARGED in the contribution role. Parent alone combines and adopts reviews.\n\nBefore creating either review root or brief, original initial foreign-brief hashes and the literal structural220 exclusion were checked using the union of active snapshot and explicit foreign-parent queued/running/waiting registry metadata only. All363 wildcard/no-r and162 substring guards remain, with the exact sealed author packet as the sole input exception. No foreign liveness or mathematical body was inspected. Author bytes and modes remain unchanged. No grade, acceptance or count. **19/20, latest R041, one remaining; publication STOPPED.**\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr
tmp=registry.with_suffix('.structural220-reviews.tmp');tmp.write_text(json.dumps(t,indent=2)+'\n');assert registry.read_bytes()==raw;os.replace(tmp,registry)
assert ledger.read_bytes()==lr;ledger.write_bytes(lr+append.encode())
out={'observed_utc':now,'added_tasks':added,'all_previous_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0,'status_from_actual_dispatch_only':True}
(R/'integration-record.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
