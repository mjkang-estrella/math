#!/usr/bin/env python3
"""Register actual independent review dispatches; preserve every existing task."""
from pathlib import Path
import copy,datetime,hashlib,json,os
R=Path(__file__).resolve().parent;C=R.parent;PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes());sha=lambda b:hashlib.sha256(b).hexdigest()
owner='164b1204-be68-4540-94bb-0b91055c4381';now=datetime.datetime.now(datetime.timezone.utc).isoformat()
runtime=read(R/'runtime.json');iso=read(R/'prospective-isolation.json');briefs=read(R/'brief-records.json')
assert runtime['parentThreadId']==iso['parent_thread']==owner
assert iso['roots_and_briefs_absent_when_checked'] and all(x['present'] for x in iso['initial_brief_checks_before_new_root_or_brief'])
registry=C/'tasks.json';ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md';raw=registry.read_bytes();lr=ledger.read_bytes();t=json.loads(raw);old=copy.deepcopy(t)
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
assert t['tasks'][743]['parent_disposition']=='AWAITING_INDEPENDENT_REVIEWS'
added=[]
for b in briefs:
    role=b['role'];d=read(R/(role+'-dispatch.json'))
    assert d['status'] in ['queued','running'] and d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra'
    assert {e['id']:e['value'] for e in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
    assert sha((PROJECT/b['brief']).read_bytes())==b['brief_sha256']
    assert not any(e.get('taskId')==d['taskId'] or e.get('brief')==b['brief'] for e in t['tasks'])
    idx=len(t['tasks']);entry=dict(d,parent_thread=owner,role='correctness' if role=='proof' else 'contribution',round=1,structural_round=216,clientRequestId=b['clientRequestId'],source_index=340,output=b['root']+'/',brief=b['brief'],brief_sha256=b['brief_sha256'],brief_bytes=b['brief_bytes'],author_task_index=743,statement_sha256='75b55258f022d13db6995649a1ab7d7f29b80066721e560dd01cfb4ca9ddb6e3',proof_sha256='eae38f752f868a3d4e7ad601c3d24e41926f8dad8341929b943f6735bbf792ba',parent_count_at_dispatch=19,accepted=False,count_change=0,publication='STOPPED',dispatch_receipt='structural-r216-review-parent/'+role+'-dispatch.json',prospective_isolation='structural-r216-review-parent/prospective-isolation.json',status_provenance='Actual async dispatch response only; no subsequent liveness poll.',parent_full_intake_pending=True)
    t['tasks'].append(entry);added.append({'task_index':idx,'role':entry['role'],'taskId':d['taskId'],'status':d['status'],'brief':b['brief'],'brief_sha256':b['brief_sha256'],'output':entry['output'],'dispatch_receipt':entry['dispatch_receipt']})
note='Structural216 full unchanged nominee is in separate independent correctness and contribution reviews, Codex/GPT-6 Astra/xhigh/default. Author packet and intake committed; no grades, acceptance or count. Campaign 19/20, latest R041, one remaining; publication STOPPED. Existing foreign records preserved.'
t['last_parent_progress']=note;s=t['current_work_snapshot'];s.update(observed_utc=now,note=note)
s['structural216_review_dispatches']=added;s['structural216_review_isolation']='structural-r216-review-parent/prospective-isolation.json'
if 'active_task_indices' in s:s['active_task_indices']=[*s['active_task_indices'],*(e['task_index'] for e in added)]
if 't3_last_polled_running' in s:s['t3_last_polled_running']=[*s['t3_last_polled_running'],*(e['taskId'] for e in added)]
assert t['tasks'][:-2]==old['tasks']
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in ['observed_utc','note','active_task_indices','t3_last_polled_running'])
heading='## Structural216 independent reviews dispatched';assert heading.encode() not in lr
append='\n'+heading+'\n\nTwo fresh round-one tasks now review the entire unchanged frozen statement AND submitted proof: [correctness brief](campaigns/2026-10-14/expanded-target-2026-10-17/structural-r216-proof-r1-brief.txt) and [conditional contribution brief](campaigns/2026-10-14/expanded-target-2026-10-17/structural-r216-contribution-r1-brief.txt). Both actual async receipts confirm Codex / GPT-6 Astra / xhigh / default, matching the fresh live descriptors. Each brief includes the complete original discovery instructions and exact immutable author-input selection. Neither reviewer reads the other review or parent findings. No prior review findings or responses exist for this first round.\n\nThe correctness assignment examines the integral natural coset of unmarked images, canonical separated double, zero-regular radial homotopies, compactification/smoothing, rigid action and every pair on one common base. The contribution assignment must execute the strongest compatible source and primary construction through the same full scope; its condition is correctness of both the entire statement and submitted proof, not selected lemmas. Parent alone adopts.\n\nBefore creating either namespace or brief, original initial foreign-brief hashes and the literal structural216 exclusion were checked through shared coordination metadata only. All 355 wildcard/no-r and 162 substring guards remain; the exact sealed author input is the sole new read exception. No foreign liveness or mathematical bodies were inspected. No nominee mutation, grade, acceptance or count. **19/20, latest R041, one remaining; publication STOPPED.**\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr
tmp=registry.with_suffix('.structural216-reviews.tmp');tmp.write_text(json.dumps(t,indent=2)+'\n');assert registry.read_bytes()==raw;os.replace(tmp,registry)
assert ledger.read_bytes()==lr;ledger.write_bytes(lr+append.encode())
out={'observed_utc':now,'added_tasks':added,'all_previous_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0,'status_from_actual_dispatch_only':True}
(R/'integration-record.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
