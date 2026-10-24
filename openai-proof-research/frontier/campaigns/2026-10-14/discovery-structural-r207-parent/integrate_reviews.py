#!/usr/bin/env python3
"""Register two actual independent review dispatches; no grades or count."""
from pathlib import Path
import copy,datetime,hashlib,json,os
P=Path(__file__).resolve().parent; C=P.parent; PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes()); sha=lambda b:hashlib.sha256(b).hexdigest()
owner='164b1204-be68-4540-94bb-0b91055c4381'; now=datetime.datetime.now(datetime.timezone.utc).isoformat(); br=read(P/'review-brief-record.json'); iso=read(P/'review-isolation.json')
assert read(P/'review-runtime.json')['parentThreadId']==iso['parent_thread']==owner and iso['all_review_roots_and_briefs_absent_when_checked']
assert all(e['present'] for e in iso['initial_foreign_brief_checks'])
registry=C/'tasks.json'; ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md'; raw=registry.read_bytes(); t=json.loads(raw); old=copy.deepcopy(t); lr=ledger.read_bytes(); intake_raw=(P/'intake.json').read_bytes(); intake=json.loads(intake_raw)
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
assert t['tasks'][714]['nominee'] and t['tasks'][714]['frozen_sha256']==br['frozen_sha256']==intake['frozen_sha256']
assert not intake['review_dispatches']; entries=[]
for e in br['reviews']:
    role=e['role']; d=read(P/f'{role}-dispatch.json')
    assert d['status'] in ['queued','running'] and d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra'
    assert {x['id']:x['value'] for x in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
    assert sha((PROJECT/e['brief']).read_bytes())==e['sha256'] and not any(x.get('taskId')==d['taskId'] for x in t['tasks'])
    idx=len(t['tasks']); entry=dict(d,parent_thread=owner,role='correctness_review' if role=='proof' else 'contribution_review',round=207,review_round=1,clientRequestId=f'twenty-20261023-structural-r207-{role}-codex-astra-r1',author_task_index=714,source_index=331,output=e['root']+'/',brief=e['brief'],brief_sha256=e['sha256'],brief_bytes=e['bytes'],frozen_sha256=br['frozen_sha256'],proof_sha256=br['proof_sha256'],parent_count_at_dispatch=19,accepted=False,count_change=0,publication='STOPPED',dispatch_receipt=f'discovery-structural-r207-parent/{role}-dispatch.json',prospective_isolation='discovery-structural-r207-parent/review-isolation.json',status_provenance='Actual async dispatch only; no liveness poll.',parent_full_intake_pending=True)
    t['tasks'].append(entry); entries.append({'role':role,'task_index':idx,'taskId':d['taskId'],'status':d['status'],'brief':e['brief'],'brief_sha256':e['sha256'],'output':e['root']+'/'})
t['tasks'][714]['review_dispatches']=entries
intake['review_dispatches']=entries; intake['review_dispatch_utc']=now
s=t['current_work_snapshot']; note='Structural207 unchanged full-scope author nominee now has separate independent correctness and conditional contribution reviews dispatched, Codex/GPT-6 Astra/xhigh/default. Neither review result or grade is adopted. Campaign19/20 latestR041 one remains; publicationSTOPPED. All foreign records preserved.'
t['last_parent_progress']=note; s.update(observed_utc=now,note=note)
s['structural207_review_dispatches']=entries; s['structural207_review_isolation']={'record':'discovery-structural-r207-parent/review-isolation.json','mutually_isolated':True,'frozen_sha256':br['frozen_sha256']}
if 'active_task_indices' in s: s['active_task_indices']=[*s['active_task_indices'],*[e['task_index'] for e in entries]]
if 't3_last_polled_running' in s: s['t3_last_polled_running']=[*s['t3_last_polled_running'],*[e['taskId'] for e in entries]]
changed=[i for i,e in enumerate(old['tasks']) if t['tasks'][i]!=e]; assert changed==[714] and len(t['tasks'])==len(old['tasks'])+2
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in ['observed_utc','note','active_task_indices','t3_last_polled_running'])
heading='## Structural207 independent correctness and contribution reviews dispatched'; assert heading.encode() not in lr
append='\n'+heading+'\n\nTwo separate mutually isolated reviews are running at the entire unchanged frozen compact-law product-tree scope. The [correctness brief](campaigns/2026-10-14/expanded-target-2026-10-17/structural-r207-proof-r1-brief.txt) requires all mathematical claims, mixed-law scalar limits, conditional first-moment estimates, modulus quantifiers, bounded-limit necessity and the full equivalent-norm zero interval to be checked. The [contribution brief](campaigns/2026-10-14/expanded-target-2026-10-17/structural-r207-contribution-r1-brief.txt) requires the strongest compatible full-scope source/classical/primary reduction; correctness remains UNDISCHARGED in that role. Neither may use the other review.\n\nBoth actual async responses select Codex/GPT-6 Astra/xhigh/default, matching live descriptors. The original author brief and exact frozen statement are supplied in full. All337 inherited wildcard/no-r guards and162 substring exclusions persist. Original initial foreign brief literal/hash checks preceded creation of both review briefs and roots; no foreign liveness or mathematical body was inspected. Exact immutable author-input exceptions do not admit old scopes or parent/peer bodies. No author edits, narrowing, grades or count are authorized. Parent alone adopts results.\n\n**19/20, latest R041, one remaining; correctness and contribution pending; publication STOPPED.**\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr and (P/'intake.json').read_bytes()==intake_raw
tmp=registry.with_suffix('.structural207-reviews.tmp'); tmp.write_text(json.dumps(t,indent=2)+'\n'); assert registry.read_bytes()==raw; os.replace(tmp,registry)
assert ledger.read_bytes()==lr; ledger.write_bytes(lr+append.encode()); (P/'intake.json').write_text(json.dumps(intake,indent=2)+'\n')
out={'observed_utc':now,'changed_existing_tasks':changed,'added_task_indices':[e['task_index'] for e in entries],'all_other_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0,'status_from_actual_dispatch_only':True}
(P/'review-integration-record.json').write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps(out,indent=2))
