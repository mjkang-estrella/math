#!/usr/bin/env python3
"""Register independent review dispatches without adopting either mathematical grade."""
from pathlib import Path
import copy,datetime,hashlib,json,os
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
owner='164b1204-be68-4540-94bb-0b91055c4381';now=datetime.datetime.now(datetime.timezone.utc).isoformat();br=read(P/'review-brief-record.json');iso=read(P/'review-isolation.json');runtime=read(P/'review-runtime.json')
assert iso['all_roots_and_briefs_absent_when_checked'] and iso['mutually_isolated'] and all(e['present'] for e in iso['initial_brief_checks_before_new_root_or_brief']) and runtime['parentThreadId']==owner
registry=C/'tasks.json';ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md';raw=registry.read_bytes();t=json.loads(raw);old=copy.deepcopy(t);lr=ledger.read_bytes();ir=(P/'intake.json').read_bytes();intake=json.loads(ir)
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
author=t['tasks'][721];assert author['parent_thread']==owner and author['nominee'] and author['correctness']==author['contribution']=='PENDING' and not author['review_dispatches']
assert sha(C/'fresh-structural-discovery-r209/FROZEN-STATEMENT.md')==author['frozen_sha256']==iso['author_frozen_sha256']
assert sha(C/'fresh-structural-discovery-r209/AUTHOR-PROOF.md')==author['proof_sha256']==iso['author_proof_sha256']
entries=[]
for e in br['records']:
    role=e['role'];d=read(P/(role+'-dispatch.json'));assert d['status'] in ['queued','running'] and d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra'
    assert {x['id']:x['value'] for x in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
    assert sha(PROJECT/e['brief'])==e['brief_sha256'] and e['frozen_sha256']==author['frozen_sha256'] and e['proof_sha256']==author['proof_sha256']
    assert not any(x.get('taskId')==d['taskId'] or x.get('brief')==e['brief'] for x in t['tasks']);idx=len(t['tasks'])
    row=dict(d,parent_thread=owner,role='correctness_review' if role=='proof' else 'contribution_review',round=209,review_round=1,clientRequestId=f'twenty-20261023-structural-r209-{role}-codex-astra-r1',author_task_index=721,source_index=333,output=e['output'],brief=e['brief'],brief_sha256=e['brief_sha256'],brief_bytes=e['brief_bytes'],frozen_sha256=author['frozen_sha256'],proof_sha256=author['proof_sha256'],parent_count_at_dispatch=19,accepted=False,count_change=0,publication='STOPPED',dispatch_receipt=f'discovery-structural-r209-parent/{role}-dispatch.json',prospective_isolation='discovery-structural-r209-parent/review-isolation.json',status_provenance='Actual async dispatch only; no liveness poll.',parent_full_intake_pending=True)
    t['tasks'].append(row);entries.append({'role':role,'task_index':idx,'taskId':d['taskId'],'status':d['status'],'brief':e['brief'],'brief_sha256':e['brief_sha256'],'output':e['output']})
disposition='AUTHOR_NOMINEE_UNDER_INDEPENDENT_REVIEW';author.update(parent_disposition=disposition,review_dispatches=entries)
intake.update(disposition=disposition,review_dispatches=entries,review_dispatch_utc=now)
s=t['current_work_snapshot'];s['structural209_dispatch']['disposition']=disposition;s['structural209_parent_intake']['disposition']=disposition;s['structural209_review_dispatches']=entries;s['structural209_review_isolation']={'record':'discovery-structural-r209-parent/review-isolation.json','mutually_isolated':True,'frozen_sha256':author['frozen_sha256']}
if 'active_task_indices' in s:s['active_task_indices'] += [e['task_index'] for e in entries]
if 't3_last_polled_running' in s:s['t3_last_polled_running'] += [e['taskId'] for e in entries]
note='Structural209 unchanged T333Q209 now has mutually isolated correctness and contribution reviews running, Codex/GPT-6 Astra/xhigh/default. No grades, acceptance or count. Campaign19/20 latestR041 one remains; publicationSTOPPED. All foreign records preserved.'
t['last_parent_progress']=note;s.update(observed_utc=now,note=note)
assert [i for i,x in enumerate(old['tasks']) if t['tasks'][i]!=x]==[721] and len(t['tasks'])==len(old['tasks'])+2
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in ['observed_utc','note','active_task_indices','t3_last_polled_running','structural209_dispatch','structural209_parent_intake'])
heading='## Structural209 independent correctness and contribution reviews dispatched';assert heading.encode() not in lr
append='\n'+heading+'\n\nTwo mutually isolated first-round reviews now examine the exact same unchanged frozen statement and submitted proof of T333Q209. [Correctness brief](campaigns/2026-10-14/expanded-target-2026-10-17/structural-r209-proof-r1-brief.txt) covers the periodic obstruction, finite derivative recursion, fixed-reference smoothing and uniform-threshold/waiting-time quantifiers, embedding and sharp lower bound. [Contribution brief](campaigns/2026-10-14/expanded-target-2026-10-17/structural-r209-contribution-r1-brief.txt) requires the strongest compatible source/classical/primary/original-history reduction, including singular or perturbed-map alternatives, at the entire scope and explicit derivative budget. Correctness remains UNDISCHARGED in the contribution role. Neither reviewer receives the other’s findings.\n\nBoth actual dispatch responses match **Codex / GPT-6 Astra / xhigh / default**. Complete original discovery/standing instructions and the exact frozen statement are included in each prompt. All341 wildcard/no-r and162 substring guards, prospective administrative-heading filtering, author immutability and rights limits remain. Foreign original initial briefs were checked prospectively for the structural209 literal, using shared metadata/hashes only; no foreign liveness or mathematical body was read. No prior independent findings or author responses existed.\n\nNo mathematical grade, acceptance or count is adopted. **19/20, latest R041, one remaining; publication STOPPED.**\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr and (P/'intake.json').read_bytes()==ir
tmp=registry.with_suffix('.structural209-reviews.tmp');tmp.write_text(json.dumps(t,indent=2)+'\n');assert registry.read_bytes()==raw;os.replace(tmp,registry)
assert ledger.read_bytes()==lr;ledger.write_bytes(lr+append.encode());(P/'intake.json').write_text(json.dumps(intake,indent=2)+'\n')
out={'observed_utc':now,'changed_existing_tasks':[721],'new_tasks':entries,'all_other_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0,'status_from_actual_dispatch_only':True}
(P/'review-integration-record.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
