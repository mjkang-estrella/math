#!/usr/bin/env python3
"""Adopt the completed full-scope correctness review; leave contribution untouched."""
from pathlib import Path
import copy,datetime,hashlib,json,os
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
d=read(P/'proof-task-status.json');r=read(P/'proof-replay.json');owner='164b1204-be68-4540-94bb-0b91055c4381';now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert d['status']=='completed' and d['workState']=='result_available' and not d['hasPendingChildRuns']
assert d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra' and {e['id']:e['value'] for e in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
assert r['review_originals_bytes_modes_unchanged'] and r['whole_author_root_unchanged_since_parent_intake']
registry=C/'tasks.json';ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md';raw=registry.read_bytes();lr=ledger.read_bytes();t=json.loads(raw);old=copy.deepcopy(t)
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
idx=744;e=t['tasks'][idx];author=t['tasks'][743]
assert e['taskId']==d['taskId'] and e['parent_thread']==owner and e['parent_full_intake_pending']
assert sha(PROJECT/e['brief'])==e['brief_sha256']=='59b3623307d05875c472dec26bdd1e808aa680b178fac828c5c0f647a21ac578'
assert author['parent_thread']==owner and author['correctness']=='NOT_ASSIGNED'
intake={'observed_utc':now,'parent_thread':owner,'task_index':idx,'taskId':d['taskId'],'author_task_index':743,'scope':'Entire unchanged frozen statement AND submitted AUTHOR-PROOF.md, including auxiliary comparisons.','statement_sha256':e['statement_sha256'],'proof_sha256':e['proof_sha256'],'correctness':'PASS','correctness_basis':'Stipulated Source340 truth and explicitly cited primary interfaces; no essential repair or unresolved obligation.','contribution':'PENDING','accepted':False,'count_change':0,'newAccepted':19,'latestAcceptance':'R041','remaining':1,'publication':'STOPPED','assessment_sha256':sha(P/'proof-assessment.md'),'erratum_sha256':sha(P/'verifier-anchor-erratum.md'),'artifact_replay':r,'next':'Await separately dispatched contribution review; no new discovery, polling, peer steering or downstream work.'}
for k in ['status','workState','hasPendingChildRuns','latestTerminalRunId','latestTerminalStatus','latestTerminalSummary','latestTerminalResultContextTransferId','summary','resultContextTransferId','hasPendingQuestion','pendingApproval','waitTimedOut','observed_utc']:e[k]=d[k]
e.update(parent_disposition='ADOPTED_FULL_SCOPE_CORRECTNESS_PASS',parent_full_intake_pending=False,parent_intake='structural-r216-review-parent/proof-intake.json',parent_intake_utc=now,correctness='PASS',accepted=False,count_change=0,status_provenance='Terminal lookup after delivered owned correctness completion only; no other task liveness lookup.')
author.update(correctness='PASS',correctness_adoption='structural-r216-review-parent/proof-intake.json',parent_disposition='AWAITING_CONTRIBUTION_REVIEW')
s=t['current_work_snapshot']
for x in s['structural216_review_dispatches']:
    if x['task_index']==idx:x.update(status='completed',correctness='PASS',intake='structural-r216-review-parent/proof-intake.json')
s['structural216_parent_intake'].update(correctness='PASS',disposition='AWAITING_CONTRIBUTION_REVIEW',correctness_adoption='structural-r216-review-parent/proof-intake.json')
s['structural216_correctness_adoption']={'task_index':idx,'correctness':'PASS','scope':'Entire unchanged statement AND proof','intake':'structural-r216-review-parent/proof-intake.json','count_change':0}
note='Structural216 full-scope correctness PASS adopted after complete review reading and artifact replay. Parent verifier-hash transcription error documented; actual author packet unchanged. Separate contribution verdict pending, no acceptance/count. Campaign 19/20, latest R041, one remaining; publication STOPPED.'
t['last_parent_progress']=note;s.update(observed_utc=now,note=note)
if 'active_task_indices' in s:s['active_task_indices']=[i for i in s['active_task_indices'] if i!=idx]
if 't3_last_polled_running' in s:s['t3_last_polled_running']=[x for x in s['t3_last_polled_running'] if x!=d['taskId']]
changed=[i for i,x in enumerate(old['tasks']) if t['tasks'][i]!=x];assert changed==[743,744] and len(t['tasks'])==len(old['tasks'])
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
allowed=['observed_utc','note','active_task_indices','t3_last_polled_running','structural216_review_dispatches','structural216_parent_intake']
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in allowed)
assert [x for x in s['structural216_review_dispatches'] if x['task_index']!=idx]==[x for x in old['current_work_snapshot']['structural216_review_dispatches'] if x['task_index']!=idx]
heading='## Structural216 correctness adopted: full-scope PASS';assert heading.encode() not in lr
append='\n'+heading+'\n\nParent read the complete independent [correctness review](campaigns/2026-10-14/structural-r216-proof-r1/packet/REVIEW.md) and adopts **PASS for the entire unchanged frozen statement AND submitted proof**, relative to stipulated Source340 truth and the explicitly cited primary interfaces. All twelve checks are addressed, including the natural integral coset, actual small double, regular compact partition and smooth cap comparisons, rigid action and all six unmarked pairs. No essential repair, narrowing or unresolved correctness obligation is identified. See [parent assessment](campaigns/2026-10-14/structural-r216-review-parent/proof-assessment.md).\n\nExplicit-anchor replay matched 17 selected files and two subdirectories; the review and all author originals remained unchanged. Seven copied controls behaved as expected. Reading/version/access/truncation/editorial limits remain disclosed; source/primary identities were bound without inherited parent semantic reading. Exact Lean navigation returned404 and supplies no formal support. The standalone verifier hash in both original review briefs was a parent transcription error; the actual script matches the original parent baseline and committed author version, while all four packet anchors match. The [erratum](campaigns/2026-10-14/structural-r216-review-parent/verifier-anchor-erratum.md) preserves that discrepancy without altering either brief or sealed packet.\n\nThe separately dispatched contribution review remains pending and was not polled or steered. No contribution grade, acceptance or count is adopted. **19/20, latest R041, one remaining; publication STOPPED.**\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr
(P/'proof-intake.json').write_text(json.dumps(intake,indent=2)+'\n');tmp=registry.with_suffix('.structural216-proof.tmp');tmp.write_text(json.dumps(t,indent=2)+'\n');assert registry.read_bytes()==raw;os.replace(tmp,registry)
assert ledger.read_bytes()==lr;ledger.write_bytes(lr+append.encode())
out={'observed_utc':now,'changed_existing_tasks':changed,'all_other_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'contribution_task_untouched':True,'count_change':0}
(P/'proof-adoption-record.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
