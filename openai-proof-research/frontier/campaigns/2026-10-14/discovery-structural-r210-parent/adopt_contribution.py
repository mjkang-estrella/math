#!/usr/bin/env python3
"""Reconcile the delivered conditional contribution result with adopted correctness."""
from pathlib import Path
import copy, datetime, hashlib, json, os
P=Path(__file__).resolve().parent; C=P.parent; PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes()); sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
d=read(P/'contribution-task-status.json'); r=read(P/'contribution-replay.json'); proof=read(P/'proof-intake.json')
now=datetime.datetime.now(datetime.timezone.utc).isoformat(); owner='164b1204-be68-4540-94bb-0b91055c4381'
assert d['status']=='completed' and not d['hasPendingChildRuns']
assert d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra'
assert {e['id']:e['value'] for e in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
assert r['review_originals_unchanged'] and r['author_files_unchanged']==186 and proof['correctness']=='PASS'
registry=C/'tasks.json'; ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md'; raw=registry.read_bytes(); lr=ledger.read_bytes()
t=json.loads(raw); old=copy.deepcopy(t); assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
author=t['tasks'][727]; review=t['tasks'][730]; assert author['parent_thread']==review['parent_thread']==owner
assert author['correctness']=='PASS' and author['contribution']=='PENDING' and review['parent_full_intake_pending']
assert review['taskId']==d['taskId'] and sha(PROJECT/review['brief'])==review['brief_sha256']=='9bccd7ce48ad7c1ec142ce74d2d005c2d4d3b949a8c65755ee52edfe848f0845'
assert all(author[k]==review[k]==proof[k] for k in ['frozen_sha256','proof_sha256'])
ip=P/'intake.json'; ir=ip.read_bytes(); intake=json.loads(ir); old_intake=copy.deepcopy(intake)
disposition='CLOSED_FULL_SCOPE_PASS_TECHNICAL_ZERO_COUNT'
ci={'observed_utc':now,'parent_thread':owner,'task_index':730,'taskId':d['taskId'],'author_task_index':727,'source_index':334,'scope':'Entire unchanged frozen statement and submitted proof','correctness':'PASS','upstream_truth_stipulated':True,'contribution':'TECHNICAL','reviewer_correctness':'UNDISCHARGED','condition':'Full correctness of the entire unchanged frozen statement and submitted proof','condition_discharged_by':'discovery-structural-r210-parent/proof-intake.json','frozen_sha256':author['frozen_sha256'],'proof_sha256':author['proof_sha256'],'disposition':disposition,'accepted':False,'count_change':0,'newAccepted':19,'latestAcceptance':'R041','remaining':1,'publication':'STOPPED','anchors':r['anchors'],'assessment_sha256':sha(P/'contribution-assessment.md'),'artifact_replay':r,'next':'Distinct discovery under all inherited exclusions; do not reopen or resubmit Structural210.'}
for k in ['status','workState','hasPendingChildRuns','latestTerminalRunId','latestTerminalStatus','latestTerminalSummary','latestTerminalResultContextTransferId','summary','resultContextTransferId','hasPendingQuestion','pendingApproval','waitTimedOut','observed_utc']:review[k]=d[k]
review.update(parent_full_intake_pending=False,parent_disposition='CONDITIONAL_TECHNICAL_ADOPTED_CONDITION_DISCHARGED',contribution='TECHNICAL',reviewer_correctness='UNDISCHARGED',condition_discharged_by=ci['condition_discharged_by'],parent_intake='discovery-structural-r210-parent/contribution-intake.json',parent_intake_utc=now,status_provenance='Terminal lookup after delivered owned completion only; no foreign liveness lookup.')
author.update(contribution='TECHNICAL',parent_disposition=disposition,contribution_intake='discovery-structural-r210-parent/contribution-intake.json',closed_utc=now,accepted=False,count_change=0)
intake.update(contribution='TECHNICAL',disposition=disposition,contribution_intake='discovery-structural-r210-parent/contribution-intake.json',contribution_adopted_utc=now,condition_discharged_by=ci['condition_discharged_by'],closed_utc=now,next=ci['next'])
s=t['current_work_snapshot']
for rows in [author['review_dispatches'],intake['review_dispatches'],s['structural210_review_dispatches']]:
    e=next(x for x in rows if x['task_index']==730); e.update(status='completed',contribution='TECHNICAL',intake='discovery-structural-r210-parent/contribution-intake.json')
for key in ['structural210_dispatch','structural210_parent_intake']:
    s[key].update(disposition=disposition,correctness='PASS',contribution='TECHNICAL',count_change=0)
s['structural210_contribution_adoption']={'task_index':730,'contribution':'TECHNICAL','correctness':'PASS','condition_discharged_by':ci['condition_discharged_by'],'intake':'discovery-structural-r210-parent/contribution-intake.json','count_change':0}
s['structural210_closed']={'author_task_index':727,'correctness_task_index':729,'contribution_task_index':730,'disposition':disposition,'correctness':'PASS','contribution':'TECHNICAL','intake':'discovery-structural-r210-parent/intake.json','count_change':0}
if 'active_task_indices' in s:s['active_task_indices']=[i for i in s['active_task_indices'] if i!=730]
if 't3_last_polled_running' in s:s['t3_last_polled_running']=[x for x in s['t3_last_polled_running'] if x!=d['taskId']]
note='Structural210 closed at the entire unchanged scope: correctness PASS under stipulated upstream truth, contribution TECHNICAL with full correctness condition discharged. Zero count. Campaign 19/20, latest R041, one remaining; publication STOPPED. Distinct discovery next; all other tasks preserved.'
t['last_parent_progress']=note; s.update(observed_utc=now,note=note)
changed=[i for i,x in enumerate(old['tasks']) if t['tasks'][i]!=x]; assert changed==[727,730] and len(t['tasks'])==len(old['tasks'])
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
allowed={'observed_utc','note','active_task_indices','t3_last_polled_running','structural210_dispatch','structural210_parent_intake','structural210_review_dispatches'}
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in allowed)
for before,after in [(old['tasks'][727]['review_dispatches'],author['review_dispatches']),(old_intake['review_dispatches'],intake['review_dispatches']),(old['current_work_snapshot']['structural210_review_dispatches'],s['structural210_review_dispatches'])]:assert [x for x in before if x['task_index']!=730]==[x for x in after if x['task_index']!=730]
heading='## Structural210 closed: full-scope PASS / TECHNICAL, zero count'; assert heading.encode() not in lr
append='\n'+heading+'\n\nThe parent read the full independent [contribution review](campaigns/2026-10-14/structural-r210-contribution-r1/packet/REVIEW.md) and adopts **TECHNICAL for the entire unchanged frozen statement and submitted proof**. The separate full-scope correctness PASS, under stipulated upstream truth, discharges the contribution condition. The reviewer’s own immutable correctness status remains UNDISCHARGED. See [parent reconciliation](campaigns/2026-10-14/discovery-structural-r210-parent/contribution-assessment.md).\n\nThe complete compatible reduction includes quantitative boundary flux, finite spatial and angular capture, independently small collar slope and model amplitudes, arbitrary closed nowhere-dense accumulation sets, positive flat curvature background, metric prescription and tensor scaling, exact exterior zeros, both locus inclusions, coefficient bounds and all frozen jets. No essential contribution comparison remains unresolved. Read-only replay matched 129 selected review files and 16 directories; all 186 author files and modes remained unchanged. Seven tiny copied controls behaved as expected. Reading/access/history and comparator limitations remain explicit; identity checks are not mathematical evidence.\n\nStructural210 is closed without revision or another review round. Distinct discovery follows under every inherited exclusion. **No acceptance or count: 19/20, latest R041, one remaining; publication STOPPED.**\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr and ip.read_bytes()==ir
(P/'contribution-intake.json').write_text(json.dumps(ci,indent=2)+'\n'); ip.write_text(json.dumps(intake,indent=2)+'\n')
tmp=registry.with_suffix('.structural210-contribution.tmp'); tmp.write_text(json.dumps(t,indent=2)+'\n'); assert registry.read_bytes()==raw; os.replace(tmp,registry)
assert ledger.read_bytes()==lr; ledger.write_bytes(lr+append.encode())
record={'observed_utc':now,'changed_existing_tasks':changed,'new_tasks':0,'all_other_tasks_unchanged':True,'other_snapshot_entries_preserved':True,'correctness':'PASS','contribution':'TECHNICAL','full_scope_condition_discharged':True,'count_change':0}
(P/'contribution-adoption-record.json').write_text(json.dumps(record,indent=2)+'\n'); print(json.dumps(record,indent=2))
