#!/usr/bin/env python3
"""Adopt the conditional contribution review without discharging correctness."""
from pathlib import Path
import copy,datetime,hashlib,json,os
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
d=read(P/'contribution-task-status.json');r=read(P/'contribution-replay.json');owner='164b1204-be68-4540-94bb-0b91055c4381';now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert d['status']=='completed' and not d['hasPendingChildRuns'] and r['review_originals_bytes_modes_unchanged'] and r['all_author_baseline_bytes_modes_unchanged']
assert d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra' and {x['id']:x['value'] for x in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
registry=C/'tasks.json';ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md';raw=registry.read_bytes();lr=ledger.read_bytes();t=json.loads(raw);old=copy.deepcopy(t)
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
idx=753;ai=751;e=t['tasks'][idx];a=t['tasks'][ai]
assert e['taskId']==d['taskId'] and e['parent_thread']==owner and e['parent_full_intake_pending'] and e['role']=='contribution'
assert a['parent_thread']==owner and a['parent_disposition']=='AWAITING_INDEPENDENT_REVIEWS' and a['correctness']=='NOT_ASSIGNED'
assert sha(PROJECT/e['brief'])==e['brief_sha256']=='105c79d5857109ab134ca1d36ae007ee01490fe5f8dc30298f34bbb368ceea1e'
ar=read(C/'discovery-structural-r220-parent/replay.json');A=C/'fresh-structural-discovery-r220/packet'
assert sha(A/'STATEMENT.md')==ar['statement_sha256']==e['statement_sha256'] and sha(A/'PROOF.md')==ar['proof_sha256']==e['proof_sha256']
disposition='ADOPTED_CONDITIONAL_TECHNICAL';author_state='AWAITING_CORRECTNESS_CONDITIONAL_TECHNICAL'
intake={'observed_utc':now,'parent_thread':owner,'task_index':idx,'author_task_index':ai,'taskId':d['taskId'],'disposition':disposition,'author_disposition':author_state,'scope':'Entire unchanged frozen statement AND submitted proof','statement_sha256':ar['statement_sha256'],'proof_sha256':ar['proof_sha256'],'contribution':'TECHNICAL','contribution_condition':'Full correctness of the entire unchanged statement AND submitted proof','correctness_condition':'UNDISCHARGED','correctness':'NOT_ASSIGNED','accepted':False,'count_change':0,'newAccepted':19,'latestAcceptance':'R041','remaining':1,'publication':'STOPPED','anchors':r['anchors'],'assessment_sha256':sha(P/'contribution-assessment.md'),'artifact_replay':r,'remaining_obligations':['Separate full-scope correctness review remains outstanding; no correctness result has been inspected in this intake.'],'essential_contribution_comparison_unresolved':False,'next':'Intake the owned correctness completion when delivered; no polling, author repair, narrowing, grade shopping or new count.'}
for k in ['status','workState','hasPendingChildRuns','latestTerminalRunId','latestTerminalStatus','latestTerminalSummary','latestTerminalResultContextTransferId','summary','resultContextTransferId','hasPendingQuestion','pendingApproval','waitTimedOut']:e[k]=d[k]
e.update(observed_utc=now,parent_disposition=disposition,parent_full_intake_pending=False,parent_intake='structural-r220-review-parent/contribution-intake.json',parent_intake_utc=now,contribution='TECHNICAL',correctness_condition='UNDISCHARGED',accepted=False,count_change=0,status_provenance='Terminal lookup after delivered owned contribution completion only; no correctness or foreign liveness lookup.')
a.update(parent_disposition=author_state,contribution='TECHNICAL',contribution_condition='Full correctness of entire unchanged statement AND submitted proof',correctness_condition='UNDISCHARGED',contribution_intake='structural-r220-review-parent/contribution-intake.json',accepted=False,count_change=0)
s=t['current_work_snapshot']
for x in s['structural220_review_dispatches']:
 if x['task_index']==idx:x.update(status='completed',disposition=disposition,intake='structural-r220-review-parent/contribution-intake.json')
s['structural220_contribution_parent_intake']={'task_index':idx,'author_task_index':ai,'disposition':disposition,'correctness_condition':'UNDISCHARGED','intake':'structural-r220-review-parent/contribution-intake.json','count_change':0}
note='Structural220 contribution adopted TECHNICAL conditional on full correctness of the entire unchanged statement AND proof. Correctness remains UNDISCHARGED and its separate review is outstanding. No acceptance or count; 19/20 latestR041 one remains, publicationSTOPPED. All other tasks and foreign records preserved.'
t['last_parent_progress']=note;s.update(observed_utc=now,note=note)
if 'active_task_indices' in s:s['active_task_indices']=[i for i in s['active_task_indices'] if i!=idx]
if 't3_last_polled_running' in s:s['t3_last_polled_running']=[x for x in s['t3_last_polled_running'] if x!=d['taskId']]
changed=[i for i,x in enumerate(old['tasks']) if t['tasks'][i]!=x];assert changed==[ai,idx] and len(t['tasks'])==len(old['tasks'])
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in ['observed_utc','note','active_task_indices','t3_last_polled_running','structural220_review_dispatches'])
assert [x for x in s['structural220_review_dispatches'] if x['task_index']!=idx]==[x for x in old['current_work_snapshot']['structural220_review_dispatches'] if x['task_index']!=idx]
heading='## Structural220 conditional contribution adopted; correctness outstanding';assert heading.encode() not in lr
append='\n'+heading+'\n\nParent read the complete [contribution review](campaigns/2026-10-14/structural-r220-contribution-r1/packet/REVIEW.md), its reading limits and handoff, and adopts **TECHNICAL conditional on full correctness of the entire unchanged frozen statement AND submitted proof**. The compatible reduction covers scalar/matrix remainders, coupling, endpoint calibration, free B, the specified common shear on both branches, exact powers and threshold, every derivative and zero defect. No essential contribution comparison remains unresolved. See [parent assessment](campaigns/2026-10-14/structural-r220-review-parent/contribution-assessment.md).\n\nExplicit-anchor artifact verification matched17 selected files and2 directories. Review originals and the full140-file author baseline remained unchanged; eight tiny copied controls behaved as expected. Logged extents, canonical/primary identities and one exact original-history span were bound without inherited semantic reading. Parent output truncation was recovered, and temporary-fixture permissions were handled only on copies. Scoped primary/history reading, OCR, adjacent exposures, late recovery and exact Lean404 remain disclosed. Artifact checks do not discharge mathematics.\n\n**Full correctness remains UNDISCHARGED.** The separate correctness result is still outstanding and was not polled or inspected in this intake. No repaired/narrowed theorem is substituted; no acceptance or count is added. **19/20, latest R041, one remaining; publication STOPPED.**\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr
(P/'contribution-intake.json').write_text(json.dumps(intake,indent=2)+'\n');tmp=registry.with_suffix('.structural220-contribution.tmp');tmp.write_text(json.dumps(t,indent=2)+'\n');assert registry.read_bytes()==raw;os.replace(tmp,registry)
assert ledger.read_bytes()==lr;ledger.write_bytes(lr+append.encode())
out={'observed_utc':now,'changed_existing_tasks':changed,'new_tasks':0,'all_other_tasks_unchanged':True,'correctness_task_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0,'correctness_condition':'UNDISCHARGED'}
(P/'contribution-adoption-record.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
