#!/usr/bin/env python3
"""Close the owned unchanged nominee at PASS/TECHNICAL, with zero count."""
from pathlib import Path
import copy,datetime,hashlib,json,os
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
d=read(P/'contribution-task-status.json');r=read(P/'contribution-replay.json');proof=read(P/'proof-intake.json')
owner='164b1204-be68-4540-94bb-0b91055c4381';now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert d['status']=='completed' and d['workState']=='result_available' and not d['hasPendingChildRuns']
assert d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra' and {e['id']:e['value'] for e in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
assert r['review_originals_bytes_modes_unchanged'] and r['whole_author_root_unchanged_since_parent_intake'] and proof['correctness']=='PASS'
registry=C/'tasks.json';ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md';raw=registry.read_bytes();lr=ledger.read_bytes();t=json.loads(raw);old=copy.deepcopy(t)
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
idx=745;e=t['tasks'][idx];author=t['tasks'][743]
assert e['taskId']==d['taskId'] and e['parent_thread']==owner and e['parent_full_intake_pending']
assert sha(PROJECT/e['brief'])==e['brief_sha256']=='2ddff883eb99d584c7fd689c7d0130c557db96e47a340b907386633772289e20'
assert author['parent_thread']==owner and author['correctness']=='PASS'
assert e['statement_sha256']==proof['statement_sha256'] and e['proof_sha256']==proof['proof_sha256']
intake={'observed_utc':now,'parent_thread':owner,'task_index':idx,'taskId':d['taskId'],'author_task_index':743,'scope':'Entire unchanged frozen statement AND submitted AUTHOR-PROOF.md, including auxiliary assertions.','statement_sha256':e['statement_sha256'],'proof_sha256':e['proof_sha256'],'role_correctness':'UNDISCHARGED','role_contribution':'TECHNICAL conditional on full correctness of the entire unchanged statement AND proof','parent_correctness':'PASS','parent_contribution':'TECHNICAL','parent_correctness_condition':'DISCHARGED','condition_basis':'Separate full-scope correctness adoption in proof-intake.json, identical statement/proof hashes.','disposition':'CLOSED_PASS_TECHNICAL','accepted':False,'count_change':0,'newAccepted':19,'latestAcceptance':'R041','remaining':1,'publication':'STOPPED','assessment_sha256':sha(P/'contribution-assessment.md'),'artifact_replay':r,'next':'Distinct discovery family; preserve closed scope and proof without reopening, narrowing, renaming or grade shopping.'}
for k in ['status','workState','hasPendingChildRuns','latestTerminalRunId','latestTerminalStatus','latestTerminalSummary','latestTerminalResultContextTransferId','summary','resultContextTransferId','hasPendingQuestion','pendingApproval','waitTimedOut','observed_utc']:e[k]=d[k]
e.update(parent_disposition='ADOPTED_FULL_SCOPE_TECHNICAL',parent_full_intake_pending=False,parent_intake='structural-r216-review-parent/contribution-intake.json',parent_intake_utc=now,role_correctness='UNDISCHARGED',contribution='TECHNICAL',parent_correctness_condition='DISCHARGED',accepted=False,count_change=0,status_provenance='Terminal lookup after delivered owned contribution completion only; no foreign liveness lookup.')
author.update(contribution='TECHNICAL',contribution_adoption='structural-r216-review-parent/contribution-intake.json',parent_correctness_condition='DISCHARGED',parent_disposition='CLOSED_PASS_TECHNICAL',accepted=False,count_change=0)
s=t['current_work_snapshot']
for x in s['structural216_review_dispatches']:
    if x['task_index']==idx:x.update(status='completed',contribution='TECHNICAL',intake='structural-r216-review-parent/contribution-intake.json')
s['structural216_parent_intake'].update(contribution='TECHNICAL',disposition='CLOSED_PASS_TECHNICAL',contribution_adoption='structural-r216-review-parent/contribution-intake.json',parent_correctness_condition='DISCHARGED')
s['structural216_contribution_adoption']={'task_index':idx,'contribution':'TECHNICAL','scope':'Entire unchanged statement AND proof','correctness_condition':'DISCHARGED at parent level','intake':'structural-r216-review-parent/contribution-intake.json','count_change':0}
s['structural216_closed']={'correctness':'PASS','contribution':'TECHNICAL','scope':'Entire unchanged frozen statement AND submitted proof','correctness_condition':'DISCHARGED','accepted':False,'count_change':0,'remaining':1,'publication':'STOPPED'}
note='Structural216 closed at full unchanged scope: correctness PASS, contribution TECHNICAL; full correctness condition discharged at parent level. Complete compatible hyperbolic-suspension reduction, no substantial residual. Zero acceptance/count. Campaign 19/20, latest R041, one remaining; publication STOPPED. Continue distinct discovery.'
t['last_parent_progress']=note;s.update(observed_utc=now,note=note)
if 'active_task_indices' in s:s['active_task_indices']=[i for i in s['active_task_indices'] if i!=idx]
if 't3_last_polled_running' in s:s['t3_last_polled_running']=[x for x in s['t3_last_polled_running'] if x!=d['taskId']]
changed=[i for i,x in enumerate(old['tasks']) if t['tasks'][i]!=x];assert changed==[743,745] and len(t['tasks'])==len(old['tasks'])
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
allowed=['observed_utc','note','active_task_indices','t3_last_polled_running','structural216_review_dispatches','structural216_parent_intake']
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in allowed)
assert [x for x in s['structural216_review_dispatches'] if x['task_index']!=idx]==[x for x in old['current_work_snapshot']['structural216_review_dispatches'] if x['task_index']!=idx]
heading='## Structural216 closed: full-scope PASS / TECHNICAL';assert heading.encode() not in lr
append='\n'+heading+'\n\nParent read the complete independent [contribution review](campaigns/2026-10-14/structural-r216-contribution-r1/packet/REVIEW.md) and adopts **TECHNICAL** at the entire unchanged frozen statement AND submitted proof. Its condition is discharged at parent level by the separately adopted full-scope correctness PASS on identical hashes; correctness remains UNDISCHARGED in the contribution reviewer role itself. The comparison gives a complete small-coefficient hyperbolic-suspension reduction, reaches the exact submitted endpoint and carries the natural integral coset through all four unmarked images and six pairs on one common base. No essential comparison remains unresolved and no identifiable nonroutine residual survives. See [parent assessment](campaigns/2026-10-14/structural-r216-review-parent/contribution-assessment.md).\n\nArtifact replay matched 31 selected files and five subdirectories, with seven copied controls and all review/author bytes and modes unchanged. Source, primary, extent and render identities were bound without inherited parent semantic reading. The same parent verifier-hash transcription error remains recorded. Reading/access/version/truncation/editorial limits, the unread scanned Waldhausen original and guarded-history omissions remain disclosed. Exact Lean navigation returned404 and supplies no formal support. No priority or exhaustive-clearance claim is adopted.\n\nStructural216 is CLOSED without acceptance or count. Its author and reviews remain immutable; no narrowing, renaming or grade shopping. **19/20, latest R041, one remaining; publication STOPPED.** Continue to a distinct discovery family.\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr
(P/'contribution-intake.json').write_text(json.dumps(intake,indent=2)+'\n');tmp=registry.with_suffix('.structural216-contribution.tmp');tmp.write_text(json.dumps(t,indent=2)+'\n');assert registry.read_bytes()==raw;os.replace(tmp,registry)
assert ledger.read_bytes()==lr;ledger.write_bytes(lr+append.encode())
out={'observed_utc':now,'changed_existing_tasks':changed,'all_other_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0,'correctness_condition_discharged_at_parent':True}
(P/'contribution-adoption-record.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
