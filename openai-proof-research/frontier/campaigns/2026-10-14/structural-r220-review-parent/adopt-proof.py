#!/usr/bin/env python3
"""Adopt full correctness and discharge the already-adopted contribution condition."""
from pathlib import Path
import copy,datetime,hashlib,json,os
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
d=read(P/'proof-task-status.json');r=read(P/'proof-replay.json');ci=read(P/'contribution-intake.json');owner='164b1204-be68-4540-94bb-0b91055c4381';now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert d['status']=='completed' and not d['hasPendingChildRuns'] and r['review_originals_bytes_modes_unchanged'] and r['all_author_baseline_bytes_modes_unchanged']
assert d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra' and {x['id']:x['value'] for x in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
registry=C/'tasks.json';ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md';raw=registry.read_bytes();lr=ledger.read_bytes();t=json.loads(raw);old=copy.deepcopy(t)
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
ai,pi,co=751,752,753;a,e,c=(t['tasks'][i] for i in [ai,pi,co])
assert e['taskId']==d['taskId'] and e['parent_thread']==owner and e['parent_full_intake_pending'] and e['role']=='correctness'
assert a['parent_thread']==owner and a['parent_disposition']=='AWAITING_CORRECTNESS_CONDITIONAL_TECHNICAL'
assert c['parent_disposition']=='ADOPTED_CONDITIONAL_TECHNICAL' and ci['contribution']=='TECHNICAL' and ci['correctness_condition']=='UNDISCHARGED'
assert sha(PROJECT/e['brief'])==e['brief_sha256']=='e0bed40cd1fb61a36f8e7025694ead14ecb40ca5cd23d31cb7b6393c5ca6ed44'
ar=read(C/'discovery-structural-r220-parent/replay.json');A=C/'fresh-structural-discovery-r220/packet'
assert sha(A/'STATEMENT.md')==ar['statement_sha256']==e['statement_sha256']==ci['statement_sha256'] and sha(A/'PROOF.md')==ar['proof_sha256']==e['proof_sha256']==ci['proof_sha256']
disposition='ADOPTED_FULL_SCOPE_PASS';closed='CLOSED_PASS_TECHNICAL'
intake={'observed_utc':now,'parent_thread':owner,'task_index':pi,'author_task_index':ai,'contribution_task_index':co,'taskId':d['taskId'],'disposition':disposition,'author_disposition':closed,'scope':'Entire unchanged frozen statement AND submitted proof','statement_sha256':ar['statement_sha256'],'proof_sha256':ar['proof_sha256'],'correctness':'PASS','contribution':'TECHNICAL','correctness_condition':'DISCHARGED','contribution_condition_discharged_by':'Independent full-scope correctness PASS adopted in this intake','accepted':False,'count_change':0,'newAccepted':19,'latestAcceptance':'R041','remaining':1,'publication':'STOPPED','anchors':r['anchors'],'assessment_sha256':sha(P/'proof-assessment.md'),'artifact_replay':r,'contribution_intake':'structural-r220-review-parent/contribution-intake.json','scope_qualification':'The exact cut-pair and exterior pole assumptions already force B=I for every admissible chart. The submitted weaker estimate is valid; no independent B!=I variation claim is established.','unresolved_correctness_obligations':[],'next':'Distinct discovery family; no reopening, narrowing, renaming, author mutation or count.'}
for k in ['status','workState','hasPendingChildRuns','latestTerminalRunId','latestTerminalStatus','latestTerminalSummary','latestTerminalResultContextTransferId','summary','resultContextTransferId','hasPendingQuestion','pendingApproval','waitTimedOut']:e[k]=d[k]
e.update(observed_utc=now,parent_disposition=disposition,parent_full_intake_pending=False,parent_intake='structural-r220-review-parent/proof-intake.json',parent_intake_utc=now,correctness='PASS',accepted=False,count_change=0,status_provenance='Terminal lookup after delivered owned correctness completion only; no foreign liveness lookup.')
a.update(parent_disposition=closed,correctness='PASS',contribution='TECHNICAL',correctness_condition='DISCHARGED',contribution_condition='DISCHARGED by independent full-scope correctness PASS',proof_intake='structural-r220-review-parent/proof-intake.json',closed_utc=now,accepted=False,count_change=0)
c.update(parent_disposition='ADOPTED_TECHNICAL_CONDITION_DISCHARGED',parent_correctness_condition='DISCHARGED',contribution_condition_discharged=True,condition_discharge_intake='structural-r220-review-parent/proof-intake.json')
s=t['current_work_snapshot']
for x in s['structural220_review_dispatches']:
 if x['task_index']==pi:x.update(status='completed',disposition=disposition,intake='structural-r220-review-parent/proof-intake.json')
 elif x['task_index']==co:x.update(disposition=c['parent_disposition'],parent_correctness_condition='DISCHARGED')
s['structural220_contribution_parent_intake']['correctness_condition']='DISCHARGED_AT_PARENT'
s['structural220_proof_parent_intake']={'task_index':pi,'author_task_index':ai,'disposition':disposition,'author_disposition':closed,'correctness_condition':'DISCHARGED','intake':'structural-r220-review-parent/proof-intake.json','count_change':0}
note='Structural220 CLOSED full-scope PASS/TECHNICAL; full correctness condition discharged at parent level. Exact cut/exterior assumptions force B=I; the submitted weaker estimate remains valid and no independent B variation is established. Zero acceptance/count; 19/20 latestR041 one remains, publicationSTOPPED. Continue a distinct family.'
t['last_parent_progress']=note;s.update(observed_utc=now,note=note)
if 'active_task_indices' in s:s['active_task_indices']=[i for i in s['active_task_indices'] if i!=pi]
if 't3_last_polled_running' in s:s['t3_last_polled_running']=[x for x in s['t3_last_polled_running'] if x!=d['taskId']]
changed=[i for i,x in enumerate(old['tasks']) if t['tasks'][i]!=x];assert changed==[ai,pi,co] and len(t['tasks'])==len(old['tasks'])
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in ['observed_utc','note','active_task_indices','t3_last_polled_running','structural220_review_dispatches','structural220_contribution_parent_intake'])
heading='## Structural220 closed: full-scope PASS / TECHNICAL';assert heading.encode() not in lr
append='\n'+heading+'\n\nParent adopts the independent [correctness PASS](campaigns/2026-10-14/structural-r220-proof-r1/packet/REVIEW.md) for the entire unchanged frozen statement AND submitted proof. No essential repair or unresolved correctness obligation remains. This discharges the condition of the previously adopted TECHNICAL contribution review; Structural220 closes with zero acceptance/count. See [parent assessment](campaigns/2026-10-14/structural-r220-review-parent/proof-assessment.md).\n\nThe exact cut-pair/exterior assumptions already force B=I, for all defects: Q(u,u+D)=(I-B)/u+O(1)=0. The weaker submitted residue estimate remains valid; independently varying B is not established or required by the theorem. The scalar-normalization shorthand is resolved with the cited chord factor kept outside its double integral. Neither point requires changing frozen bytes.\n\nExplicit-anchor artifact replay matched18 selected files and2 directories. Review originals and the140-file author baseline remained unchanged; eight tiny copied controls behaved as expected. LF extent, canonical and primary identities were bound without inherited semantic reading. Scoped source/primary reading, OCR/visual limits, wrapper/bibliography exposure and exact Lean404 remain disclosed. No formal support or exhaustive priority clearance is claimed.\n\nThe entire unchanged scope is **CLOSED PASS/TECHNICAL**, with full correctness condition discharged at parent level. No acceptance or count is added. **19/20, latest R041, one remaining; publication STOPPED.** Continue to a distinct source family without reopening, narrowing or renaming this target.\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr
(P/'proof-intake.json').write_text(json.dumps(intake,indent=2)+'\n');tmp=registry.with_suffix('.structural220-proof.tmp');tmp.write_text(json.dumps(t,indent=2)+'\n');assert registry.read_bytes()==raw;os.replace(tmp,registry)
assert ledger.read_bytes()==lr;ledger.write_bytes(lr+append.encode())
out={'observed_utc':now,'changed_existing_tasks':changed,'new_tasks':0,'all_other_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0,'correctness_condition':'DISCHARGED','author_disposition':closed}
(P/'proof-adoption-record.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
