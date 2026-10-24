#!/usr/bin/env python3
"""Integrate the owned full nominee without grading it or changing other tasks."""
from pathlib import Path
import copy, datetime, hashlib, json, os
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
d=read(P/'task-status.json');r=read(P/'replay.json');owner='164b1204-be68-4540-94bb-0b91055c4381';now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert d['status']=='completed' and not d['hasPendingChildRuns'] and r['originals_bytes_modes_unchanged']
registry=C/'tasks.json';ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md';raw=registry.read_bytes();t=json.loads(raw);old=copy.deepcopy(t);lr=ledger.read_bytes()
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
idx=751;e=t['tasks'][idx];assert e['taskId']==d['taskId'] and e['parent_thread']==owner and e['parent_full_intake_pending']
assert sha(PROJECT/e['brief'])==e['brief_sha256']=='2367f3b36de032b123ba9b76d0442ea2dc59598fa29475ea188c2302fc5e30b1'
disposition='AWAITING_INDEPENDENT_REVIEWS'
intake={'observed_utc':now,'parent_thread':owner,'task_index':idx,'taskId':d['taskId'],'disposition':disposition,'source_index':344,'nominee':True,'frozen_statement':'fresh-structural-discovery-r220/packet/STATEMENT.md','statement_sha256':r['statement_sha256'],'proof_sha256':r['proof_sha256'],'correctness':'NOT_ASSIGNED','contribution':'NOT_ASSIGNED','accepted':False,'count_change':0,'newAccepted':19,'latestAcceptance':'R041','remaining':1,'publication':'STOPPED','anchors':r['anchors'],'assessment_sha256':sha(P/'assessment.md'),'artifact_replay':r,'remaining_obligations':['Independent adversarial correctness review of the entire unchanged statement AND proof.','Separate contribution review conditional on full correctness, carrying the strongest compatible construction through the full unchanged scope.'],'formal_coverage':r['formal_navigation'],'next':'Two fresh independent round-one reviews; no nominee mutation or downstream work.'}
for k in ['status','workState','hasPendingChildRuns','latestTerminalRunId','latestTerminalStatus','latestTerminalSummary','latestTerminalResultContextTransferId','summary','resultContextTransferId','hasPendingQuestion','pendingApproval','waitTimedOut']:e[k]=d[k]
e.update(parent_disposition=disposition,parent_full_intake_pending=False,parent_intake='discovery-structural-r220-parent/intake.json',parent_intake_utc=now,nominee=True,correctness='NOT_ASSIGNED',contribution='NOT_ASSIGNED',accepted=False,count_change=0,status_provenance='Terminal lookup after delivered owned completion only; no foreign liveness lookup.')
s=t['current_work_snapshot'];s['structural220_dispatch'].update(status='completed',disposition=disposition,intake='discovery-structural-r220-parent/intake.json')
s['structural220_parent_intake']={'task_index':idx,'disposition':disposition,'intake':'discovery-structural-r220-parent/intake.json','count_change':0}
note='Structural220 full nominee received: quantitative Lagrangian-chart rigidity with exact cut pairs, a free middle residue and one common shear on both branches. Sealed packet verified; independent correctness and contribution reviews pending. No grades or count. Campaign 19/20, latest R041, one remaining; publication STOPPED.'
t['last_parent_progress']=note;s.update(observed_utc=now,note=note)
if 'active_task_indices' in s:s['active_task_indices']=[i for i in s['active_task_indices'] if i!=idx]
if 't3_last_polled_running' in s:s['t3_last_polled_running']=[x for x in s['t3_last_polled_running'] if x!=d['taskId']]
changed=[i for i,x in enumerate(old['tasks']) if t['tasks'][i]!=x];assert changed==[idx] and len(t['tasks'])==len(old['tasks'])
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in ['observed_utc','note','active_task_indices','t3_last_polled_running','structural220_dispatch'])
heading='## Structural220 full nominee: independent reviews pending';assert heading.encode() not in lr
append='\n## Structural220 full nominee: independent reviews pending\n\nParent read the entire unchanged [statement](campaigns/2026-10-14/fresh-structural-discovery-r220/packet/STATEMENT.md) and [author proof](campaigns/2026-10-14/fresh-structural-discovery-r220/packet/PROOF.md): under exact cut pairs and uniform chart hypotheses, the integrated determinant defect controls both branches after the same specified constant shear, including the initially free middle residue and every derivative in the frozen range. No near-Blaschke metric stability is claimed. See [parent assessment](campaigns/2026-10-14/discovery-structural-r220-parent/assessment.md).\n\nExplicit-anchor artifact replay matched66 selected files and8 directories including the packet root; all140 observed files and17 directories remained unchanged. Eight tiny copied controls behaved as expected. Canonical, primary and logged extent identities were bound without inherited semantic reading. A parent duplicate-path assumption was corrected for code/guard copies; no original mutation or artifact mismatch occurred. Reading/OCR/crop, late comparison, access and accidental-exposure limits remain disclosed. No original-history mathematical body was selected, and exact Lean navigation returned404. Protected bodies and private inventories remain local.\n\nFresh separate correctness and contribution reviews will assess the entire unchanged frozen statement AND submitted proof. No grade, acceptance or count is assigned. **19/20, latest R041, one remaining; publication STOPPED.**\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr
(P/'intake.json').write_text(json.dumps(intake,indent=2)+'\n');tmp=registry.with_suffix('.structural220-intake.tmp');tmp.write_text(json.dumps(t,indent=2)+'\n');assert registry.read_bytes()==raw;os.replace(tmp,registry)
assert ledger.read_bytes()==lr;ledger.write_bytes(lr+append.encode())
out={'observed_utc':now,'changed_existing_tasks':changed,'new_tasks':0,'all_other_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0}
(P/'intake-record.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
