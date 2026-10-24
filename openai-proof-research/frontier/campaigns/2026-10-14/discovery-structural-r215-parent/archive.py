#!/usr/bin/env python3
"""Archive the completed owned non-nominee without changing any other task."""
from pathlib import Path
import copy,datetime,hashlib,json,os
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
d=read(P/'task-status.json');r=read(P/'replay.json');owner='164b1204-be68-4540-94bb-0b91055c4381';now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert d['status']=='completed' and not d['hasPendingChildRuns'] and r['originals_bytes_modes_unchanged']
assert d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra' and {e['id']:e['value'] for e in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
registry=C/'tasks.json';ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md';raw=registry.read_bytes();t=json.loads(raw);old=copy.deepcopy(t);lr=ledger.read_bytes()
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
idx=742;e=t['tasks'][idx];assert e['taskId']==d['taskId'] and e['parent_thread']==owner and e['parent_full_intake_pending']
assert sha(PROJECT/e['brief'])==e['brief_sha256']=='a8608cc9f401f7ad37d62be72e48ddc855049218a4468d43aec246502cbe57af'
disposition='ARCHIVED_PREFREEZE_NO_NOMINEE'
intake={'observed_utc':now,'parent_thread':owner,'task_index':idx,'taskId':d['taskId'],'disposition':disposition,'source_index':339,'nominee':False,'frozen_statement':None,'correctness':'NOT_ASSIGNED','contribution':'NOT_ASSIGNED','accepted':False,'count_change':0,'newAccepted':19,'latestAcceptance':'R041','remaining':1,'publication':'STOPPED','anchors':r['anchors'],'assessment_sha256':sha(P/'assessment.md'),'artifact_replay':r,'remaining_obligations':['A geometric lower bound for the corrected second cocycle modulo coboundaries and metric accelerations, with uniform gauge, range and nonlinear control, remains unproved; the alternative all-type quadratic kernel/injectivity route also remains open.'],'formal_coverage':'Exact pinned Lean navigation returned HTTP404; no comparator or formal support claimed.','next':'Distinct discovery family; preserve original derivations and gaps without reopening or renaming.'}
for k in ['status','workState','hasPendingChildRuns','latestTerminalRunId','latestTerminalStatus','latestTerminalSummary','latestTerminalResultContextTransferId','summary','resultContextTransferId','hasPendingQuestion','pendingApproval','waitTimedOut','observed_utc']:e[k]=d[k]
e.update(parent_disposition=disposition,parent_full_intake_pending=False,parent_intake='discovery-structural-r215-parent/intake.json',parent_intake_utc=now,nominee=False,correctness='NOT_ASSIGNED',contribution='NOT_ASSIGNED',accepted=False,count_change=0,status_provenance='Terminal lookup after delivered owned completion only; no foreign liveness lookup.')
s=t['current_work_snapshot'];s['structural215_dispatch'].update(status='completed',disposition=disposition,intake='discovery-structural-r215-parent/intake.json')
s['structural215_parent_intake']={'task_index':idx,'disposition':disposition,'intake':'discovery-structural-r215-parent/intake.json','count_change':0}
note='Structural215 archived PREFREEZE/no nominee. Source integration, quaternionic A-energy estimate, corrected quartic pressure/Riccati formulas and compactness reduction retained; geometric lower bound in the corrected variance quotient remains unproved. No grades or count. Campaign19/20 latestR041 one remains; publicationSTOPPED. Foreign records preserved.'
t['last_parent_progress']=note;s.update(observed_utc=now,note=note)
if 'active_task_indices' in s:s['active_task_indices']=[i for i in s['active_task_indices'] if i!=idx]
if 't3_last_polled_running' in s:s['t3_last_polled_running']=[x for x in s['t3_last_polled_running'] if x!=d['taskId']]
changed=[i for i,x in enumerate(old['tasks']) if t['tasks'][i]!=x];assert changed==[idx] and len(t['tasks'])==len(old['tasks'])
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in ['observed_utc','note','active_task_indices','t3_last_polled_running','structural215_dispatch'])
heading='## Structural215 archived: PREFREEZE / no nominee';assert heading.encode() not in lr
append='\n## Structural215 archived: PREFREEZE / no nominee\n\nParent read and preserves the complete [derivations](campaigns/2026-10-14/fresh-structural-discovery-r215/DERIVATIONS.md): full source integration, quaternionic A-energy calculation, corrected fourth-order pressure formula, second Riccati-variation Green formula and compact-class qualitative reduction. The geometric lower bound modulo coboundaries and allowable metric accelerations remains unproved, as does the alternative all-type kernel/injectivity step. No statement was frozen or old target renamed. See [parent assessment](campaigns/2026-10-14/discovery-structural-r215-parent/assessment.md).\n\nExplicit-anchor verification matched 57 selected files and six subdirectories; all 65 observed files and eight directories remained unchanged. Seven tiny copied controls behaved as expected. All 12 canonical blobs and 11 complete textual read unions were identity-bound. The recovered bibliography truncation, OCR losses, unread antecedents, access failures, accidental cover/footnote exposures and bounded-history limitations remain disclosed. Lean navigation returned404, with no formal support claimed. Private source, primary, history and reading records remain local under original rights. Parent artifact checks neither inherit semantic reading nor certify the deductions.\n\nNo mathematical grade, acceptance or count is assigned. **19/20, latest R041, one remaining; publication STOPPED.** Continue to a distinct family while preserving the sealed packet and exact remaining obligation.\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr
(P/'intake.json').write_text(json.dumps(intake,indent=2)+'\n');tmp=registry.with_suffix('.structural215-archive.tmp');tmp.write_text(json.dumps(t,indent=2)+'\n');assert registry.read_bytes()==raw;os.replace(tmp,registry)
assert ledger.read_bytes()==lr;ledger.write_bytes(lr+append.encode())
out={'observed_utc':now,'changed_existing_tasks':changed,'new_tasks':0,'all_other_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0}
(P/'archive-record.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
