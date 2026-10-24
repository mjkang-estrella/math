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
idx=739;e=t['tasks'][idx];assert e['taskId']==d['taskId'] and e['parent_thread']==owner and e['parent_full_intake_pending']
assert sha(PROJECT/e['brief'])==e['brief_sha256']=='23b7667ac241316258cbdba1363af9411c93972e6951fa67445984d4cc2573e3'
disposition='ARCHIVED_PREFREEZE_NO_NOMINEE'
intake={'observed_utc':now,'parent_thread':owner,'task_index':idx,'taskId':d['taskId'],'disposition':disposition,'source_index':338,'nominee':False,'frozen_statement':None,'correctness':'NOT_ASSIGNED','contribution':'NOT_ASSIGNED','accepted':False,'count_change':0,'newAccepted':19,'latestAcceptance':'R041','remaining':1,'publication':'STOPPED','anchors':r['anchors'],'assessment_sha256':sha(P/'assessment.md'),'artifact_replay':r,'remaining_obligations':['General compact-group equivariant global models and assembly under full Source338 hypotheses remain unproved, including compatible jets and forward/inverse exhaustion in the variable clock.'],'formal_coverage':'Exact pinned Lean navigation returned HTTP404; no comparator or formal support claimed.','next':'Distinct discovery family; preserve original derivations and gaps without reopening or renaming.'}
for k in ['status','workState','hasPendingChildRuns','latestTerminalRunId','latestTerminalStatus','latestTerminalSummary','latestTerminalResultContextTransferId','summary','resultContextTransferId','hasPendingQuestion','pendingApproval','waitTimedOut','observed_utc']:e[k]=d[k]
e.update(parent_disposition=disposition,parent_full_intake_pending=False,parent_intake='discovery-structural-r214-parent/intake.json',parent_intake_utc=now,nominee=False,correctness='NOT_ASSIGNED',contribution='NOT_ASSIGNED',accepted=False,count_change=0,status_provenance='Terminal lookup after delivered owned completion only; no foreign liveness lookup.')
s=t['current_work_snapshot'];s['structural214_dispatch'].update(status='completed',disposition=disposition,intake='discovery-structural-r214-parent/intake.json')
s['structural214_parent_intake']={'task_index':idx,'disposition':disposition,'intake':'discovery-structural-r214-parent/intake.json','count_change':0}
note='Structural214 archived PREFREEZE/no nominee. Invariant charts, repaired two-weight models and full classical comparisons retained; general compact-group equivariant assembly under full source hypotheses remains unproved. No grades or count. Campaign19/20 latestR041 one remains; publicationSTOPPED. Foreign records preserved.'
t['last_parent_progress']=note;s.update(observed_utc=now,note=note)
if 'active_task_indices' in s:s['active_task_indices']=[i for i in s['active_task_indices'] if i!=idx]
if 't3_last_polled_running' in s:s['t3_last_polled_running']=[x for x in s['t3_last_polled_running'] if x!=d['taskId']]
changed=[i for i,x in enumerate(old['tasks']) if t['tasks'][i]!=x];assert changed==[idx] and len(t['tasks'])==len(old['tasks'])
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in ['observed_utc','note','active_task_indices','t3_last_polled_running','structural214_dispatch'])
heading='## Structural214 archived: PREFREEZE / no nominee';assert heading.encode() not in lr
append='\n## Structural214 archived: PREFREEZE / no nominee\n\nParent read and preserves the complete [integrated symmetry derivations](campaigns/2026-10-14/fresh-structural-discovery-r214/INTEGRATED-DERIVATIONS.md): invariant approximations, common fixed point and equivariant charts, repaired two-weight entire models, inverse bounds and exhaustion. The actual Forstnerič, Suzuki and full Chau–Tam comparisons absorb the completed cases. No statement was frozen. General compact-group equivariant construction under the full source hypotheses remains unproved. See [parent assessment](campaigns/2026-10-14/discovery-structural-r214-parent/assessment.md).\n\nExplicit-anchor verification matched 94 selected files and five subdirectories; all 105 observed files and nine directories remained unchanged. Seven tiny copied controls behaved as expected. All 14 canonical blobs and recorded 13 textual read unions were identity-bound. Four disclosed boundary-overread types, late and selective primary reading, access failures, formula limits and a bibliographic metadata discrepancy remain recorded. No eligible history section was admitted; this is not clearance. Lean navigation returned404 and no formal support is claimed. Parent artifact checks do not inherit source/primary semantics or certify the deductions.\n\nNo mathematical grade, acceptance or count is assigned. **19/20, latest R041, one remaining; publication STOPPED.** Continue to a distinct family while preserving this sealed packet and the general equivariance obligation.\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr
(P/'intake.json').write_text(json.dumps(intake,indent=2)+'\n');tmp=registry.with_suffix('.structural214-archive.tmp');tmp.write_text(json.dumps(t,indent=2)+'\n');assert registry.read_bytes()==raw;os.replace(tmp,registry)
assert ledger.read_bytes()==lr;ledger.write_bytes(lr+append.encode())
out={'observed_utc':now,'changed_existing_tasks':changed,'new_tasks':0,'all_other_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0}
(P/'archive-record.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
