#!/usr/bin/env python3
"""Archive only the completed owned non-nominee, preserving concurrent records."""
from pathlib import Path
import copy,datetime,hashlib,json,os
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
d=read(P/'task-status.json');r=read(P/'replay.json');now=datetime.datetime.now(datetime.timezone.utc).isoformat()
owner='164b1204-be68-4540-94bb-0b91055c4381';idx=750
assert d['status']=='completed' and not d['hasPendingChildRuns'] and r['originals_bytes_modes_unchanged']
assert d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra'
assert {e['id']:e['value'] for e in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
registry=C/'tasks.json';ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md'
raw=registry.read_bytes();t=json.loads(raw);old=copy.deepcopy(t);lr=ledger.read_bytes()
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
e=t['tasks'][idx];assert e['taskId']==d['taskId'] and e['parent_thread']==owner and e['parent_full_intake_pending']
assert sha(PROJECT/e['brief'])==e['brief_sha256']=='c4858c36b0eb3d621ceea905a50992c49e5d25cb5d629cb8af6ab3fcd3954616'
disposition='ARCHIVED_PREFREEZE_NO_NOMINEE'
intake={'observed_utc':now,'parent_thread':owner,'task_index':idx,'taskId':d['taskId'],'disposition':disposition,'source_index':343,'nominee':False,'frozen_statement':None,'correctness':'NOT_ASSIGNED','contribution':'NOT_ASSIGNED','accepted':False,'count_change':0,'newAccepted':19,'latestAcceptance':'R041','remaining':1,'publication':'STOPPED','anchors':r['anchors'],'assessment_sha256':sha(P/'assessment.md'),'artifact_replay':r,'remaining_obligations':['No distinct substantial operation beyond finite source packing, elementary carrier scheduling and classical blowup/homology composition was identified.','Global parametric sections, arbitrary fixed-prefix extension, new fixed-capacity isotopy and effective optimal derivative estimates were not obtained.'],'formal_coverage':'Author reports both indicated Lean comparator endpoints contain sorry; parent bound identities only and claims no completed formal support.','next':'Distinct discovery family; retain original derivations and limitations without reopening or renaming.'}
for k in ['status','workState','hasPendingChildRuns','latestTerminalRunId','latestTerminalStatus','latestTerminalSummary','latestTerminalResultContextTransferId','summary','resultContextTransferId','hasPendingQuestion','pendingApproval','waitTimedOut']:e[k]=d[k]
e.update(observed_utc=now,parent_disposition=disposition,parent_full_intake_pending=False,parent_intake='discovery-structural-r219-parent/intake.json',parent_intake_utc=now,nominee=False,correctness='NOT_ASSIGNED',contribution='NOT_ASSIGNED',accepted=False,count_change=0,status_provenance='Terminal lookup after delivered owned completion only; no foreign liveness lookup.')
s=t['current_work_snapshot'];s['structural219_dispatch'].update(status='completed',disposition=disposition,intake='discovery-structural-r219-parent/intake.json')
s['structural219_parent_intake']={'task_index':idx,'disposition':disposition,'intake':'discovery-structural-r219-parent/intake.json','count_change':0}
note='Structural219 archived PREFREEZE/no nominee. Proper countable packing with prescribed boundary accumulation, positive-collar volume obstruction and locally finite blowup consequences retained; no distinct substantial operation beyond compatible source/classical composition. No grades or count. Campaign19/20 latestR041 one remains; publicationSTOPPED. Foreign records preserved.'
t['last_parent_progress']=note;s.update(observed_utc=now,note=note)
if 'active_task_indices' in s:s['active_task_indices']=[i for i in s['active_task_indices'] if i!=idx]
if 't3_last_polled_running' in s:s['t3_last_polled_running']=[x for x in s['t3_last_polled_running'] if x!=d['taskId']]
changed=[i for i,x in enumerate(old['tasks']) if t['tasks'][i]!=x];assert changed==[idx] and len(t['tasks'])==len(old['tasks'])
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in ['observed_utc','note','active_task_indices','t3_last_polled_running','structural219_dispatch'])
heading='## Structural219 archived: PREFREEZE / no nominee';assert heading.encode() not in lr
append='\n'+heading+'\n\nParent read and preserves the complete [derivations](campaigns/2026-10-14/fresh-structural-discovery-r219/packet/DERIVATIONS.md): finite-carrier scheduling yields proper countable packings with any prescribed nonempty closed boundary accumulation set; disjoint collars force strict volume; locally finite blowups give the stated volume and direct-sum homology. No distinct substantial operation was established beyond the stipulated finite source theorem and elementary/classical composition. No theorem was frozen or old target renamed. See [parent assessment](campaigns/2026-10-14/discovery-structural-r219-parent/assessment.md).\n\nExplicit-anchor verification matched 57 selected files and 10 subdirectories; all 67 observed files and 14 directories remained unchanged. Eight tiny copied controls behaved as expected. Canonical, formal, primary and exact read identities were bound without inherited semantic coverage. Primary intermediates, OCR/crop limits, accidental exposures, later reading and bounded history remain disclosed. Lerman access returned403; the indicated Lean endpoints contain sorry according to the author report, with no completed formal support claimed. Private records remain local under original rights. Artifact checks do not certify mathematical deductions.\n\nNo mathematical grade, acceptance or count is assigned. **19/20, latest R041, one remaining; publication STOPPED.** Continue to a distinct family while preserving the sealed packet.\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr
(P/'intake.json').write_text(json.dumps(intake,indent=2)+'\n')
tmp=registry.with_suffix('.structural219-archive.tmp');tmp.write_text(json.dumps(t,indent=2)+'\n');assert registry.read_bytes()==raw;os.replace(tmp,registry)
assert ledger.read_bytes()==lr;ledger.write_bytes(lr+append.encode())
out={'observed_utc':now,'changed_existing_tasks':changed,'new_tasks':0,'all_other_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0}
(P/'archive-record.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
