#!/usr/bin/env python3
"""Archive delivered Structural205 without a nominee, grade, or count."""
from pathlib import Path
import copy,datetime,hashlib,json,os
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
now=datetime.datetime.now(datetime.timezone.utc).isoformat();owner='164b1204-be68-4540-94bb-0b91055c4381';d=read(P/'task-status.json');r=read(P/'replay.json')
assert d['status']=='completed' and not d['hasPendingChildRuns'] and r['originals_bytes_modes_unchanged']
assert d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra' and {e['id']:e['value'] for e in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
registry=C/'tasks.json';ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md';raw=registry.read_bytes();t=json.loads(raw);old=copy.deepcopy(t);lr=ledger.read_bytes()
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
e=t['tasks'][710];assert e['taskId']==d['taskId'] and e['parent_thread']==owner and e['parent_full_intake_pending']
assert sha(PROJECT/e['brief'])==e['brief_sha256']=='4b79f0ce86ef05e63e91fca55a13f2f78aaceaad153459d012471a2191875ad6'
disposition='ARCHIVED_PREFREEZE_NO_NOMINEE'
intake={'observed_utc':now,'parent_thread':owner,'task_index':710,'taskId':d['taskId'],'disposition':disposition,'source_index':329,'frozen_statement':None,'nominee':False,'correctness':None,'contribution':None,'review_dispatches':[],'accepted':False,'count_change':0,'newAccepted':19,'latestAcceptance':'R041','remaining':1,'publication':'STOPPED','anchors':r['anchors'],'reduction_sha256':r['reduction_sha256'],'derivations_sha256':r['derivations_sha256'],'assessment_sha256':sha(P/'assessment.md'),'open_obligations':['A nonroutine operation beyond the completed source/classical composition','A smaller T-indicator dictionary or encoding with all row separations and uniform signed-approximation constraints, if pursued'],'artifact_replay':{k:r[k] for k in ['verification','selected_directories','root_files','root_directories','originals_bytes_modes_unchanged','canonical_blobs','formal_bindings','primary_pdf_bindings','primary_extent_records','history_exact_spans','direct_input_spans','renders_integrity_only']},'copied_controls_passed':4,'limits':r['limits'],'next':'Distinct discovery only; preserve the prefreeze archive. Add scope.json substring exclusion prospectively; no old rescan. No nominee review or mathematical grade.'}
for k in ['status','workState','hasPendingChildRuns','latestTerminalRunId','latestTerminalStatus','latestTerminalSummary','latestTerminalResultContextTransferId','summary','resultContextTransferId','hasPendingQuestion','pendingApproval','waitTimedOut','observed_utc']:e[k]=d[k]
e.update(parent_disposition=disposition,parent_full_intake_pending=False,parent_intake='discovery-structural-r205-parent/intake.json',parent_intake_utc=now,frozen_statement=None,nominee=False,correctness=None,contribution=None,accepted=False,count_change=0,status_provenance='Terminal lookup after delivered owned completion only; no foreign liveness lookup.')
s=t['current_work_snapshot'];note='Structural205 archived PREFREEZE/no nominee: complete quantitative source/classical reduction and higher-contraction accounting retained; no further nonroutine operation established. No mathematical grades or count. Campaign19/20 latestR041 one remains; publicationSTOPPED. Distinct discovery next; foreign records preserved.'
t['last_parent_progress']=note;s.update(observed_utc=now,note=note)
s['structural205_dispatch'].update(status='completed',disposition=disposition,intake='discovery-structural-r205-parent/intake.json')
s['structural205_parent_intake']={'task_index':710,'disposition':disposition,'intake':'discovery-structural-r205-parent/intake.json','count_change':0}
if 'active_task_indices' in s:s['active_task_indices']=[i for i in s['active_task_indices'] if i!=710]
if 't3_last_polled_running' in s:s['t3_last_polled_running']=[x for x in s['t3_last_polled_running'] if x!=d['taskId']]
changed=[i for i,e in enumerate(old['tasks']) if t['tasks'][i]!=e];assert changed==[710] and len(t['tasks'])==len(old['tasks'])
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in ['observed_utc','note','structural205_dispatch','active_task_indices','t3_last_polled_running'])
heading='## Structural205 archived: PREFREEZE / no nominee'
assert heading.encode() not in lr
append='\n'+heading+'\n\nParent read and archived the complete [reduction](campaigns/2026-10-14/fresh-structural-discovery-r205/reduction.md), early derivations and [handoff](campaigns/2026-10-14/fresh-structural-discovery-r205/FINAL.md). The quantitative dimension bound n <= exp(C_a b^(2h) log(2+b)), h=ceil(3^(1000a)), is retained with its exact finite formula, affine zero-pattern and empirical-approximation dependencies, common-kernel saturation proof, and full higher-contraction accounting. No further nonroutine operation was established; a smaller T-indicator encoding would still need every simultaneous separation and uniform signed-approximation constraint. No theorem was frozen or nominated and no correctness/contribution grade or review is assigned. See [parent assessment](campaigns/2026-10-14/discovery-structural-r205-parent/assessment.md).\n\nRead-only verification matched 72 selected files/seven directory modes and four copied controls; all 94 observed files/12 directories remained unchanged. All11canonical and two formal bindings matched. Primary version/access, scoped original-history, reconstructed navigation record, metadata false admission and sorry comparator limits remain disclosed. Add scope.json to future full-path substring guards without rerunning an old scan. Artifact identity is not semantic reading or a mathematical grade.\n\nPreserve this archive and continue only to a distinct discovery. **19/20, latest R041, one remaining; zero acceptance/count added; publication STOPPED.**\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr
(P/'intake.json').write_text(json.dumps(intake,indent=2)+'\n')
tmp=registry.with_suffix('.structural205-archive.tmp');tmp.write_text(json.dumps(t,indent=2)+'\n');assert registry.read_bytes()==raw;os.replace(tmp,registry)
assert ledger.read_bytes()==lr;ledger.write_bytes(lr+append.encode())
out={'observed_utc':now,'changed_existing_tasks':changed,'new_tasks':0,'all_other_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0}
(P/'archive-record.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
