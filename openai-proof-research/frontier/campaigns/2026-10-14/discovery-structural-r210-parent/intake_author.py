#!/usr/bin/env python3
"""Record the immutable author nominee, leaving both independent grades pending."""
from pathlib import Path
import copy,datetime,hashlib,json,os
P=Path(__file__).resolve().parent; C=P.parent; PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes()); sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
d=read(P/'task-status.json'); r=read(P/'replay.json'); now=datetime.datetime.now(datetime.timezone.utc).isoformat(); owner='164b1204-be68-4540-94bb-0b91055c4381'
assert d['status']=='completed' and not d['hasPendingChildRuns'] and r['originals_bytes_modes_unchanged']
assert d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra' and {e['id']:e['value'] for e in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
registry=C/'tasks.json'; ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md'; raw=registry.read_bytes(); lr=ledger.read_bytes(); t=json.loads(raw); old=copy.deepcopy(t)
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
idx=727; e=t['tasks'][idx]; assert e['taskId']==d['taskId'] and e['parent_thread']==owner and e['parent_full_intake_pending']
assert sha(PROJECT/e['brief'])==e['brief_sha256']=='3242d7cd49cbd9c313ca054d86deb35172df016d48ef6f1bcdb657dfe1f8012b'
disposition='AUTHOR_NOMINEE_INDEPENDENT_REVIEWS_PENDING'
intake={'observed_utc':now,'parent_thread':owner,'task_index':idx,'taskId':d['taskId'],'disposition':disposition,'source_index':334,'nominee':True,'frozen_statement':'fresh-structural-discovery-r210/packet/FROZEN-STATEMENT.md','frozen_sha256':r['frozen_sha256'],'proof':'fresh-structural-discovery-r210/packet/AUTHOR-PROOF.md','proof_sha256':r['proof_sha256'],'correctness':'PENDING','contribution':'PENDING','review_dispatches':[],'accepted':False,'count_change':0,'newAccepted':19,'latestAcceptance':'R041','remaining':1,'publication':'STOPPED','anchors':r['anchors'],'assessment_sha256':sha(P/'assessment.md'),'artifact_replay':r,'next':'Separate independent correctness and contribution reviews of the entire unchanged statement and submitted proof; no grades adopted.'}
for k in ['status','workState','hasPendingChildRuns','latestTerminalRunId','latestTerminalStatus','latestTerminalSummary','latestTerminalResultContextTransferId','summary','resultContextTransferId','hasPendingQuestion','pendingApproval','waitTimedOut','observed_utc']:e[k]=d[k]
e.update(parent_disposition=disposition,parent_full_intake_pending=False,parent_intake='discovery-structural-r210-parent/intake.json',parent_intake_utc=now,nominee=True,frozen_statement=intake['frozen_statement'],frozen_sha256=r['frozen_sha256'],proof_sha256=r['proof_sha256'],correctness='PENDING',contribution='PENDING',review_dispatches=[],accepted=False,count_change=0,status_provenance='Terminal lookup after delivered owned completion only; no foreign liveness lookup.')
s=t['current_work_snapshot']; s['structural210_dispatch'].update(status='completed',disposition=disposition,intake='discovery-structural-r210-parent/intake.json')
s['structural210_parent_intake']={'task_index':idx,'disposition':disposition,'intake':'discovery-structural-r210-parent/intake.json','frozen_sha256':r['frozen_sha256'],'count_change':0}
note='Structural210 exact smooth nonimmersion-locus author nominee admitted unchanged for separate correctness and contribution reviews. No grades, acceptance or count. Campaign 19/20, latest R041, one remains; publication STOPPED. Other task records preserved.'
t['last_parent_progress']=note; s.update(observed_utc=now,note=note)
if 'active_task_indices' in s:s['active_task_indices']=[i for i in s['active_task_indices'] if i!=idx]
if 't3_last_polled_running' in s:s['t3_last_polled_running']=[x for x in s['t3_last_polled_running'] if x!=d['taskId']]
changed=[i for i,x in enumerate(old['tasks']) if t['tasks'][i]!=x]; assert changed==[idx] and len(t['tasks'])==len(old['tasks'])
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in ['observed_utc','note','active_task_indices','t3_last_polled_running','structural210_dispatch'])
heading='## Structural210 author nominee: exact smooth local nonimmersion loci'; assert heading.encode() not in lr
append='\n'+heading+'\n\nThe parent read the complete [frozen statement](campaigns/2026-10-14/fresh-structural-discovery-r210/packet/FROZEN-STATEMENT.md) and [author proof](campaigns/2026-10-14/fresh-structural-discovery-r210/packet/AUTHOR-PROOF.md), admitting the exact-locus nominee unchanged for separate independent reviews. The scope includes both classification directions, uniform metric bounds, flat curvature jets on the prescribed set, regular zeros off it, and the conditional Euclidean metric jet at the origin. See [parent intake assessment](campaigns/2026-10-14/discovery-structural-r210-parent/assessment.md).\n\nThe proposed finite bounded-class capture and independent interior-mass/boundary-slope choices require full correctness and contribution comparison against the paid source, primary and eligible original-history operations. No finite-regularity conclusion is claimed. Read-only artifact verification matched 87 selected files and ten directories; all 186 observed root files and modes remained unchanged. Seven tiny copied controls behaved as expected. Underlying source/primary/history/comparator bodies and renders were identity-bound only by parent; reading and version limits remain explicit, and the comparator supplies no endpoint proof.\n\nBoth independent grades remain **PENDING**. No acceptance or count. **19/20, latest R041, one remaining; publication STOPPED.**\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr
(P/'intake.json').write_text(json.dumps(intake,indent=2)+'\n'); tmp=registry.with_suffix('.structural210-intake.tmp'); tmp.write_text(json.dumps(t,indent=2)+'\n'); assert registry.read_bytes()==raw; os.replace(tmp,registry)
assert ledger.read_bytes()==lr; ledger.write_bytes(lr+append.encode())
out={'observed_utc':now,'changed_existing_tasks':changed,'new_tasks':0,'all_other_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0}; (P/'intake-record.json').write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps(out,indent=2))
