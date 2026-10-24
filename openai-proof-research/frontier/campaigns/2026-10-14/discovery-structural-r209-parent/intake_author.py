#!/usr/bin/env python3
"""Record an unchanged author nominee; independent mathematical grades stay pending."""
from pathlib import Path
import copy,datetime,hashlib,json,os
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
d=read(P/'task-status.json');r=read(P/'replay.json');owner='164b1204-be68-4540-94bb-0b91055c4381';now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert d['status']=='completed' and not d['hasPendingChildRuns'] and r['originals_bytes_modes_unchanged']
assert d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra' and {e['id']:e['value'] for e in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
registry=C/'tasks.json';ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md';raw=registry.read_bytes();t=json.loads(raw);old=copy.deepcopy(t);lr=ledger.read_bytes()
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
idx=721;e=t['tasks'][idx];assert e['taskId']==d['taskId'] and e['parent_thread']==owner and e['parent_full_intake_pending']
assert sha(PROJECT/e['brief'])==e['brief_sha256']=='32fc534bf6d36769bccd05eb15f5769b4b3d5898a50f906614b8056cca6fa930'
disposition='AUTHOR_NOMINEE_INDEPENDENT_REVIEWS_PENDING'
intake={'observed_utc':now,'parent_thread':owner,'task_index':idx,'taskId':d['taskId'],'disposition':disposition,'source_index':333,'nominee':True,'frozen_statement':'fresh-structural-discovery-r209/FROZEN-STATEMENT.md','frozen_sha256':r['frozen_sha256'],'proof':'fresh-structural-discovery-r209/AUTHOR-PROOF.md','proof_sha256':r['proof_sha256'],'correctness':'PENDING','contribution':'PENDING','review_dispatches':[],'accepted':False,'count_change':0,'newAccepted':19,'latestAcceptance':'R041','remaining':1,'publication':'STOPPED','anchors':r['anchors'],'assessment_sha256':sha(P/'assessment.md'),'artifact_replay':r,'next':'Separate independent correctness and contribution reviews of the entire unchanged statement and submitted proof; no grades adopted.'}
for k in ['status','workState','hasPendingChildRuns','latestTerminalRunId','latestTerminalStatus','latestTerminalSummary','latestTerminalResultContextTransferId','summary','resultContextTransferId','hasPendingQuestion','pendingApproval','waitTimedOut','observed_utc']:e[k]=d[k]
e.update(parent_disposition=disposition,parent_full_intake_pending=False,parent_intake='discovery-structural-r209-parent/intake.json',parent_intake_utc=now,nominee=True,frozen_statement=intake['frozen_statement'],frozen_sha256=r['frozen_sha256'],proof_sha256=r['proof_sha256'],correctness='PENDING',contribution='PENDING',review_dispatches=[],accepted=False,count_change=0,status_provenance='Terminal lookup after delivered owned completion only; no foreign liveness lookup.')
s=t['current_work_snapshot'];s['structural209_dispatch'].update(status='completed',disposition=disposition,intake='discovery-structural-r209-parent/intake.json')
s['structural209_parent_intake']={'task_index':idx,'disposition':disposition,'intake':'discovery-structural-r209-parent/intake.json','frozen_sha256':r['frozen_sha256'],'count_change':0}
note='Structural209 full author-proof nominee T333Q209 admitted unchanged for separate correctness and contribution reviews. No grades, acceptance or count. Campaign19/20 latestR041 one remains; publicationSTOPPED. Foreign records preserved.'
t['last_parent_progress']=note;s.update(observed_utc=now,note=note)
if 'active_task_indices' in s:s['active_task_indices']=[i for i in s['active_task_indices'] if i!=idx]
if 't3_last_polled_running' in s:s['t3_last_polled_running']=[x for x in s['t3_last_polled_running'] if x!=d['taskId']]
changed=[i for i,x in enumerate(old['tasks']) if t['tasks'][i]!=x];assert changed==[idx] and len(t['tasks'])==len(old['tasks'])
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in ['observed_utc','note','active_task_indices','t3_last_polled_running','structural209_dispatch'])
heading='## Structural209 author nominee: sharp square-root metric realization near the Clifford torus';assert heading.encode() not in lr
append='\n'+heading+'\n\nParent read the complete [unchanged frozen target](campaigns/2026-10-14/fresh-structural-discovery-r209/FROZEN-STATEMENT.md) and [author proof](campaigns/2026-10-14/fresh-structural-discovery-r209/AUTHOR-PROOF.md), admitting T333Q209 for separate independent reviews. It asserts smooth exact embeddings for the full nearby-metric ball, an explicit finite derivative budget and a sharp square-root estimate, with the integral/C1 lower bounds included. The periodic two-sign obstruction resolution, finite recursion and uniform fixed-reference smoothing bridge require independent review at the entire submitted scope. See [parent intake assessment](campaigns/2026-10-14/discovery-structural-r209-parent/assessment.md).\n\nThe complete source correction mechanism, classical operations and original r107 embedding construction are paid comparison inputs. Primary access limits, scoped history exclusions and the comparator sorry remain disclosed; neither failure of a naive inverse nor artifact verification establishes substantial contribution. Exact-anchor replay matched82selectedfiles/threeoutsidefiles/sixdirectories; all85observedfiles stayed unchanged. Seven tiny parent-local copied controls behaved as expected. No inherited semantic reading or formal endpoint support is claimed.\n\nCorrectness and contribution remain **PENDING**. No acceptance or count. **19/20, latest R041, one remaining; publication STOPPED.**\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr
(P/'intake.json').write_text(json.dumps(intake,indent=2)+'\n');tmp=registry.with_suffix('.structural209-intake.tmp');tmp.write_text(json.dumps(t,indent=2)+'\n');assert registry.read_bytes()==raw;os.replace(tmp,registry)
assert ledger.read_bytes()==lr;ledger.write_bytes(lr+append.encode())
out={'observed_utc':now,'changed_existing_tasks':changed,'new_tasks':0,'all_other_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0}
(P/'intake-record.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
