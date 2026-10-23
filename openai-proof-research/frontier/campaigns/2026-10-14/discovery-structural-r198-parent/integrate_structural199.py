#!/usr/bin/env python3
"""Register only the new owned discovery; preserve all existing task entries."""
from pathlib import Path
import copy, datetime, hashlib, json, os
P=Path(__file__).resolve().parent; C=P.parent; PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_text()); owner='164b1204-be68-4540-94bb-0b91055c4381'
d=read(P/'structural-r199-dispatch.json'); m=read(P/'next-discovery-preparation.json')
assert d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra'
assert {e['id']:e['value'] for e in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
assert hashlib.sha256((C/m['path']).read_bytes()).hexdigest()==m['sha256']
assert read(P/'intake.json')['disposition']=='PASS_TECHNICAL_CLOSED_ZERO_COUNT'
now=datetime.datetime.now(datetime.timezone.utc).isoformat(); registry=C/'tasks.json'; ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md'
raw=registry.read_bytes(); t=json.loads(raw); old=copy.deepcopy(t); lr=ledger.read_bytes()
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
assert not any(x.get('taskId')==d['taskId'] for x in t['tasks'])
for x in t['tasks']:
 if x.get('parent_thread') and x.get('taskId') and x.get('status') in ['running','queued','waiting']:
  assert x['parent_thread']!=owner
  assert b'*structural*r199*' in (PROJECT/x['brief']).read_bytes()
idx=len(t['tasks']); x=copy.deepcopy(d); x.pop('brief')
x.update(role='research',round=1,output='frontier/campaigns/2026-10-14/fresh-structural-discovery-r199/',brief='frontier/campaigns/2026-10-14/'+m['path'],brief_sha256=m['sha256'],brief_bytes=m['bytes'],parent_count_at_dispatch=19,accepted=False,count_change=0,publication='STOPPED',dispatch_receipt='discovery-structural-r198-parent/structural-r199-dispatch.json',prospective_isolation='discovery-structural-r198-parent/prospective-isolation-structural199.json',source_family_navigation='Source323 relative independence of separable quotient problem; exact catalogue [548447,549528), one canonical folder 14 blobs/16 entries, main.tex 2076 bytes plus ten section bodies. Lean link navigation only; parent did not read documentation or mathematical source bodies. Source and all operative proofs stipulated true; full deduction/contribution gates required.',status_provenance='Actual async dispatch response; no later liveness poll.')
t['tasks'].append(x)
s=t['current_work_snapshot']; note='Structural198 closed full-scope PASS/TECHNICAL zero count; distinct Structural199 Source323 separable-quotient independence discovery dispatched with prospective peer guards and unchanged standing exclusions. Campaign 19/20 latest R041 one remains; publication STOPPED. Foreign tasks preserved without liveness/body inspection.'
s.update(observed_utc=now,note=note)
s['structural199_dispatch']={'task_index':idx,'taskId':d['taskId'],'brief_sha256':m['sha256'],'prospective_isolation':'discovery-structural-r198-parent/prospective-isolation-structural199.json'}
active=[i for i,z in enumerate(t['tasks']) if z.get('parent_thread') and z.get('taskId') and z.get('status') in ['running','queued','waiting']]
s['active_task_indices']=active
s['t3_last_polled_running']=[t['tasks'][i]['taskId'] for i in active if t['tasks'][i]['parent_thread']==owner]
s['t3_last_polled_running_note']='Owned discovery status comes from actual async dispatch response only. Foreign statuses are shared records only; no poll.'
s['t3_recorded_running_different_owner']=[{'task_index':i,'taskId':t['tasks'][i]['taskId'],'parent_thread':t['tasks'][i]['parent_thread'],'shared_record_status':t['tasks'][i]['status'],'current_liveness_verified_here':False,'action':'Preserved shared registry metadata; initial-brief literal guard/hash check only, no mathematical body/liveness inspection or steering.'} for i in active if t['tasks'][i]['parent_thread']!=owner]
t['last_parent_progress']=note
assert t['tasks'][:-1]==old['tasks']
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
append="\n## Distinct Structural199 discovery dispatched: Source323 separable quotients\n\nFollowing the entire-scope Structural198 PASS/TECHNICAL closure, a new discovery task studies the pinned relative-independence source for the separable quotient problem. Its initial brief preserves every literal, no-r and substring exclusion and excludes all closed-round bodies. The currently recorded foreign task's original initial brief already contained the Structural199 exclusion before this brief or output root existed; only its literal guard and hash were checked. No foreign mathematical body or liveness was inspected.\n\nParent navigation selected only Source323, catalogue bytes [548447,549528), and its single canonical folder (fourteen blobs/sixteen entries; main.tex 2,076 bytes and ten section bodies). The Lean link is navigation only; parent read neither its documentation nor source mathematical bodies for this discovery. The child must read actual operative proofs, primary comparisons and eligible original history before sustained deductions, freeze and proof. Exact ambient-model, field, density, separability and consistency quantifiers are required. Stipulated upstream truth, full-scope gates, immutable old targets and publication stop remain. **19/20, latest R041, one remains.**\n"
assert '## Distinct Structural199 discovery dispatched:' not in lr.decode()
assert registry.read_bytes()==raw and ledger.read_bytes()==lr
rt=registry.with_suffix('.structural199.tmp'); rt.write_text(json.dumps(t,indent=2)+'\n'); assert registry.read_bytes()==raw; os.replace(rt,registry)
assert ledger.read_bytes()==lr; ledger.write_bytes(lr+append.encode())
result={'observed_utc':now,'new_task_index':idx,'taskId':d['taskId'],'old_task_count':len(old['tasks']),'all_existing_task_entries_unchanged':True,'active_task_indices':active,'count_change':0}
(P/'structural-r199-integration.json').write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps(result,indent=2))
