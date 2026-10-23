#!/usr/bin/env python3
"""Register distinct Source327 discovery without altering any existing task."""
from pathlib import Path
import copy,datetime,hashlib,json,os
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes());owner='164b1204-be68-4540-94bb-0b91055c4381'
d=read(P/'structural-r203-dispatch.json');m=read(P/'next-discovery-preparation.json');iso=read(P/'prospective-isolation-structural203.json')
assert d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra' and d['parent_thread']==owner
assert {e['id']:e['value'] for e in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
b=(C/m['path']).read_bytes();assert hashlib.sha256(b).hexdigest()==m['sha256'] and d['brief'].encode()==b
assert read(P/'closure.json')['disposition']=='CLOSED_FULL_SCOPE_PASS_TECHNICAL_ZERO_COUNT'
now=datetime.datetime.now(datetime.timezone.utc).isoformat();registry=C/'tasks.json';ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md'
raw=registry.read_bytes();t=json.loads(raw);old=copy.deepcopy(t);lr=ledger.read_bytes()
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
assert not any(e.get('taskId')==d['taskId'] for e in t['tasks'])
for i,e in enumerate(t['tasks']):
    if e.get('parent_thread') and e.get('taskId') and e.get('status') in ['running','queued','waiting']:
        assert e['parent_thread']!=owner
        q=(PROJECT/e['brief']).read_bytes();assert b'*structural*r203*' in q
        receipt=next(x for x in iso['foreign_original_guard_checks'] if x['task_index']==i)
        assert hashlib.sha256(q).hexdigest()==receipt['sha256']
idx=len(t['tasks']);x=copy.deepcopy(d);x.pop('brief')
x.update(role='research',round=1,output='frontier/campaigns/2026-10-14/fresh-structural-discovery-r203/',brief='frontier/campaigns/2026-10-14/'+m['path'],brief_sha256=m['sha256'],brief_bytes=m['bytes'],parent_count_at_dispatch=19,accepted=False,count_change=0,publication='STOPPED',dispatch_receipt='discovery-structural-r202-parent/structural-r203-dispatch.json',prospective_isolation='discovery-structural-r202-parent/prospective-isolation-structural203.json',source_family_navigation='Source327 Markov type and superreflexivity; exact catalogue [553766,554644), one canonical manuscript with 5 blobs/7 entries, main.tex 42458 bytes plus references and chart-transport figure. Lean link navigation only. Parent did not read source mathematical bodies or formal documentation. All operative upstream proofs stipulated true; full independent gates required.',status_provenance='Actual async dispatch response only; no subsequent liveness poll.')
t['tasks'].append(x)
s=t['current_work_snapshot'];note='Structural202 closed full-scope PASS/TECHNICAL with zero count. Distinct Structural203 Source327 Markov-type/superreflexivity discovery dispatched under prospective guards and all inherited exclusions. Campaign 19/20, latest R041, one remaining; publication STOPPED. Foreign entries preserved without liveness/body inspection.'
s.update(observed_utc=now,note=note);s['structural203_dispatch']={'task_index':idx,'taskId':d['taskId'],'brief_sha256':m['sha256'],'prospective_isolation':'discovery-structural-r202-parent/prospective-isolation-structural203.json'}
active=[i for i,e in enumerate(t['tasks']) if e.get('parent_thread') and e.get('taskId') and e.get('status') in ['running','queued','waiting']]
s['active_task_indices']=active;s['t3_last_polled_running']=[t['tasks'][i]['taskId'] for i in active if t['tasks'][i]['parent_thread']==owner]
s['t3_last_polled_running_note']='Owned discovery status comes only from its async dispatch response. Foreign statuses are shared coordination records; no liveness poll.'
t['last_parent_progress']=note
assert t['tasks'][:-1]==old['tasks'] and all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
allowed={'observed_utc','note','active_task_indices','t3_last_polled_running','t3_last_polled_running_note'}
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in allowed)
heading='## Distinct Structural203 discovery dispatched: Source327 Markov type and superreflexivity'
assert heading.encode() not in lr
append='\n'+heading+'\n\nAfter closing Structural202 at full-scope PASS/TECHNICAL with zero count, a fresh discovery task studies the pinned nontrivial-Markov-type construction and superreflexivity. The initial brief preserves the complete standing brief and all literal/no-r/substring exclusions, adds the two opaque derivative substrings from the prior review setup and prospective Structural204–206 guards, and admits no closed-round mathematical body. The foreign task recorded active already had the Structural203 exclusion in its original initial brief before this brief/output root existed; only literal/hash coordination checks were performed.\n\nParent navigation selected only catalogue bytes [553766,554644) and canonical metadata for five blobs/seven entries, including main.tex (42,458 bytes), references and chart-transport figure. Source mathematical bodies and Lean documentation remain for the child to authenticate and read fully. The task requires actual strongest primary/source/history composition, precise Markov-chain and renorming parameters, a distinct nonroutine residual and a complete frozen proof before independent gates. Qualitative equivalent reformulations do not automatically count. No formalization or publication is authorized. **19/20, latest R041, one remaining; publication STOPPED.**\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr
tmp=registry.with_suffix('.structural203.tmp');tmp.write_text(json.dumps(t,indent=2)+'\n');assert registry.read_bytes()==raw;os.replace(tmp,registry)
assert ledger.read_bytes()==lr;ledger.write_bytes(lr+append.encode())
out={'observed_utc':now,'new_task_index':idx,'taskId':d['taskId'],'old_task_count':len(old['tasks']),'all_existing_task_entries_unchanged':True,'all_foreign_snapshot_entries_preserved':True,'active_task_indices':active,'count_change':0}
(P/'structural-r203-integration.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
