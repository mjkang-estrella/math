#!/usr/bin/env python3
"""Integrate this owner's Structural196 intake; preserve every foreign task."""
from pathlib import Path
import copy,datetime,hashlib,json,os
C=Path(__file__).resolve().parents[1];P=Path(__file__).resolve().parent;PROJECT=C.parents[2]
owner='164b1204-be68-4540-94bb-0b91055c4381'
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
terminal=json.loads((P/'task-status.json').read_text());replay=json.loads((P/'replay.json').read_text());briefs=json.loads((P/'briefs.json').read_text())
assert terminal['status']=='completed' and terminal['task_index']==668
assert replay['parent_exact_inventory_matched'] and replay['root_bytes_modes_unchanged']
A=C/'fresh-structural-discovery-r196'
assert sha(A/'author-proof.md')=='e1845bb0d890383d0a70a9a5146795b76b865fe723f25dcfef8541626ba5e985'
assert sha(A/'FROZEN.md')=='3c5dc0b976a4ccd9f7978958e56dcd6e3bc60caf502f28906285e08f8c263037'
registry=C/'tasks.json';ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md'
raw=registry.read_bytes();t=json.loads(raw);old=copy.deepcopy(t);ledgerraw=ledger.read_bytes()
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
author=t['tasks'][668];assert author['taskId']==terminal['taskId'] and author['parent_thread']==owner
for key in ['status','workState','hasPendingChildRuns','latestTerminalRunId','latestTerminalStatus','latestTerminalSummary','latestTerminalResultContextTransferId','summary','resultContextTransferId','hasPendingQuestion','pendingApproval','waitTimedOut','observed_utc']:
 author[key]=terminal[key]
author.update(parent_disposition='FULL_AUTHOR_PROOF_NOMINEE_REVIEWS_PENDING',parent_intake='discovery-structural-r196-parent/intake.json',parent_intake_utc=now,accepted=False,count_change=0,correctness=None,contribution=None,entire_unchanged_frozen_scope=True,frozen_statement_sha256=sha(A/'FROZEN.md'),author_proof_sha256=sha(A/'author-proof.md'))
reviews=[]
for role in ['proof','contribution']:
 receipt=json.loads((P/f'dispatch-{role}-r1.json').read_text());b=briefs[role]
 assert receipt['taskId'] not in [x.get('taskId') for x in t['tasks']]
 assert receipt['providerInstanceId']=='codex' and receipt['model']=='gpt-6-astra'
 assert {x['id']:x['value'] for x in receipt['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
 assert sha(C/b['path'])==b['sha256']
 idx=len(t['tasks']);entry=copy.deepcopy(receipt)
 entry.update(role='review',review_role=role,round=1,nominee='Structural196',author_task_index=668,output='frontier/campaigns/2026-10-14/'+b['output']+'/',brief='frontier/campaigns/2026-10-14/'+b['path'],brief_sha256=b['sha256'],brief_bytes=b['bytes'],target={'providerInstanceId':'codex','model':'gpt-6-astra','options':{'reasoningEffort':'xhigh','serviceTier':'default'}},parent_count_at_dispatch=19,accepted=False,count_change=0,publication='STOPPED',dispatch_receipt=f'discovery-structural-r196-parent/dispatch-{role}-r1.json',prospective_isolation='discovery-structural-r196-parent/prospective-isolation.json',status_provenance='Actual successful async dispatch response; no later liveness claim.')
 t['tasks'].append(entry);reviews.append({'task_index':idx,'role':role,'taskId':entry['taskId'],'status':entry['status'],'brief':b})
intake={'observed_utc':now,'parent_thread':owner,'author_task_index':668,'author_taskId':author['taskId'],'disposition':'FULL_AUTHOR_PROOF_NOMINEE_REVIEWS_PENDING','source':'Source320 with operative MT/PD companions; upstream truth stipulated','entire_unchanged_frozen_scope':True,'frozen_statement_sha256':sha(A/'FROZEN.md'),'author_proof_sha256':sha(A/'author-proof.md'),'detached_anchors':replay['anchors'],'parent_replay':{'artifact_only':True,'selected_files':78,'selected_bytes':7328007,'root_files':85,'exact_inventory_matched':True,'canonical_blobs':37,'canonical_folders':3,'history_extents':3,'reading_record_bindings_matched':True,'root_bytes_modes_unchanged':True,'author_verifier_limits':replay['author_verifier_limits']},'assessment_sha256':sha(P/'assessment.md'),'questions_sha256':sha(P/'questions.md'),'reviews':reviews,'correctness_gate':'PENDING','contribution_gate':'PENDING','contribution_condition':'UNDISCHARGED','accepted':False,'count_change':0,'newAccepted':19,'latestAcceptance':'R041','remaining':1,'publication':'STOPPED','next':'Await independent full-scope review completions; no fresh structural discovery or downstream work while pending.'}
(P/'intake.json').write_text(json.dumps(intake,indent=2)+'\n')
active=[i for i,x in enumerate(t['tasks']) if x.get('taskId') and x.get('parent_thread') and x.get('status') in ['running','queued','waiting']]
foreign=[{'task_index':i,'taskId':t['tasks'][i]['taskId'],'parent_thread':t['tasks'][i]['parent_thread'],'shared_record_status':t['tasks'][i]['status'],'current_liveness_verified_here':False,'action':'Preserved using shared registry metadata only; no task status/body inspection or steering.'} for i in active if t['tasks'][i]['parent_thread']!=owner]
note='Structural196(idx668) received as full author-proof nominee at unchanged scope; independent correctness and conditional contribution reviews dispatched with Astra xhigh/default. Artifact replay passed with disclosed author verifier selection/mode limits; no mathematical grade/count adopted. Foreign-owner tasks preserved from current registry without live status/body inspection. Campaign19/20, latestR041, one remains, publicationSTOPPED.'
s=t['current_work_snapshot'];s.update(observed_utc=now,note=note,active_task_indices=active,t3_last_polled_running=[r['taskId'] for r in reviews],t3_last_polled_running_note='Structural196 reviews confirmed running at dispatch only; no subsequent poll. Foreign task statuses are registry records only.',t3_recorded_running_different_owner=foreign,accepted_count=19,remaining=1,publication='STOPPED')
s['structural196_parent_intake']={'disposition':intake['disposition'],'intake':'discovery-structural-r196-parent/intake.json','assessment_sha256':intake['assessment_sha256'],'count_change':0}
s['structural196_review_dispatches']=reviews;s['structural196_review_isolation']='discovery-structural-r196-parent/prospective-isolation.json'
t['last_parent_progress']=note
for i,x in enumerate(old['tasks']):
 if i!=668:assert t['tasks'][i]==x,(i,'foreign/old task changed')
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
append='''\n## Structural196 full author-proof nominee; independent reviews dispatched\n\nStructural196 (author idx668) is received at its unchanged frozen scope. For every q >= 3 it claims an aspherical integral PD4 complex with torsion-free word-hyperbolic fundamental group whose degree-d cyclic covers have closed TOP four-manifold models exactly when q divides d. On every model of the q-fold cover, every marking gives a faithful cyclic outer action with no nonidentity class represented by any homeomorphism, irrespective of order. These are author claims pending independent review. See [intake assessment](campaigns/2026-10-14/discovery-structural-r196-parent/assessment.md) and [full-scope review questions](campaigns/2026-10-14/discovery-structural-r196-parent/questions.md).\n\nParent replay matched all78 selected files, the exact85-file root,37 canonical blobs in three pinned folders, reading-record bindings and three original-history spans. Author bytes/modes remained unchanged. Its verifier checks selected bytes and detached anchors but does not reject extra files or bind modes; copied controls confirm these limits, and parent exact-inventory/mode checks are separate. Finite coloring and tensor arithmetic checks do not establish the grope, formal-ideal, reflection or group-action arguments.\n\nIndependent full-scope correctness and conditional contribution reviews are now dispatched with Codex/gpt-6-astra/xhigh/default, matching the current inherited settings. Both briefs were finalized before dispatch and exclude the other role and the entire Arithmetic162 namespace. Initial preparation checked the former foreign idx667 brief; final preparation checked the currently registry-listed idx671 original brief for the same prospective Structural196 guard. Only guard hashes/literals and shared coordination metadata were used; no foreign live status or mathematical body was read. All foreign entries and old scopes remain unchanged. Structural195 stays closed PASS/TECHNICAL, zero count. No new structural discovery or downstream work begins while these reviews are pending. **19/20, latest R041, one remaining; no correctness/contribution grade or count adopted; publication stopped.**\n'''
assert '## Structural196 full author-proof nominee; independent reviews dispatched' not in ledgerraw.decode()
assert registry.read_bytes()==raw and ledger.read_bytes()==ledgerraw,'Concurrent ledger update: rerun against current state'
tmp=registry.with_suffix('.structural196.tmp');tmp.write_text(json.dumps(t,indent=2)+'\n');assert registry.read_bytes()==raw;os.replace(tmp,registry)
assert ledger.read_bytes()==ledgerraw;ledger.write_bytes(ledgerraw+append.encode())
(P/'integration-record.json').write_text(json.dumps({'observed_utc':now,'old_task_count':len(old['tasks']),'new_task_count':len(t['tasks']),'modified_existing_indices':[668],'new_review_indices':[r['task_index'] for r in reviews],'all_other_entries_unchanged':True,'active_task_indices':active,'foreign_metadata_only':foreign,'count_change':0},indent=2)+'\n')
print(json.dumps({'reviews':reviews,'active_indices':active,'foreign_entries_preserved':True,'count':19},indent=2))
