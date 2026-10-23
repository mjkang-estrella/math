#!/usr/bin/env python3
"""Adopt only this completed correctness review; preserve concurrent tasks."""
from pathlib import Path
import copy,datetime,hashlib,json,os
P=Path(__file__).resolve().parent;C=P.parents[1];PROJECT=C.parents[2];owner='164b1204-be68-4540-94bb-0b91055c4381'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();now=datetime.datetime.now(datetime.timezone.utc).isoformat()
r=read(P/'replay.json');terminal=read(P/'task-status.json');assert terminal['status']=='completed' and not terminal['hasPendingChildRuns'];assert r['author_and_reviewer_bytes_modes_unchanged']
gate='PASS_FULL_UNCHANGED_FROZEN_STRUCTURAL196';rel='discovery-structural-r196-parent/proof-r1-adoption/'
adopt={'observed_utc':now,'parent_thread':owner,'task_index':674,'taskId':terminal['taskId'],'gate':gate,'entire_unchanged_frozen_scope':True,'frozen_statement_sha256':'3c5dc0b976a4ccd9f7978958e56dcd6e3bc60caf502f28906285e08f8c263037','author_proof_sha256':'e1845bb0d890383d0a70a9a5146795b76b865fe723f25dcfef8541626ba5e985','review_sha256':r['review_sha256'],'review_anchors':r['anchors'],'assessment_sha256':sha(P/'assessment.md'),'artifact_replay':{'selected_files':142,'selected_bytes':r['selected_bytes'],'canonical_blobs':37,'primary_texts':6,'history_spans':3,'copied_controls_passed':12,'exact_selection_and_modes':True,'author_and_review_roots_unchanged':True},'contribution_gate':'PENDING','correctness_prerequisite':'SATISFIED_ON_IDENTICAL_FROZEN_STATEMENT_AND_PROOF','accepted':False,'count_change':0,'newAccepted':19,'latestAcceptance':'R041','remaining':1,'publication':'STOPPED'}
(P/'adoption.json').write_text(json.dumps(adopt,indent=2)+'\n')
registry=C/'tasks.json';ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md';ip=P.parent/'intake.json'
raw=registry.read_bytes();t=json.loads(raw);old=copy.deepcopy(t);lr=ledger.read_bytes();ir=ip.read_bytes();intake=json.loads(ir)
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
x=t['tasks'][674];assert x['taskId']==terminal['taskId'] and x['parent_thread']==owner
for k in ['status','workState','hasPendingChildRuns','latestTerminalRunId','latestTerminalStatus','latestTerminalSummary','latestTerminalResultContextTransferId','summary','resultContextTransferId','hasPendingQuestion','pendingApproval','waitTimedOut','observed_utc']:x[k]=terminal[k]
x.update(parent_disposition=gate,correctness='PASS',entire_unchanged_frozen_scope=True,parent_full_intake_pending=False,parent_adoption=rel+'adoption.json',parent_intake_utc=now,accepted=False,count_change=0)
a=t['tasks'][668];assert a['parent_thread']==owner;a.update(parent_disposition='CORRECTNESS_PASS_CONTRIBUTION_PENDING',correctness='PASS',correctness_adoption=rel+'adoption.json',accepted=False,count_change=0)
intake.update(disposition='CORRECTNESS_PASS_CONTRIBUTION_PENDING',correctness_gate=gate,contribution_gate='PENDING',contribution_condition='DISCHARGED',correctness_review_adoption=rel+'adoption.json',correctness_review_sha256=r['review_sha256'],correctness_adopted_utc=now)
for q in intake['reviews']:
 if q['role']=='proof':q.update(status='completed',gate=gate)
s=t['current_work_snapshot'];note='Structural196 full unchanged correctness PASS adopted after complete review reading and exact142-file replay; contribution pending. No count/downstream change. Foreign-owner entries preserved without liveness/body inspection. Campaign19/20 latestR041 one remains publicationSTOPPED.'
s.update(observed_utc=now,note=note)
s['structural196_parent_intake'].update(disposition=intake['disposition'])
for q in s['structural196_review_dispatches']:
 if q['role']=='proof':q.update(status='completed',gate=gate)
s['structural196_correctness_adoption']={'task_index':674,'gate':gate,'adoption':rel+'adoption.json','review_sha256':r['review_sha256'],'count_change':0}
active=[i for i,z in enumerate(t['tasks']) if z.get('parent_thread') and z.get('taskId') and z.get('status') in ['running','queued','waiting']]
s['active_task_indices']=active;s['t3_last_polled_running']=[t['tasks'][i]['taskId'] for i in active if t['tasks'][i]['parent_thread']==owner];s['t3_last_polled_running_note']='Remaining owned task recorded running at original dispatch only; no sibling poll. Completed correctness task queried once after its completion notification.'
s['t3_recorded_running_different_owner']=[{'task_index':i,'taskId':t['tasks'][i]['taskId'],'parent_thread':t['tasks'][i]['parent_thread'],'shared_record_status':t['tasks'][i]['status'],'current_liveness_verified_here':False,'action':'Preserved from shared registry; no status/body inspection or steering.'} for i in active if t['tasks'][i]['parent_thread']!=owner]
t['last_parent_progress']=note
for i,z in enumerate(old['tasks']):
 if i not in [668,674]:assert t['tasks'][i]==z
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
append='''\n## Structural196 full unchanged correctness PASS; contribution pending\n\nThe independent correctness review is adopted as **PASS for the entire unchanged frozen statement and author proof**, relative to stipulated upstream truth. It resolves all twelve checks, including marked grope geometry, full group-ring cancellation, actual nonreduced ideals, repeated-label reflection, every cover degree, every model/marking and homeomorphisms of unrestricted order. No repair, narrowing or unresolved correctness obligation is identified. See [review](campaigns/2026-10-14/structural-r196-proof-r1/REVIEW.md) and [parent adoption](campaigns/2026-10-14/discovery-structural-r196-parent/proof-r1-adoption/assessment.md).\n\nParent read the full review and limits and replayed142 selected files, exact selection/modes,37 canonical bindings, six primary bindings, three history spans and twelve tiny copied controls. Author and reviewer roots remained unchanged. Extraction and reading limits, no initial history-mode receipt and the author's weaker verifier remain explicit. The independent contribution review is pending; no acceptance or downstream stage opens. Foreign-owner entries and earlier scopes are preserved. **19/20, latest R041, one remaining; publication stopped.**\n'''
assert '## Structural196 full unchanged correctness PASS; contribution pending' not in lr.decode()
assert registry.read_bytes()==raw and ledger.read_bytes()==lr and ip.read_bytes()==ir
rt=registry.with_suffix('.structural196-proof.tmp');rt.write_text(json.dumps(t,indent=2)+'\n');assert registry.read_bytes()==raw;os.replace(rt,registry)
assert ledger.read_bytes()==lr;ledger.write_bytes(lr+append.encode());assert ip.read_bytes()==ir;ip.write_text(json.dumps(intake,indent=2)+'\n')
print(json.dumps({'correctness':gate,'contribution':'PENDING','count':19,'modified_task_indices':[668,674],'foreign_entries_unchanged':True,'active_indices':active},indent=2))
