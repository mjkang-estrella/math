#!/usr/bin/env python3
"""Adopt only Structural202's conditional contribution gate; preserve other owners."""
from pathlib import Path
import copy, datetime, hashlib, json, os

P=Path(__file__).resolve().parent; C=P.parents[1]; PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
owner='164b1204-be68-4540-94bb-0b91055c4381'
relative='discovery-structural-r202-parent/contribution-r1-adoption/'
r=read(P/'replay.json'); terminal=read(P/'task-status.json')
assert r['author_bytes_modes_unchanged'] and r['review_bytes_modes_unchanged']
assert terminal['status']=='completed' and not terminal['hasPendingChildRuns']
assert terminal['providerInstanceId']=='codex' and terminal['model']=='gpt-6-astra'
assert {e['id']:e['value'] for e in terminal['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
registry=C/'tasks.json'; ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md'; intake_path=P.parent/'intake.json'
raw=registry.read_bytes(); old=json.loads(raw); t=copy.deepcopy(old); lr=ledger.read_bytes(); ir=intake_path.read_bytes(); intake=json.loads(ir)
assert (t['newAccepted'],t['target'],t['latestAcceptance'],t['remaining'])==(19,20,'R041',1)
a=t['tasks'][696]; q=t['tasks'][701]
assert a['parent_thread']==q['parent_thread']==owner and q['taskId']==terminal['taskId']
assert a['correctness']=='PENDING' and a['contribution']=='PENDING'
assert q['parent_full_intake_pending'] is True and intake['correctness']=='PENDING'
assert a['frozen_statement_sha256']==r['frozen_statement_sha256'] and a['author_proof_sha256']==r['author_proof_sha256']
assert sha(PROJECT/q['brief'])==q['brief_sha256']=='371ed2d08cd8f81f3925b5805df8d00db442d36c8f6fd36c32fc579777c91717'
gate='TECHNICAL_FULL_UNCHANGED_FROZEN_STRUCTURAL202_CONDITIONAL'
disposition='FULL_AUTHOR_PROOF_NOMINEE_CORRECTNESS_PENDING_CONTRIBUTION_TECHNICAL_CONDITIONAL'
adoption={'observed_utc':now,'parent_thread':owner,'review_task_index':701,'author_task_index':696,'taskId':terminal['taskId'],'gate':gate,'contribution':'TECHNICAL','correctness_condition':'UNDISCHARGED','correctness_review':'PENDING_NOT_POLLED_OR_INSPECTED','full_unchanged_scope':True,'essential_comparison_unresolved':False,'required_author_repairs':[],'review_sha256':r['review_sha256'],'frozen_statement_sha256':r['frozen_statement_sha256'],'author_proof_sha256':r['author_proof_sha256'],'review_anchors':r['anchors'],'parent_assessment_sha256':sha(P/'assessment.md'),'artifact_replay':{k:r[k] for k in ['verification','selected_bytes','root_files','root_directories','author_files','author_directories','author_bytes_modes_unchanged','review_bytes_modes_unchanged','canonical_bindings','formal_bindings','history_spans','catalogue_acceptance_spans']},'copied_controls_passed':4,'artifact_limits':r['limits'],'accepted':False,'count_change':0,'newAccepted':19,'latestAcceptance':'R041','remaining':1,'publication':'STOPPED'}
for k in ['status','workState','hasPendingChildRuns','latestTerminalRunId','latestTerminalStatus','latestTerminalSummary','latestTerminalResultContextTransferId','summary','resultContextTransferId','hasPendingQuestion','pendingApproval','waitTimedOut','observed_utc']:
    q[k]=terminal[k]
q.update(parent_disposition='CONDITIONAL_CONTRIBUTION_TECHNICAL_ADOPTED',contribution='TECHNICAL',correctness_condition='UNDISCHARGED',parent_gate=gate,parent_full_intake_pending=False,parent_adoption=relative+'adoption.json',parent_adoption_utc=now,accepted=False,count_change=0,status_provenance='Terminal lookup after delivered contribution completion; no sibling or foreign liveness lookup.')
a.update(parent_disposition=disposition,contribution='TECHNICAL_CONDITIONAL',contribution_correctness_condition='UNDISCHARGED',parent_contribution_adoption=relative+'adoption.json',accepted=False,count_change=0)
intake.update(disposition=disposition,contribution='TECHNICAL_CONDITIONAL',contribution_correctness_condition='UNDISCHARGED',contribution_adoption=relative+'adoption.json',last_adoption_utc=now,next='Receive and assess separate full-scope correctness completion. Contribution TECHNICAL is conditional; no acceptance/count or new discovery dispatch at this step.')
for entry in intake['reviews']:
    if entry['task_index']==701:entry.update(status='completed',gate=gate,correctness_condition='UNDISCHARGED',adoption=relative+'adoption.json')
s=t['current_work_snapshot']
note='Structural202 conditional full-scope contribution TECHNICAL adopted after read-only packet/receipt verification; correctness remains pending and undischarged. Separate correctness review not inspected or polled. No acceptance/count change: 19/20, latest R041, one remaining; publication STOPPED. Other records preserved.'
s.update(observed_utc=now,note=note)
s['structural202_parent_intake']['disposition']=disposition
for entry in s['structural202_review_dispatches']:
    if entry['task_index']==701:entry.update(status='completed',gate=gate,correctness_condition='UNDISCHARGED',adoption=relative+'adoption.json')
s['structural202_contribution_adoption']={'task_index':701,'gate':gate,'condition':'UNDISCHARGED','adoption':relative+'adoption.json','review_sha256':r['review_sha256'],'count_change':0}
if 'active_task_indices' in s:s['active_task_indices']=[i for i in s['active_task_indices'] if i!=701]
if 't3_last_polled_running' in s:s['t3_last_polled_running']=[x for x in s['t3_last_polled_running'] if x!=terminal['taskId']]
t['last_parent_progress']=note
changed=[i for i,z in enumerate(old['tasks']) if t['tasks'][i]!=z]
assert changed==[696,701] and len(t['tasks'])==len(old['tasks'])
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
permitted={'observed_utc','note','structural202_parent_intake','structural202_review_dispatches','structural202_contribution_adoption','active_task_indices','t3_last_polled_running'}
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in permitted)
assert t['tasks'][700]==old['tasks'][700]
heading='## Structural202 conditional contribution TECHNICAL adopted; correctness pending'
assert heading.encode() not in lr
append='\n'+heading+'\n\nParent adopts the independent contribution verdict **TECHNICAL**, conditional on correctness of the entire unchanged frozen statement and submitted proof. The full comparison gives a source-based reduction through coherent dual quotient coordinates, simultaneous moment-length scheduling, identity cotype on one G*, and compatible compact-net telescoping. It covers all frozen quantifiers, prescribed E, both compact factors and constants; no essential contribution comparison remains open. No narrower theorem or repaired submission was substituted. See [review](campaigns/2026-10-14/structural-r202-contribution-r1/REVIEW.md) and [parent assessment](campaigns/2026-10-14/discovery-structural-r202-parent/contribution-r1-adoption/assessment.md).\n\nRead-only verification matched 50 selected review files, four outside files, 11 directories, detached anchors and four copied controls. All 123 author files and ten directories remain unchanged. Source/formal receipts and exact history/acceptance/catalogue slices matched; integrity is not semantic proof reading. The assessment records scoped reading and a parent registry-output selection lapse. No foreign packet or independent correctness packet was opened or polled.\n\nCorrectness remains **UNDISCHARGED/PENDING** until its separate completion is assessed. This is not a combined closure or acceptance. No new discovery is dispatched in this step. **19/20, latest R041, one remaining; publication STOPPED.**\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr and intake_path.read_bytes()==ir
(P/'adoption.json').write_text(json.dumps(adoption,indent=2)+'\n')
tmp=registry.with_suffix('.structural202-contribution.tmp');tmp.write_text(json.dumps(t,indent=2)+'\n')
assert registry.read_bytes()==raw;os.replace(tmp,registry)
assert ledger.read_bytes()==lr;ledger.write_bytes(lr+append.encode())
assert intake_path.read_bytes()==ir;intake_path.write_text(json.dumps(intake,indent=2)+'\n')
out={'observed_utc':now,'changed_existing_tasks':changed,'new_tasks':0,'correctness_task_unchanged':True,'all_other_tasks_unchanged':True,'all_foreign_snapshot_entries_preserved':True,'count_change':0,'correctness_condition':'UNDISCHARGED'}
(P/'integration-record.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
