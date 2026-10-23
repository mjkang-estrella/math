#!/usr/bin/env python3
"""Adopt the delivered contribution review and close only Structural203."""
from pathlib import Path
import copy,datetime,hashlib,json,os
P=Path(__file__).resolve().parent;C=P.parents[1];PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
now=datetime.datetime.now(datetime.timezone.utc).isoformat();owner='164b1204-be68-4540-94bb-0b91055c4381';rel='discovery-structural-r203-parent/contribution-r1-adoption/'
r=read(P/'replay.json');terminal=read(P/'task-status.json');correct=read(P.parent/'proof-r1-adoption/adoption.json')
assert terminal['status']=='completed' and not terminal['hasPendingChildRuns'] and r['author_bytes_modes_unchanged'] and r['review_bytes_modes_unchanged']
assert terminal['providerInstanceId']=='codex' and terminal['model']=='gpt-6-astra'
assert {e['id']:e['value'] for e in terminal['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
assert correct['correctness']=='PASS' and correct['entire_unchanged_scope'] and not correct['essential_repairs'] and not correct['unresolved_mathematical_obligations']
assert all(correct[k]==r[k] for k in ['frozen_statement_sha256','author_proof_sha256'])
registry=C/'tasks.json';ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md';ip=P.parent/'intake.json'
raw=registry.read_bytes();t=json.loads(raw);old=copy.deepcopy(t);lr=ledger.read_bytes();ir=ip.read_bytes();intake=json.loads(ir)
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
a=t['tasks'][703];q=t['tasks'][706];assert a['parent_thread']==q['parent_thread']==owner and q['taskId']==terminal['taskId']
assert a['correctness']=='PASS' and a['contribution']=='PENDING' and q['parent_full_intake_pending'] is True
assert sha(PROJECT/q['brief'])==q['brief_sha256']=='8087dbe4a85f2cb22ffc36637a294dce5fb12b395d83c6b321b5c077aef05cd7'
assert all(a[k]==r[k] for k in ['frozen_statement_sha256','author_proof_sha256'])
gate='TECHNICAL_FULL_UNCHANGED_FROZEN_STRUCTURAL203';disp='CLOSED_FULL_SCOPE_PASS_TECHNICAL_ZERO_COUNT'
adopt={'observed_utc':now,'parent_thread':owner,'review_task_index':706,'author_task_index':703,'taskId':terminal['taskId'],'gate':gate,'contribution':'TECHNICAL','entire_unchanged_scope':True,'reviewer_correctness_condition':'UNDISCHARGED','parent_correctness':'PASS','parent_correctness_condition':'DISCHARGED','correctness_adoption':'discovery-structural-r203-parent/proof-r1-adoption/adoption.json','correctness_adoption_sha256':sha(P.parent/'proof-r1-adoption/adoption.json'),'essential_unfinished_contribution_comparison':[],'review_sha256':r['review_sha256'],'frozen_statement_sha256':r['frozen_statement_sha256'],'author_proof_sha256':r['author_proof_sha256'],'review_anchors':r['anchors'],'parent_assessment_sha256':sha(P/'assessment.md'),'artifact_replay':{k:r[k] for k in ['verification','selected_content_bytes','root_files','root_directories','author_files','author_directories','author_bytes_modes_unchanged','review_bytes_modes_unchanged','reviewer_author_file_baseline','canonical_blobs','primary_text_bindings','primary_pdf_bindings','new_retrieval_response_bindings','render_files_integrity_only','history_spans','direct_input_bindings']},'copied_controls_passed':6,'artifact_limits':r['limits'],'disposition':disp,'accepted':False,'count_change':0,'newAccepted':19,'latestAcceptance':'R041','remaining':1,'publication':'STOPPED'}
for k in ['status','workState','hasPendingChildRuns','latestTerminalRunId','latestTerminalStatus','latestTerminalSummary','latestTerminalResultContextTransferId','summary','resultContextTransferId','hasPendingQuestion','pendingApproval','waitTimedOut','observed_utc']:q[k]=terminal[k]
q.update(parent_disposition='FULL_SCOPE_TECHNICAL_ADOPTED_CONDITION_DISCHARGED',contribution='TECHNICAL',parent_gate=gate,parent_full_intake_pending=False,parent_adoption=rel+'adoption.json',parent_adoption_utc=now,parent_correctness_condition='DISCHARGED',accepted=False,count_change=0,status_provenance='Terminal lookup after delivered contribution completion only; no foreign liveness lookup.')
a.update(parent_disposition=disp,contribution='TECHNICAL',correctness_condition='DISCHARGED',parent_contribution_adoption=rel+'adoption.json',accepted=False,count_change=0)
intake.update(disposition=disp,contribution='TECHNICAL',correctness_condition='DISCHARGED',contribution_adoption=rel+'adoption.json',last_adoption_utc=now,next='Closed unchanged scope, no count. Proceed only to a genuinely distinct discovery with prospective isolation; no renaming, narrowing or review shopping.')
for e in intake['reviews']:
    if e['task_index']==706:e.update(status='completed',gate=gate,adoption=rel+'adoption.json')
s=t['current_work_snapshot'];note='Structural203 CLOSED at entire unchanged scope: correctness PASS / contribution TECHNICAL, condition DISCHARGED, zero count. Complete compatible finite source/classical reduction adopted. Campaign19/20 latestR041 one remains; publicationSTOPPED. Next work must be distinct. Other records preserved.'
s.update(observed_utc=now,note=note);s['structural203_parent_intake']['disposition']=disp
for e in s['structural203_review_dispatches']:
    if e['task_index']==706:e.update(status='completed',gate=gate,adoption=rel+'adoption.json')
s['structural203_contribution_adoption']={'task_index':706,'gate':gate,'adoption':rel+'adoption.json','review_sha256':r['review_sha256'],'correctness_condition':'DISCHARGED','count_change':0}
s['structural203_closure']={'author_task_index':703,'correctness':'PASS','contribution':'TECHNICAL','condition':'DISCHARGED','unchanged_scope':True,'count_change':0,'adoption':rel+'adoption.json'}
if 'active_task_indices' in s:s['active_task_indices']=[i for i in s['active_task_indices'] if i!=706]
if 't3_last_polled_running' in s:s['t3_last_polled_running']=[x for x in s['t3_last_polled_running'] if x!=terminal['taskId']]
t['last_parent_progress']=note
changed=[i for i,e in enumerate(old['tasks']) if t['tasks'][i]!=e];assert changed==[703,706] and len(t['tasks'])==len(old['tasks'])
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
allowed={'observed_utc','note','structural203_parent_intake','structural203_review_dispatches','active_task_indices','t3_last_polled_running'}
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in allowed)
heading='## Structural203 closed: full-scope PASS / TECHNICAL, zero count'
assert heading.encode() not in lr
append='\n'+heading+'\n\nParent adopts the independent contribution review as **TECHNICAL** for the entire unchanged frozen theorem, constants, corollary and submitted proof. The earlier independent full-scope correctness **PASS** discharges the contribution condition at parent level. The reviewer’s role-local correctness remains UNDISCHARGED in its unchanged report. See [complete contribution review](campaigns/2026-10-14/structural-r203-contribution-r1/packet/REVIEW.md) and [parent combined assessment](campaigns/2026-10-14/discovery-structural-r203-parent/contribution-r1-adoption/assessment.md).\n\nThe compatible reduction reaches all frozen constants using the actual source subdivision sandwich, a one-endpoint finite p-Cesaro estimate, rational and convex merging bounds, finite chart/lattice counts, same-chain coordinate extraction, and Hahn–Banach deficits. No specific nonroutine residual or essential unfinished comparison remains. Original Brunel seminar proof operations and Wenzel strengthen the comparison; original 1975 access, scoped history and incomplete formal coverage remain disclosed.\n\nRead-only verification matched 43 selected files/four directories and six copied controls. All 53 review-root files/seven directories and all 50 author files/14 directories remained unchanged. Authentication is not semantic reading. Preserve this closed exact scope; no renaming, narrowing or review shopping. **19/20, latest R041, one remaining; zero acceptance/count added; publication STOPPED.**\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr and ip.read_bytes()==ir
(P/'adoption.json').write_text(json.dumps(adopt,indent=2)+'\n')
tmp=registry.with_suffix('.structural203-contribution.tmp');tmp.write_text(json.dumps(t,indent=2)+'\n');assert registry.read_bytes()==raw;os.replace(tmp,registry)
assert ledger.read_bytes()==lr;ledger.write_bytes(lr+append.encode());assert ip.read_bytes()==ir;ip.write_text(json.dumps(intake,indent=2)+'\n')
out={'observed_utc':now,'changed_existing_tasks':changed,'new_tasks':0,'correctness_task_unchanged':True,'all_other_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'condition':'DISCHARGED','count_change':0}
(P/'integration-record.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
