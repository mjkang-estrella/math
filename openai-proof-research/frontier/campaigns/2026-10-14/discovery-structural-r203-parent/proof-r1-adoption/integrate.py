#!/usr/bin/env python3
"""Adopt only full-scope correctness; leave the separate contribution task unchanged."""
from pathlib import Path
import copy,datetime,hashlib,json,os
P=Path(__file__).resolve().parent;C=P.parents[1];PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();now=datetime.datetime.now(datetime.timezone.utc).isoformat();owner='164b1204-be68-4540-94bb-0b91055c4381';rel='discovery-structural-r203-parent/proof-r1-adoption/'
r=read(P/'replay.json');terminal=read(P/'task-status.json')
assert terminal['status']=='completed' and not terminal['hasPendingChildRuns'] and r['author_bytes_modes_unchanged'] and r['review_bytes_modes_unchanged']
assert terminal['providerInstanceId']=='codex' and terminal['model']=='gpt-6-astra'
assert {e['id']:e['value'] for e in terminal['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
registry=C/'tasks.json';ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md';ip=P.parent/'intake.json';raw=registry.read_bytes();t=json.loads(raw);old=copy.deepcopy(t);lr=ledger.read_bytes();ir=ip.read_bytes();intake=json.loads(ir)
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
a=t['tasks'][703];q=t['tasks'][705];assert a['parent_thread']==q['parent_thread']==owner and q['taskId']==terminal['taskId']
assert a['correctness']=='PENDING' and a['contribution']=='PENDING' and q['parent_full_intake_pending'] is True
assert sha(PROJECT/q['brief'])==q['brief_sha256']=='4f66057fe922747920dc569b37c99c4a06d03414c0e28e5b67b5a9acbf07d412'
assert a['frozen_statement_sha256']==r['frozen_statement_sha256'] and a['author_proof_sha256']==r['author_proof_sha256']
gate='PASS_FULL_UNCHANGED_FROZEN_STRUCTURAL203';disp='FULL_SCOPE_CORRECTNESS_PASS_CONTRIBUTION_PENDING'
adopt={'observed_utc':now,'parent_thread':owner,'review_task_index':705,'author_task_index':703,'taskId':terminal['taskId'],'gate':gate,'correctness':'PASS','entire_unchanged_scope':True,'upstream_proofs_stipulated_true':True,'essential_repairs':[],'unresolved_mathematical_obligations':[],'review_sha256':r['review_sha256'],'frozen_statement_sha256':r['frozen_statement_sha256'],'author_proof_sha256':r['author_proof_sha256'],'review_anchors':r['anchors'],'parent_assessment_sha256':sha(P/'assessment.md'),'artifact_replay':{k:r[k] for k in ['verification','root_files','root_directories','author_files','author_directories','author_bytes_modes_unchanged','review_bytes_modes_unchanged','reviewer_author_baseline_files','reviewer_author_baseline_directories','canonical_blobs','formal_bindings','canonical_and_formal_reading_bindings','primary_text_extent_bindings','new_primary_pdf_bindings','render_files_integrity_only','history_spans','direct_input_bindings']},'copied_controls_passed':7,'artifact_limits':r['limits'],'contribution_status':'PENDING_NOT_POLLED_OR_INSPECTED','accepted':False,'count_change':0,'newAccepted':19,'latestAcceptance':'R041','remaining':1,'publication':'STOPPED'}
for k in ['status','workState','hasPendingChildRuns','latestTerminalRunId','latestTerminalStatus','latestTerminalSummary','latestTerminalResultContextTransferId','summary','resultContextTransferId','hasPendingQuestion','pendingApproval','waitTimedOut','observed_utc']:q[k]=terminal[k]
q.update(parent_disposition='FULL_SCOPE_CORRECTNESS_PASS_ADOPTED',correctness='PASS',parent_gate=gate,parent_full_intake_pending=False,parent_adoption=rel+'adoption.json',parent_adoption_utc=now,accepted=False,count_change=0,status_provenance='Terminal lookup after delivered correctness completion only; no sibling or foreign liveness lookup.')
a.update(parent_disposition=disp,correctness='PASS',parent_correctness_adoption=rel+'adoption.json',accepted=False,count_change=0)
intake.update(disposition=disp,correctness='PASS',correctness_adoption=rel+'adoption.json',last_adoption_utc=now,next='Receive and assess separate contribution completion at unchanged scope. Correctness PASS alone gives no contribution grade, acceptance/count or new discovery dispatch.')
for e in intake['reviews']:
    if e['task_index']==705:e.update(status='completed',gate=gate,adoption=rel+'adoption.json')
s=t['current_work_snapshot'];note='Structural203 full-scope correctness PASS adopted for unchanged frozen statement/proof under stipulated upstream premises. No essential repair or unresolved mathematical obligation. Separate contribution review pending and unpolled. Campaign19/20 latestR041 one remains; no acceptance/count change, publicationSTOPPED. Other records preserved.'
s.update(observed_utc=now,note=note);s['structural203_parent_intake']['disposition']=disp
for e in s['structural203_review_dispatches']:
    if e['task_index']==705:e.update(status='completed',gate=gate,adoption=rel+'adoption.json')
s['structural203_correctness_adoption']={'task_index':705,'gate':gate,'adoption':rel+'adoption.json','review_sha256':r['review_sha256'],'count_change':0}
if 'active_task_indices' in s:s['active_task_indices']=[i for i in s['active_task_indices'] if i!=705]
if 't3_last_polled_running' in s:s['t3_last_polled_running']=[x for x in s['t3_last_polled_running'] if x!=terminal['taskId']]
t['last_parent_progress']=note
changed=[i for i,e in enumerate(old['tasks']) if t['tasks'][i]!=e];assert changed==[703,705] and len(t['tasks'])==len(old['tasks']) and t['tasks'][706]==old['tasks'][706]
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
allowed={'observed_utc','note','structural203_parent_intake','structural203_review_dispatches','active_task_indices','t3_last_polled_running'}
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in allowed)
heading='## Structural203 full-scope correctness PASS adopted; contribution pending'
assert heading.encode() not in lr
append='\n'+heading+'\n\nParent adopts **PASS** for the entire unchanged frozen Theorem A, Corollary B and submitted proof, under stipulated upstream premises. The review reconstructs the explicit Ramsey/separation bounds, finite averaging domains and endpoint, all-sign/cancellation merging, exact source cuts and norm errors, stationary probabilities, finite reflected lattice and state count, same-chain coordinate extraction, and strict Hahn–Banach J-convexity conversion. No essential objection, unproved bridge or required repair remains. See [review](campaigns/2026-10-14/structural-r203-proof-r1/packet/REVIEW.md) and [parent assessment](campaigns/2026-10-14/discovery-structural-r203-parent/proof-r1-adoption/assessment.md).\n\nRead-only checks matched 27 selected files/four directories, three detached anchors and seven copied controls; all50author files/14directories and all37review-root files/seven directories remained unchanged. Primary/source/history and render authentication is not semantic rereading. The reviewer additionally read Wenzel’s quantitative primary proof; original Brunel–Sucheston access and scoped history/formal limitations remain disclosed without a contribution grade.\n\nThe separate contribution review remains **PENDING**, uninspected and unpolled. No acceptance/count or combined closure follows from correctness alone. **19/20, latest R041, one remaining; publication STOPPED.**\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr and ip.read_bytes()==ir
(P/'adoption.json').write_text(json.dumps(adopt,indent=2)+'\n')
tmp=registry.with_suffix('.structural203-proof.tmp');tmp.write_text(json.dumps(t,indent=2)+'\n');assert registry.read_bytes()==raw;os.replace(tmp,registry)
assert ledger.read_bytes()==lr;ledger.write_bytes(lr+append.encode());assert ip.read_bytes()==ir;ip.write_text(json.dumps(intake,indent=2)+'\n')
out={'observed_utc':now,'changed_existing_tasks':changed,'new_tasks':0,'contribution_task_unchanged':True,'all_other_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0}
(P/'integration-record.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
