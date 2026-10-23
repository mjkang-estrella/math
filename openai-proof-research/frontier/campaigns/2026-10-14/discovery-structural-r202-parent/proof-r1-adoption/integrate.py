#!/usr/bin/env python3
"""Adopt full correctness, discharge prior contribution condition, close with zero count."""
from pathlib import Path
import copy,datetime,hashlib,json,os
P=Path(__file__).resolve().parent;C=P.parents[1];PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
now=datetime.datetime.now(datetime.timezone.utc).isoformat();owner='164b1204-be68-4540-94bb-0b91055c4381'
rel='discovery-structural-r202-parent/proof-r1-adoption/';close_rel='discovery-structural-r202-parent/closure.json'
r=read(P/'replay.json');terminal=read(P/'task-status.json');ca=read(P.parent/'contribution-r1-adoption/adoption.json')
assert terminal['status']=='completed' and not terminal['hasPendingChildRuns']
assert terminal['providerInstanceId']=='codex' and terminal['model']=='gpt-6-astra'
assert {e['id']:e['value'] for e in terminal['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
assert r['author_bytes_modes_unchanged'] and r['review_bytes_modes_unchanged']
assert ca['contribution']=='TECHNICAL' and ca['correctness_condition']=='UNDISCHARGED'
assert ca['frozen_statement_sha256']==r['frozen_statement_sha256'] and ca['author_proof_sha256']==r['author_proof_sha256']
registry=C/'tasks.json';ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md';ip=P.parent/'intake.json'
raw=registry.read_bytes();t=json.loads(raw);old=copy.deepcopy(t);lr=ledger.read_bytes();ir=ip.read_bytes();intake=json.loads(ir)
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
a,q,c=[t['tasks'][i] for i in [696,700,701]]
assert all(x['parent_thread']==owner for x in [a,q,c]) and q['taskId']==terminal['taskId']
assert a['correctness']=='PENDING' and a['contribution']=='TECHNICAL_CONDITIONAL' and c['correctness_condition']=='UNDISCHARGED'
assert sha(PROJECT/q['brief'])==q['brief_sha256']=='60f40d03edab68301a0b253623d2232bfa7cef5745912a8d101b1d2ee0ee190b'
pg='PASS_FULL_UNCHANGED_FROZEN_STRUCTURAL202';cg='TECHNICAL_FULL_UNCHANGED_FROZEN_STRUCTURAL202';disp='CLOSED_FULL_SCOPE_PASS_TECHNICAL_ZERO_COUNT'
adopt={'observed_utc':now,'parent_thread':owner,'review_task_index':700,'author_task_index':696,'taskId':terminal['taskId'],'gate':pg,'correctness':'PASS','entire_unchanged_scope':True,'upstream_proofs_stipulated_true':True,'essential_repairs':[],'unresolved_mathematical_obligations':[],'review_sha256':r['review_sha256'],'frozen_statement_sha256':r['frozen_statement_sha256'],'author_proof_sha256':r['author_proof_sha256'],'review_anchors':r['anchors'],'parent_assessment_sha256':sha(P/'assessment.md'),'artifact_replay':{k:r[k] for k in ['verification','selected_bytes','root_files','root_directories','author_files','author_directories','author_bytes_modes_unchanged','review_bytes_modes_unchanged','canonical_bindings','canonical_text_reading_bindings','formal_bindings','primary_pdf_bindings','history_spans','catalogue_acceptance_spans']},'copied_controls_passed':8,'artifact_limits':r['limits'],'accepted':False,'count_change':0,'newAccepted':19,'latestAcceptance':'R041','remaining':1,'publication':'STOPPED'}
closure={'observed_utc':now,'disposition':disp,'author_task_index':696,'correctness_task_index':700,'contribution_task_index':701,'correctness':pg,'contribution':cg,'condition':'DISCHARGED','frozen_statement_sha256':r['frozen_statement_sha256'],'author_proof_sha256':r['author_proof_sha256'],'correctness_review_sha256':r['review_sha256'],'contribution_review_sha256':ca['review_sha256'],'correctness_adoption':rel+'adoption.json','prior_conditional_contribution_adoption':'discovery-structural-r202-parent/contribution-r1-adoption/adoption.json','prior_conditional_record_preserved':True,'essential_repairs':[],'accepted':False,'count_change':0,'newAccepted':19,'latestAcceptance':'R041','remaining':1,'publication':'STOPPED','next':'Distinct discovery with prospective exclusions; never narrow, rename or re-review this closed scope for a different grade.'}
for k in ['status','workState','hasPendingChildRuns','latestTerminalRunId','latestTerminalStatus','latestTerminalSummary','latestTerminalResultContextTransferId','summary','resultContextTransferId','hasPendingQuestion','pendingApproval','waitTimedOut','observed_utc']:q[k]=terminal[k]
q.update(parent_disposition='FULL_SCOPE_CORRECTNESS_PASS_ADOPTED',correctness='PASS',parent_gate=pg,parent_full_intake_pending=False,parent_adoption=rel+'adoption.json',parent_adoption_utc=now,accepted=False,count_change=0,status_provenance='Terminal lookup after delivered correctness completion; no foreign liveness/body inspection.')
c.update(parent_disposition='FULL_SCOPE_CONTRIBUTION_TECHNICAL_ADOPTED',correctness_condition='DISCHARGED',parent_gate=cg,parent_condition_discharge=close_rel)
a.update(parent_disposition=disp,correctness='PASS',contribution='TECHNICAL',contribution_correctness_condition='DISCHARGED',parent_correctness_adoption=rel+'adoption.json',parent_closure=close_rel,accepted=False,count_change=0)
intake.update(disposition=disp,correctness='PASS',contribution='TECHNICAL',contribution_correctness_condition='DISCHARGED',correctness_adoption=rel+'adoption.json',closure=close_rel,last_adoption_utc=now,next=closure['next'])
for e in intake['reviews']:
    if e['task_index']==700:e.update(status='completed',gate=pg,adoption=rel+'adoption.json')
    if e['task_index']==701:e.update(gate=cg,correctness_condition='DISCHARGED',condition_discharge=close_rel)
s=t['current_work_snapshot'];note='Structural202 closed at entire unchanged frozen scope: correctness PASS and contribution TECHNICAL, condition DISCHARGED, zero count. Campaign 19/20, latest R041, one remaining; publication STOPPED. Distinct discovery next; all foreign records preserved.'
s.update(observed_utc=now,note=note);s['structural202_parent_intake']['disposition']=disp
s['structural202_review_dispatches']=copy.deepcopy(intake['reviews'])
s['structural202_contribution_adoption'].update(gate=cg,condition='DISCHARGED',condition_discharge=close_rel)
s['structural202_correctness_adoption']={'task_index':700,'gate':pg,'adoption':rel+'adoption.json','review_sha256':r['review_sha256'],'count_change':0}
s['structural202_closure']=copy.deepcopy(closure)
if 'active_task_indices' in s:s['active_task_indices']=[i for i in s['active_task_indices'] if i!=700]
if 't3_last_polled_running' in s:s['t3_last_polled_running']=[x for x in s['t3_last_polled_running'] if x!=terminal['taskId']]
t['last_parent_progress']=note
changed=[i for i,x in enumerate(old['tasks']) if t['tasks'][i]!=x];assert changed==[696,700,701] and len(t['tasks'])==len(old['tasks'])
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
keys={'observed_utc','note','structural202_parent_intake','structural202_review_dispatches','structural202_contribution_adoption','active_task_indices','t3_last_polled_running'}
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in keys)
heading='## Structural202 closed: full-scope PASS / TECHNICAL, zero count'
assert heading.encode() not in lr
append='\n'+heading+'\n\nParent adopts independent correctness **PASS** for the entire unchanged frozen statement and submitted proof, relative to stipulated upstream truth. The review verifies finite moment duality/enlargement, kernel-preserving collapse and shift, identity cotype on the single G*, exact all-exponent constants, compact unique lifts, both compact factors, prescribed E and all zero/nonseparable cases. No essential repair or unresolved mathematical obligation remains. See [correctness review](campaigns/2026-10-14/structural-r202-proof-r1/REVIEW.md), [parent assessment](campaigns/2026-10-14/discovery-structural-r202-parent/proof-r1-adoption/assessment.md) and [closure](campaigns/2026-10-14/discovery-structural-r202-parent/closure.json).\n\nThe prior full-scope contribution **TECHNICAL** now has its correctness condition **DISCHARGED**. This closes the original scope permanently with zero acceptance/count; no narrowing, repaired submission or re-review shopping. Read-only checks matched 30 selected review files, four outside files, seven directories and eight copied controls. All 123 author files/ten directories remained unchanged. Reading, formal and source/primary/history limitations remain explicit.\n\n**19/20, latest R041, one remaining; publication STOPPED.** Continue with a distinct discovery family under prospective guards.\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr and ip.read_bytes()==ir
(P/'adoption.json').write_text(json.dumps(adopt,indent=2)+'\n');(P.parent/'closure.json').write_text(json.dumps(closure,indent=2)+'\n')
tmp=registry.with_suffix('.structural202-proof.tmp');tmp.write_text(json.dumps(t,indent=2)+'\n');assert registry.read_bytes()==raw;os.replace(tmp,registry)
assert ledger.read_bytes()==lr;ledger.write_bytes(lr+append.encode());assert ip.read_bytes()==ir;ip.write_text(json.dumps(intake,indent=2)+'\n')
out={'observed_utc':now,'changed_existing_tasks':changed,'new_tasks':0,'all_other_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0,'disposition':disp}
(P/'integration-record.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
