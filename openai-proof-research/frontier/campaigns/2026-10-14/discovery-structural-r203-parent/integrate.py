#!/usr/bin/env python3
"""Intake the immutable full nominee and register two independent reviews."""
from pathlib import Path
import copy,datetime,hashlib,json,os
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();now=datetime.datetime.now(datetime.timezone.utc).isoformat();owner='164b1204-be68-4540-94bb-0b91055c4381'
r=read(P/'replay.json');terminal=read(P/'task-status.json');briefs=read(P/'briefs.json')['reviews'];ds={role:read(P/(role+'-r1-dispatch.json')) for role in ['proof','contribution']}
assert terminal['status']=='completed' and not terminal['hasPendingChildRuns'] and r['author_bytes_modes_unchanged']
for e in briefs:
    d=ds[e['role']];assert d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra' and d['parent_thread']==owner
    assert {x['id']:x['value'] for x in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
    assert sha(C/e['path'])==e['sha256'] and d['brief'].encode()==(C/e['path']).read_bytes()
    assert sha(P/'assessment.md')==e['parent_assessment_sha256'] and sha(P/'questions.md')==e['parent_questions_sha256']
    assert sha(C/'fresh-structural-discovery-r203/packet/FROZEN.md')==e['frozen_statement_sha256']==r['frozen_statement_sha256']
    assert sha(C/'fresh-structural-discovery-r203/packet/DERIVATION.md')==e['author_proof_sha256']==r['author_proof_sha256']
registry=C/'tasks.json';ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md';raw=registry.read_bytes();t=json.loads(raw);old=copy.deepcopy(t);lr=ledger.read_bytes()
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
a=t['tasks'][703];assert a['taskId']==terminal['taskId'] and a['parent_thread']==owner
for k in ['status','workState','hasPendingChildRuns','latestTerminalRunId','latestTerminalStatus','latestTerminalSummary','latestTerminalResultContextTransferId','summary','resultContextTransferId','hasPendingQuestion','pendingApproval','waitTimedOut','observed_utc']:a[k]=terminal[k]
a.update(parent_disposition='FULL_AUTHOR_PROOF_NOMINEE_INDEPENDENT_REVIEWS_PENDING',frozen_statement=True,author_proof_nominee=True,frozen_statement_sha256=r['frozen_statement_sha256'],author_proof_sha256=r['author_proof_sha256'],correctness='PENDING',contribution='PENDING',parent_full_intake_pending=False,parent_intake='discovery-structural-r203-parent/intake.json',parent_intake_utc=now,accepted=False,count_change=0,status_provenance='Terminal lookup after delivered author completion; no foreign or review liveness lookup.')
for e in t['tasks']:
    if e.get('parent_thread') and e.get('taskId') and e.get('status') in ['running','queued','waiting']:
        assert e['parent_thread']!=owner and b'*structural*r203*' in (PROJECT/e['brief']).read_bytes()
reviews=[]
for e in briefs:
    role=e['role'];d=ds[role];assert not any(x.get('taskId')==d['taskId'] for x in t['tasks']);idx=len(t['tasks']);x=copy.deepcopy(d);x.pop('brief')
    x.update(role='review',round=1,review_type='correctness' if role=='proof' else 'contribution',output='frontier/campaigns/2026-10-14/'+e['output']+'/',brief='frontier/campaigns/2026-10-14/'+e['path'],brief_sha256=e['sha256'],brief_bytes=e['bytes'],frozen_statement_sha256=r['frozen_statement_sha256'],author_proof_sha256=r['author_proof_sha256'],parent_count_at_dispatch=19,accepted=False,count_change=0,publication='STOPPED',dispatch_receipt='discovery-structural-r203-parent/'+role+'-r1-dispatch.json',prospective_isolation='discovery-structural-r203-parent/prospective-isolation.json',status_provenance='Actual async dispatch response only; no subsequent liveness poll.',parent_full_intake_pending=True)
    if role=='contribution':x['correctness_condition']='UNDISCHARGED'
    t['tasks'].append(x);reviews.append({'role':'correctness' if role=='proof' else 'contribution','task_index':idx,'taskId':d['taskId'],'status':d['status'],'brief_sha256':e['sha256'],'gate':'PENDING'})
intake={'observed_utc':now,'parent_thread':owner,'task_index':703,'taskId':terminal['taskId'],'disposition':'FULL_AUTHOR_PROOF_NOMINEE_INDEPENDENT_REVIEWS_PENDING','frozen_statement_sha256':r['frozen_statement_sha256'],'author_proof_sha256':r['author_proof_sha256'],'author_anchors':r['anchors'],'correctness':'PENDING','contribution':'PENDING','accepted':False,'count_change':0,'newAccepted':19,'latestAcceptance':'R041','remaining':1,'publication':'STOPPED','assessment_sha256':sha(P/'assessment.md'),'questions_sha256':sha(P/'questions.md'),'artifact_replay':{k:r[k] for k in ['selected_files','selected_directories','selected_bytes','canonical_blobs','formal_file_bindings','source_semantic_extent_bindings','primary_pdf_bindings','primary_text_extent_bindings','history_exact_spans','catalogue_acceptance_spans','root_files','root_directories','author_bytes_modes_unchanged']},'artifact_limit':r['limits'],'copied_controls_passed':5,'reviews':reviews,'next':'Receive independent full-scope correctness and conditional contribution reviews. No grade, acceptance/count, scope narrowing or downstream action inferred.'}
(P/'intake.json').write_text(json.dumps(intake,indent=2)+'\n')
s=t['current_work_snapshot'];note='Structural203 full frozen author-proof nominee received; exact packet/receipts verified. Separate full-scope correctness and conditional contribution reviews dispatched at unchanged scope. No mathematical gate adopted. Campaign19/20 latestR041 one remaining; publicationSTOPPED. Foreign records preserved.'
s.update(observed_utc=now,note=note);s['structural203_parent_intake']={'task_index':703,'disposition':intake['disposition'],'intake':'discovery-structural-r203-parent/intake.json','frozen_statement_sha256':r['frozen_statement_sha256'],'count_change':0};s['structural203_review_dispatches']=reviews
active=[i for i,e in enumerate(t['tasks']) if e.get('parent_thread') and e.get('taskId') and e.get('status') in ['running','queued','waiting']]
s['active_task_indices']=active;s['t3_last_polled_running']=[t['tasks'][i]['taskId'] for i in active if t['tasks'][i]['parent_thread']==owner];s['t3_last_polled_running_note']='Owned reviews only from actual async dispatch responses; foreign shared statuses not queried.';t['last_parent_progress']=note
assert [i for i,x in enumerate(old['tasks']) if t['tasks'][i]!=x]==[703] and len(t['tasks'])==len(old['tasks'])+2
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
allowed={'observed_utc','note','active_task_indices','t3_last_polled_running','t3_last_polled_running_note'}
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in allowed)
heading='## Structural203 full nominee received; independent reviews dispatched'
assert heading.encode() not in lr
append='\n'+heading+'\n\nSource327 discovery submitted a full author proof at unchanged frozen scope: explicit finite Markov witnesses from approximate James arrays in any real normed space, with a chain-state bound depending only on n, original-norm normalization and the frozen quantitative J-convexity corollary. The claimed additional operation is finite subdivision averaging with quantified all-sign merging errors, propagated through paid source chart identities and a finite lattice lift, followed by same-chain coordinate extraction. All Ramsey functions, errors and probability constants remain part of the review scope. No mathematical grade, acceptance or count is adopted. See [statement](campaigns/2026-10-14/fresh-structural-discovery-r203/packet/FROZEN.md), [proof](campaigns/2026-10-14/fresh-structural-discovery-r203/packet/DERIVATION.md) and [parent questions](campaigns/2026-10-14/discovery-structural-r203-parent/questions.md).\n\nParent read all authored mathematical/scope material and verified the selected40files/11directories, five canonical bindings, two formal bindings, four primary PDFs, six primary text extents, three exact original-history spans and five copied controls. All50author-root files/14directories remain unchanged. Packet-selection versus outside-anchor/mode limits, primary access/version limits, semantic false history admission and the comparator sorry remain explicit. Authentication is not semantic reading.\n\nBoth independent review briefs were finalized before either review root/dispatch, preserve the entire original brief and all guards, and prohibit sibling/peer/future-adoption access. The foreign original initial brief already excluded Structural203 before these roots existed; no foreign liveness/body inspection occurred. Contribution correctness remains UNDISCHARGED within that role. **19/20, latest R041, one remaining; publication STOPPED.**\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr
tmp=registry.with_suffix('.structural203-intake.tmp');tmp.write_text(json.dumps(t,indent=2)+'\n');assert registry.read_bytes()==raw;os.replace(tmp,registry)
assert ledger.read_bytes()==lr;ledger.write_bytes(lr+append.encode())
out={'observed_utc':now,'changed_existing_tasks':[703],'new_review_task_indices':[e['task_index'] for e in reviews],'all_old_other_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0}
(P/'integration-record.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
