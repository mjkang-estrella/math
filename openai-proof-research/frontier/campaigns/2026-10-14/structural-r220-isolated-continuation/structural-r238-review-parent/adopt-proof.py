#!/usr/bin/env python3
"""Adopt only full-scope S238 correctness; preserve the pending contribution."""
from pathlib import Path
import copy,datetime,json,os
P=Path(__file__).resolve().parent;C=P.parents[1];PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes());now=datetime.datetime.now(datetime.timezone.utc).isoformat()
status=read(P/'proof-task-status.json');replay=read(P/'proof-replay.json')
assert status['status']=='completed' and status['workState']=='result_available' and not status['hasPendingChildRuns']
assert replay['author_originals_unchanged'] and replay['review_originals_unchanged']
registry=C/'tasks.json';ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md';raw=registry.read_bytes();lr=ledger.read_bytes();t=json.loads(raw);old=copy.deepcopy(t)
author=t['tasks'][798];proof=t['tasks'][801];contribution_before=copy.deepcopy(t['tasks'][802])
assert proof['taskId']==status['taskId'] and proof['parent_thread']=='164b1204-be68-4540-94bb-0b91055c4381' and proof['parent_full_intake_pending']
assert author['parent_disposition']=='FULL_AUTHOR_PROOF_NOMINEE_UNDER_INDEPENDENT_REVIEWS'
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
rel=P.relative_to(C).as_posix();intake_path=rel+'/proof-intake.json'
proof.update(status='completed',workState='result_available',hasPendingChildRuns=False,parent_full_intake_pending=False,parent_disposition='ADOPTED_FULL_SCOPE_PASS',correctness='PASS',correctness_condition='DISCHARGED',parent_intake=intake_path,review_anchors=replay['anchors'],accepted=False,count_change=0,status_provenance='Owned terminal completion read during parent correctness intake; result_available, no pending child runs.')
author.update(parent_disposition='FULL_SCOPE_PASS_CONTRIBUTION_PENDING',correctness='PASS',correctness_condition='DISCHARGED',proof_intake=intake_path,contribution='UNDISCHARGED',accepted=False,count_change=0,proof_scope_note='Entire unchanged frozen S238 statement AND submitted proof: exact local entropy balance for both unchanged October limits, every-time weighted entropy continuity, absolute gain/loss logarithms and vacuum vanishing, local entropy density/flux continuity and equality at every finite endpoint; all source common-data, conservation, admissibility and separation properties preserved. No essential repair or unresolved correctness obligation relative to stipulated Source363 premises.')
note='Structural238 independent correctness review adopted PASS for the entire unchanged statement AND proof, relative to stipulated upstream truth. Contribution remains separately pending and UNDISCHARGED. No acceptance/count:19/20,latestR041,one remaining; publication STOPPED.'
t['last_parent_progress']=note;s=t['current_work_snapshot'];s.update(observed_utc=now,note=note)
if 'active_task_indices' in s:s['active_task_indices']=[i for i in s['active_task_indices'] if i!=801]
if 't3_last_polled_running' in s:s['t3_last_polled_running']=[i for i in s['t3_last_polled_running'] if i!=status['taskId']]
for x in s['structural238_review_dispatch']['reviews']:
 if x['task_index']==801:x['status']='completed';x['parent_disposition']='ADOPTED_FULL_SCOPE_PASS'
s['structural238_author_intake'].update(disposition=author['parent_disposition'],correctness='PASS',correctness_condition='DISCHARGED',contribution='UNDISCHARGED')
s['structural238_proof_parent_intake']={'task_index':801,'author_task_index':798,'correctness':'PASS','scope':'entire unchanged frozen statement AND submitted proof, relative to stipulated source premises','intake':intake_path,'contribution':'pending separate independent review','count_change':0}
assert all(t['tasks'][i]==old['tasks'][i] for i in range(len(t['tasks'])) if i not in (798,801));assert t['tasks'][802]==contribution_before
assert all(t[k]==old[k] for k in old if k not in ('tasks','current_work_snapshot','last_parent_progress'))
allowed={'observed_utc','note','active_task_indices','t3_last_polled_running','structural238_review_dispatch','structural238_author_intake'}
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in allowed)
heading='## Structural238 full-scope correctness PASS adopted; contribution pending';assert heading.encode() not in lr
append='\n## Structural238 full-scope correctness PASS adopted; contribution pending\n\nParent read the complete independent correctness review, objections/resolutions and reading limits, checked them against the unchanged author proof, and adopts **PASS for the entire unchanged frozen statement AND submitted proof**, relative to stipulated Source363 truth. The review checks the simultaneous cold/hot source interfaces, compression-aware distinction between height and mass, every-time deterministic bounds, logarithmic geometric sums, exact outgoing-sphere normalization, gain/loss logarithms and vacuum, weighted entropy continuity, characteristic chain rule, absolute local symmetrization and every-endpoint equality. All source properties and final separation remain those of the unchanged pair. No essential repair or altered hypothesis is required. [Full review](campaigns/2026-10-14/structural-r220-isolated-continuation/structural-r238-proof-r1/packet/REVIEW.md) and [parent assessment](campaigns/2026-10-14/structural-r220-isolated-continuation/structural-r238-review-parent/proof-assessment.md).\n\nRead-only replay matched the three detached anchors and all 13 selected review files plus manifest, with two exact directories. All 34 whole-review files, 83 admitted author files and 14 author directory modes remain unchanged; the broader 167-file author baseline also matches. Parent bound 35 canonical blobs, 51 general read intervals, 31 complete operative source selections and eight primary intervals across five documents. Eight tiny copied controls behaved as expected. Source chronology/recoveries, bounded primary coverage, OCR limits and actual adjacent/editorial exposures remain disclosed. No exhaustive history clearance or proved formal coverage is claimed. Artifact checks do not establish the mathematical verdict.\n\n**Contribution remains pending in its separate independent review.** Its body was not opened or used for correctness adoption, and its task remains unchanged. No acceptance or count is assigned. **19/20, latest R041, one remaining; publication STOPPED.**\n'
intake={'observed_utc':now,'task_index':801,'author_task_index':798,'taskId':status['taskId'],'correctness':'PASS','correctness_condition':'DISCHARGED','scope':'entire unchanged frozen statement AND submitted proof, relative to stipulated source premises','assessment':(P/'proof-assessment.md').relative_to(PROJECT).as_posix(),'artifact_replay':replay,'essential_repairs':[],'unresolved_correctness_obligations':[],'contribution':'UNDISCHARGED; separate review pending','accepted':False,'count_change':0,'publication':'STOPPED'}
(P/'proof-intake.json').write_text(json.dumps(intake,indent=2)+'\n')
assert registry.read_bytes()==raw and ledger.read_bytes()==lr
tmp=registry.with_suffix('.structural238-proof.tmp');tmp.write_text(json.dumps(t,indent=2)+'\n');assert registry.read_bytes()==raw;os.replace(tmp,registry)
assert ledger.read_bytes()==lr;ledger.write_bytes(lr+append.encode())
out={'observed_utc':now,'owned_changed_task_indices':[798,801],'all_other_tasks_unchanged':True,'contribution_task_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0,'append_only_ledger':True}
(P/'proof-adoption-record.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
