#!/usr/bin/env python3
"""Adopt conditional TECHNICAL only; leave correctness independently pending."""
from pathlib import Path
import copy,datetime,hashlib,json,os
P=Path(__file__).resolve().parent; C=P.parent; PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes()); sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
d=read(P/'contribution-task-status.json'); r=read(P/'contribution-replay.json'); owner='164b1204-be68-4540-94bb-0b91055c4381'; now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert d['status']=='completed' and not d['hasPendingChildRuns'] and r['review_originals_bytes_modes_unchanged'] and r['all303_author_files80_directories_unchanged']
assert d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra' and {e['id']:e['value'] for e in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
registry=C/'tasks.json'; ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md'; raw=registry.read_bytes(); t=json.loads(raw); old=copy.deepcopy(t); lr=ledger.read_bytes(); ir=(P/'intake.json').read_bytes(); intake=json.loads(ir)
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
e=t['tasks'][717]; author=t['tasks'][714]
assert e['taskId']==d['taskId'] and e['parent_thread']==owner and e['parent_full_intake_pending'] and author['correctness']=='PENDING' and author['contribution']=='PENDING'
assert sha(PROJECT/e['brief'])==e['brief_sha256']=='8778223a157ad94ac218c97cb1cd338cd1769bae26207411de624800459e7cd4'
condition='Full correctness of the entire unchanged frozen statement and submitted proof'
disposition='CONTRIBUTION_TECHNICAL_CONDITIONAL_CORRECTNESS_PENDING'
adoption={'observed_utc':now,'parent_thread':owner,'review_task_index':717,'author_task_index':714,'taskId':d['taskId'],'disposition':disposition,'contribution':'TECHNICAL','conditional_on':condition,'condition_status':'UNDISCHARGED','correctness':'PENDING','frozen_sha256':author['frozen_sha256'],'proof_sha256':author['proof_sha256'],'anchors':r['anchors'],'review_sha256':r['review_sha256'],'assessment_sha256':sha(P/'contribution-assessment.md'),'artifact_replay':{k:r[k] for k in ['verification','author_verification','root_files','root_directories','review_originals_bytes_modes_unchanged','all303_author_files80_directories_unchanged','canonical_blobs','formal_bindings','author_extent_metadata_bindings','new_probability_access_bindings','new_probability_extent_bindings','render_integrity_only']},'copied_controls_passed':5,'control_verifier_change':r['control_verifier_change'],'limits':r['limits'],'essential_contribution_comparison_remaining':False,'accepted':False,'count_change':0,'newAccepted':19,'latestAcceptance':'R041','remaining':1,'publication':'STOPPED','next':'Await independent full-scope correctness result; no narrowing, grade shopping, author edits or peer-result transfer.'}
for k in ['status','workState','hasPendingChildRuns','latestTerminalRunId','latestTerminalStatus','latestTerminalSummary','latestTerminalResultContextTransferId','summary','resultContextTransferId','hasPendingQuestion','pendingApproval','waitTimedOut','observed_utc']: e[k]=d[k]
e.update(parent_disposition='CONDITIONAL_TECHNICAL_ADOPTED',parent_full_intake_pending=False,parent_intake='discovery-structural-r207-parent/contribution-intake.json',parent_intake_utc=now,contribution='TECHNICAL',contribution_condition=condition,contribution_condition_status='UNDISCHARGED',correctness='UNDISCHARGED',accepted=False,count_change=0,status_provenance='Terminal lookup after delivered owned completion only; no correctness or foreign liveness lookup.')
author.update(parent_disposition=disposition,contribution='TECHNICAL',contribution_condition=condition,contribution_condition_status='UNDISCHARGED',contribution_intake='discovery-structural-r207-parent/contribution-intake.json')
intake.update(disposition=disposition,contribution='TECHNICAL',contribution_condition=condition,contribution_condition_status='UNDISCHARGED',contribution_intake='discovery-structural-r207-parent/contribution-intake.json')
def mark(entries):
    for x in entries:
        if x['taskId']==d['taskId']: x.update(status='completed',contribution='TECHNICAL',condition_status='UNDISCHARGED')
mark(author['review_dispatches']); mark(intake['review_dispatches'])
s=t['current_work_snapshot']; mark(s['structural207_review_dispatches'])
s['structural207_dispatch']['disposition']=disposition; s['structural207_parent_intake']['disposition']=disposition
s['structural207_contribution_adoption']={'task_index':717,'contribution':'TECHNICAL','conditional_on':condition,'condition_status':'UNDISCHARGED','intake':'discovery-structural-r207-parent/contribution-intake.json','count_change':0}
note='Structural207 contribution TECHNICAL adopted conditionally at entire unchanged scope; complete compatible reduction retained. Correctness remains independently pending/UNDISCHARGED; no correctness-role poll or result transfer. Zero count. Campaign19/20 latestR041 one remains; publicationSTOPPED. Foreign records preserved.'
t['last_parent_progress']=note; s.update(observed_utc=now,note=note)
if 'active_task_indices' in s: s['active_task_indices']=[i for i in s['active_task_indices'] if i!=717]
if 't3_last_polled_running' in s: s['t3_last_polled_running']=[x for x in s['t3_last_polled_running'] if x!=d['taskId']]
changed=[i for i,e in enumerate(old['tasks']) if t['tasks'][i]!=e]; assert changed==[714,717] and len(t['tasks'])==len(old['tasks']) and t['tasks'][716]==old['tasks'][716]
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
allowed=['observed_utc','note','active_task_indices','t3_last_polled_running','structural207_review_dispatches','structural207_dispatch','structural207_parent_intake']
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in allowed)
heading='## Structural207 contribution adopted conditionally: TECHNICAL; correctness pending'; assert heading.encode() not in lr
append='\n'+heading+'\n\nParent read the complete [independent contribution review](campaigns/2026-10-14/structural-r207-contribution-r1/packet/REVIEW.md), working notes and reading/access limits and adopts **TECHNICAL conditional on full correctness of the entire unchanged frozen statement and submitted proof**. The review supplies a complete compatible mixed-law/first-moment reduction, carrying the exact Theta/C bound, closure-only bounded-law necessity, both midpoint conventions and full equivalent-norm zero interval. Durrett’s actual root-tightness/compound-Poisson operations plus an explicit logarithmic estimate pay the required symmetric nonidentical-array step; source6 and source2 supply the remaining compatible interfaces. Generic-monograph access failures, partial/retrospective readings and scoped-history limits remain disclosed. No essential contribution comparison remains unresolved. See [parent assessment](campaigns/2026-10-14/discovery-structural-r207-parent/contribution-assessment.md).\n\nReview20files/two directories and author146files/39directories matched explicit-anchor verification; all44 observed review files/12directories and303authorfiles/80directories stayed unchanged. Five parent-local tiny copied controls behaved as expected; only the copied verifier’s EXCLUSIVE path constant was rerooted for those controls, while the unchanged sealed verifier separately passed the actual review. Artifact identity is not mathematical validation or inherited semantic reading.\n\nCorrectness remains PENDING/UNDISCHARGED under its separate commissioned review; it was not polled or sent this result. No scope change, acceptance or count. **19/20, latest R041, one remaining; publication STOPPED.**\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr and (P/'intake.json').read_bytes()==ir
(P/'contribution-intake.json').write_text(json.dumps(adoption,indent=2)+'\n')
tmp=registry.with_suffix('.structural207-contribution.tmp'); tmp.write_text(json.dumps(t,indent=2)+'\n'); assert registry.read_bytes()==raw; os.replace(tmp,registry)
assert ledger.read_bytes()==lr; ledger.write_bytes(lr+append.encode()); (P/'intake.json').write_text(json.dumps(intake,indent=2)+'\n')
out={'observed_utc':now,'changed_existing_tasks':changed,'new_tasks':0,'correctness_task_unchanged':True,'all_other_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0}
(P/'contribution-adoption-record.json').write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps(out,indent=2))
