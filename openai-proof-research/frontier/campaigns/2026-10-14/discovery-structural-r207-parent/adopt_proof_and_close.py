#!/usr/bin/env python3
"""Adopt full-scope correctness; discharge contribution condition and close zero-count."""
from pathlib import Path
import copy,datetime,hashlib,json,os
P=Path(__file__).resolve().parent; C=P.parent; PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes()); sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
d=read(P/'proof-task-status.json'); r=read(P/'proof-replay.json'); owner='164b1204-be68-4540-94bb-0b91055c4381'; now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert d['status']=='completed' and not d['hasPendingChildRuns'] and r['review_originals_bytes_modes_unchanged'] and r['all303_author_files80_directories_unchanged'] and r['contribution44files12directories_unchanged']
assert d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra' and {e['id']:e['value'] for e in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
registry=C/'tasks.json'; ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md'; raw=registry.read_bytes(); t=json.loads(raw); old=copy.deepcopy(t); lr=ledger.read_bytes(); ir=(P/'intake.json').read_bytes(); intake=json.loads(ir)
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
e=t['tasks'][716]; author=t['tasks'][714]; contrib=t['tasks'][717]
assert e['taskId']==d['taskId'] and e['parent_thread']==author['parent_thread']==contrib['parent_thread']==owner
assert e['parent_full_intake_pending'] and author['correctness']=='PENDING' and author['contribution']=='TECHNICAL' and contrib['correctness']=='UNDISCHARGED'
assert sha(PROJECT/e['brief'])==e['brief_sha256']=='46403994eb8c175d4bd5efe601d183d8d04959cee264242095e8df4f5255223b'
ci=read(P/'contribution-intake.json'); assert ci['condition_status']=='UNDISCHARGED' and ci['frozen_sha256']==author['frozen_sha256']==e['frozen_sha256'] and ci['proof_sha256']==author['proof_sha256']==e['proof_sha256']
disposition='CLOSED_PASS_TECHNICAL_ZERO_COUNT'
adoption={'observed_utc':now,'parent_thread':owner,'review_task_index':716,'author_task_index':714,'taskId':d['taskId'],'disposition':disposition,'correctness':'PASS','correctness_scope':'Entire unchanged frozen statement and submitted proof, relative to stipulated upstream truth','contribution':'TECHNICAL','contribution_condition_status':'DISCHARGED','contribution_intake':'discovery-structural-r207-parent/contribution-intake.json','frozen_sha256':author['frozen_sha256'],'proof_sha256':author['proof_sha256'],'anchors':r['anchors'],'review_sha256':r['review_sha256'],'assessment_sha256':sha(P/'proof-assessment.md'),'artifact_replay':r,'essential_correctness_obligations_remaining':False,'accepted':False,'count_change':0,'newAccepted':19,'latestAcceptance':'R041','remaining':1,'publication':'STOPPED','next':'Distinct discovery family; no edits, narrowing, renaming or grade shopping for Structural207.'}
for k in ['status','workState','hasPendingChildRuns','latestTerminalRunId','latestTerminalStatus','latestTerminalSummary','latestTerminalResultContextTransferId','summary','resultContextTransferId','hasPendingQuestion','pendingApproval','waitTimedOut','observed_utc']: e[k]=d[k]
e.update(parent_disposition='FULL_SCOPE_PASS_ADOPTED',parent_full_intake_pending=False,parent_intake='discovery-structural-r207-parent/proof-intake.json',parent_intake_utc=now,correctness='PASS',accepted=False,count_change=0,status_provenance='Terminal lookup after delivered owned completion only; no foreign liveness lookup.')
author.update(parent_disposition=disposition,correctness='PASS',contribution_condition_status='DISCHARGED',proof_intake='discovery-structural-r207-parent/proof-intake.json',closure='discovery-structural-r207-parent/closure.json')
contrib.update(parent_contribution_condition_status='DISCHARGED',parent_condition_discharge='discovery-structural-r207-parent/closure.json')
intake.update(disposition=disposition,correctness='PASS',contribution_condition_status='DISCHARGED',proof_intake='discovery-structural-r207-parent/proof-intake.json',closure='discovery-structural-r207-parent/closure.json',next=adoption['next'])
def mark(entries):
    for x in entries:
        if x['task_index']==716: x.update(status='completed',correctness='PASS')
        if x['task_index']==717: x.update(parent_condition_status='DISCHARGED')
mark(author['review_dispatches']); mark(intake['review_dispatches']); s=t['current_work_snapshot']; mark(s['structural207_review_dispatches'])
for key in ['structural207_dispatch','structural207_parent_intake']: s[key]['disposition']=disposition
s['structural207_contribution_adoption'].update(condition_status='DISCHARGED',discharge='discovery-structural-r207-parent/closure.json')
s['structural207_closure']={'disposition':disposition,'correctness':'PASS','contribution':'TECHNICAL','condition_status':'DISCHARGED','closure':'discovery-structural-r207-parent/closure.json','count_change':0}
note='Structural207 CLOSED full unchanged-scope PASS/TECHNICAL; parent discharges contribution correctness condition. Zero count; no reopening. Campaign19/20 latestR041 one remains; publicationSTOPPED. Foreign records preserved.'
t['last_parent_progress']=note; s.update(observed_utc=now,note=note)
if 'active_task_indices' in s: s['active_task_indices']=[i for i in s['active_task_indices'] if i!=716]
if 't3_last_polled_running' in s: s['t3_last_polled_running']=[x for x in s['t3_last_polled_running'] if x!=d['taskId']]
changed=[i for i,x in enumerate(old['tasks']) if t['tasks'][i]!=x]; assert changed==[714,716,717] and len(t['tasks'])==len(old['tasks'])
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
allowed=['observed_utc','note','active_task_indices','t3_last_polled_running','structural207_review_dispatches','structural207_dispatch','structural207_parent_intake','structural207_contribution_adoption']
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in allowed)
heading='## Structural207 closed: full-scope PASS / TECHNICAL, zero count'; assert heading.encode() not in lr
append='\n'+heading+'\n\nParent read and adopts the complete [correctness review](campaigns/2026-10-14/structural-r207-proof-r1/packet/REVIEW.md): **PASS for the entire unchanged frozen statement and submitted proof**, relative to stipulated upstream truth. All18 objections are resolved, including mixed-law first-moment compactness, conditional independence, closed-cofinite quantifiers, closure-only bounded-law necessity and the exact equivalent-norm endpoint. No repair or narrowing is required. See [parent assessment](campaigns/2026-10-14/discovery-structural-r207-parent/proof-assessment.md).\n\nThe independent **TECHNICAL** contribution verdict was conditional on correctness of that same whole scope. Parent now discharges the condition; the contribution role’s historical UNDISCHARGED correctness status and all sealed texts remain unchanged. No substantial-contribution acceptance is assigned.\n\nExplicit-anchor replay matched26reviewfiles/sevendirectories and146authorfiles/39directories; all observed author and both review roots stayed unchanged. Seven tiny parent-local copied controls passed their expected outcomes. Source/primary/history reading limits and missing formal endpoint coverage remain disclosed; artifact identity supplies no mathematical or inherited semantic-reading credit.\n\n**19/20, latest R041, one remaining; publication STOPPED.** Continue with a distinct discovery family, without reopening Structural207.\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr and (P/'intake.json').read_bytes()==ir
for name,value in [('proof-intake.json',adoption),('closure.json',adoption)]: (P/name).write_text(json.dumps(value,indent=2)+'\n')
tmp=registry.with_suffix('.structural207-proof.tmp'); tmp.write_text(json.dumps(t,indent=2)+'\n'); assert registry.read_bytes()==raw; os.replace(tmp,registry)
assert ledger.read_bytes()==lr; ledger.write_bytes(lr+append.encode()); (P/'intake.json').write_text(json.dumps(intake,indent=2)+'\n')
out={'observed_utc':now,'changed_existing_tasks':changed,'new_tasks':0,'all_other_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'contribution_review_historical_correctness_unchanged':True,'count_change':0}
(P/'proof-adoption-record.json').write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps(out,indent=2))
