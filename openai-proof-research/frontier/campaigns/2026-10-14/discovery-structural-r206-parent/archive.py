#!/usr/bin/env python3
"""Archive delivered Structural206 without nominee, grades or count."""
from pathlib import Path
import copy,datetime,hashlib,json,os
P=Path(__file__).resolve().parent; C=P.parent; PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes()); sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
now=datetime.datetime.now(datetime.timezone.utc).isoformat(); owner='164b1204-be68-4540-94bb-0b91055c4381'; d=read(P/'task-status.json'); r=read(P/'replay.json')
assert d['status']=='completed' and not d['hasPendingChildRuns'] and r['originals_bytes_modes_unchanged']
assert d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra' and {e['id']:e['value'] for e in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
registry=C/'tasks.json'; ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md'; raw=registry.read_bytes(); t=json.loads(raw); old=copy.deepcopy(t); lr=ledger.read_bytes()
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
e=t['tasks'][712]; assert e['taskId']==d['taskId'] and e['parent_thread']==owner and e['parent_full_intake_pending']
assert sha(PROJECT/e['brief'])==e['brief_sha256']=='d2248286583edf1896d1cbcc8608545bce8e5ceac546017544f529ed208dab86'
disposition='ARCHIVED_PREFREEZE_NO_NOMINEE'
intake={'observed_utc':now,'parent_thread':owner,'task_index':712,'taskId':d['taskId'],'disposition':disposition,'source_index':330,'frozen_statement':None,'nominee':False,'correctness':None,'contribution':None,'review_dispatches':[],'accepted':False,'count_change':0,'newAccepted':19,'latestAcceptance':'R041','remaining':1,'publication':'STOPPED','anchors':r['anchors'],'mathematics_sha256':r['mathematics_sha256'],'derivations_sha256':r['derivations_sha256'],'reading_sha256':r['reading_sha256'],'assessment_sha256':sha(P/'assessment.md'),'open_obligations':['A distinct construction or comparison escaping the finite-core cutoff and the stated source-style quadratic certificate obstruction; no such theorem was frozen'],'artifact_replay':{k:r[k] for k in ['verification','root_files','root_directories','originals_bytes_modes_unchanged','canonical_blobs','formal_bindings','primary_pdf_bindings','primary_extent_records','history_exact_spans','direct_input_spans']},'copied_controls_passed':6,'limits':r['limits'],'next':'Distinct discovery only; preserve all guards and use precise navigation aliases. No retrospective rescan, nominee review or mathematical grade.'}
for k in ['status','workState','hasPendingChildRuns','latestTerminalRunId','latestTerminalStatus','latestTerminalSummary','latestTerminalResultContextTransferId','summary','resultContextTransferId','hasPendingQuestion','pendingApproval','waitTimedOut','observed_utc']: e[k]=d[k]
e.update(parent_disposition=disposition,parent_full_intake_pending=False,parent_intake='discovery-structural-r206-parent/intake.json',parent_intake_utc=now,frozen_statement=None,nominee=False,correctness=None,contribution=None,accepted=False,count_change=0,status_provenance='Terminal lookup after delivered owned completion only; no foreign liveness lookup.')
s=t['current_work_snapshot']; note='Structural206 archived PREFREEZE/no nominee: finite-core cutoff, unit-edge interpolation and specified quadratic certificate barrier retained; no additional substantial construction proved. No grades or count. Campaign19/20 latestR041 one remains; publicationSTOPPED. Distinct discovery next; foreign records preserved.'
t['last_parent_progress']=note; s.update(observed_utc=now,note=note)
s['structural206_dispatch'].update(status='completed',disposition=disposition,intake='discovery-structural-r206-parent/intake.json')
s['structural206_parent_intake']={'task_index':712,'disposition':disposition,'intake':'discovery-structural-r206-parent/intake.json','count_change':0}
if 'active_task_indices' in s: s['active_task_indices']=[i for i in s['active_task_indices'] if i!=712]
if 't3_last_polled_running' in s: s['t3_last_polled_running']=[x for x in s['t3_last_polled_running'] if x!=d['taskId']]
changed=[i for i,e in enumerate(old['tasks']) if t['tasks'][i]!=e]; assert changed==[712] and len(t['tasks'])==len(old['tasks'])
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in ['observed_utc','note','structural206_dispatch','active_task_indices','t3_last_polled_running'])
heading='## Structural206 archived: PREFREEZE / no nominee'; assert heading.encode() not in lr
append='\n'+heading+'\n\nParent read and archived the complete [mathematics](campaigns/2026-10-14/fresh-structural-discovery-r206/selected/mathematics.md), early derivations, [handoff](campaigns/2026-10-14/fresh-structural-discovery-r206/selected/FINAL.md), and reading limits. The finite-core logarithmic cutoff gives max(1,||P||)-BAP with exact compact-set quantifiers; unit-edge interpolation and the specific B>4q² certification barrier are retained. No additional substantial construction was proved. No theorem was frozen or nominated; no correctness/contribution grade, review or count is assigned. See [parent assessment](campaigns/2026-10-14/discovery-structural-r206-parent/assessment.md).\n\nRead-only verification matched all80 selected files/eight directories and six copied controls. All186 observed files/31 directories remained unchanged. Eleven canonical blobs, three formal bindings, nine primary PDF bindings, ten primary text selections and four exact original-history spans matched. Reading/recovery limits, unread prerequisites, sorry comparator endpoints and the overly broad supplemental navigation query remain disclosed. Artifact identity is not semantic reading or a mathematical grade. Retain precise aliases and every inherited guard in future work; no retrospective rescan.\n\nPreserve this archive and continue only to a distinct discovery. **19/20, latest R041, one remaining; zero acceptance/count added; publication STOPPED.**\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr
(P/'intake.json').write_text(json.dumps(intake,indent=2)+'\n')
tmp=registry.with_suffix('.structural206-archive.tmp'); tmp.write_text(json.dumps(t,indent=2)+'\n'); assert registry.read_bytes()==raw; os.replace(tmp,registry)
assert ledger.read_bytes()==lr; ledger.write_bytes(lr+append.encode())
out={'observed_utc':now,'changed_existing_tasks':changed,'new_tasks':0,'all_other_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0}
(P/'archive-record.json').write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps(out,indent=2))
