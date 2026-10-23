#!/usr/bin/env python3
"""Archive one delivered PREFREEZE round; assign no mathematical gate or count."""
from pathlib import Path
import copy,datetime,hashlib,json,os
P=Path(__file__).resolve().parent;C=P.parent;PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
now=datetime.datetime.now(datetime.timezone.utc).isoformat();owner='164b1204-be68-4540-94bb-0b91055c4381';d=read(P/'task-status.json');r=read(P/'replay.json')
assert d['status']=='completed' and not d['hasPendingChildRuns'] and r['originals_bytes_modes_unchanged']
assert d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra' and {e['id']:e['value'] for e in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
registry=C/'tasks.json';ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md';raw=registry.read_bytes();t=json.loads(raw);old=copy.deepcopy(t);lr=ledger.read_bytes()
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
e=t['tasks'][708];assert e['taskId']==d['taskId'] and e['parent_thread']==owner and e['parent_full_intake_pending']
assert sha(PROJECT/e['brief'])==e['brief_sha256']=='a86d438af1c912bafbc52ae1359e43dd8287ae9827f121d12f6dd8fe37856d56'
disposition='ARCHIVED_PREFREEZE_NO_NOMINEE'
intake={'observed_utc':now,'parent_thread':owner,'task_index':708,'taskId':d['taskId'],'disposition':disposition,'source_index':328,'frozen_statement':None,'nominee':False,'correctness':None,'contribution':None,'review_dispatches':[],'accepted':False,'count_change':0,'newAccepted':19,'latestAcceptance':'R041','remaining':1,'publication':'STOPPED','anchors':r['anchors'],'derivations_sha256':r['derivations_sha256'],'assessment_sha256':sha(P/'assessment.md'),'open_obligations':['Unrestricted reflexive asymptotic fixed-point extension','Orbit-limit fixed-point property under the contemplated hypotheses','Approximate fixed points inside the same minimal orbit-limit domain','Diameter-one detection and compatible nearly nonexpansive tree estimate'],'artifact_replay':{k:r[k] for k in ['verification','manifest_additional_file','selected_content_bytes','root_files','root_directories','originals_bytes_modes_unchanged','outside_copies_matched_selected_files','canonical_blobs','formal_bindings','source_text_read_extent_bindings','primary_text_bindings','primary_pdf_bindings','renders_integrity_only','history_exact_spans','catalogue_acceptance_spans']},'copied_controls_passed':5,'limits':r['limits'],'next':'Distinct discovery only; preserve this prefreeze archive and all closed scopes. No nominee review or grade.'}
for k in ['status','workState','hasPendingChildRuns','latestTerminalRunId','latestTerminalStatus','latestTerminalSummary','latestTerminalResultContextTransferId','summary','resultContextTransferId','hasPendingQuestion','pendingApproval','waitTimedOut','observed_utc']:e[k]=d[k]
e.update(parent_disposition=disposition,parent_full_intake_pending=False,parent_intake='discovery-structural-r204-parent/intake.json',parent_intake_utc=now,frozen_statement=None,nominee=False,correctness=None,contribution=None,accepted=False,count_change=0,status_provenance='Terminal lookup after delivered owned completion only; no foreign liveness lookup.')
s=t['current_work_snapshot'];note='Structural204 archived PREFREEZE/no nominee: integrated source/classical reductions and concrete obstruction calculations retained, general reflexive asymptotic/orbit-limit and same-domain detector obligations unresolved. No mathematical grades or count. Campaign19/20 latestR041 one remains; publicationSTOPPED. Distinct discovery next; foreign records preserved.'
t['last_parent_progress']=note;s.update(observed_utc=now,note=note)
s['structural204_dispatch'].update(status='completed',disposition=disposition,intake='discovery-structural-r204-parent/intake.json')
s['structural204_parent_intake']={'task_index':708,'disposition':disposition,'intake':'discovery-structural-r204-parent/intake.json','count_change':0}
if 'active_task_indices' in s:s['active_task_indices']=[i for i in s['active_task_indices'] if i!=708]
if 't3_last_polled_running' in s:s['t3_last_polled_running']=[x for x in s['t3_last_polled_running'] if x!=d['taskId']]
changed=[i for i,e in enumerate(old['tasks']) if t['tasks'][i]!=e];assert changed==[708] and len(t['tasks'])==len(old['tasks'])
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in ['observed_utc','note','structural204_dispatch','active_task_indices','t3_last_polled_running'])
heading='## Structural204 archived: PREFREEZE / no nominee'
assert heading.encode() not in lr
append='\n'+heading+'\n\nParent read and archived the complete [derivations](campaigns/2026-10-14/fresh-structural-discovery-r204/packet/DERIVATIONS.md) and [handoff](campaigns/2026-10-14/fresh-structural-discovery-r204/packet/FINAL.md). The source/Wisnicki ultrapower and local-correction construction, credited Bruck and orbit-limit retraction machinery, explicit ultrapower and weak-compression obstructions, and near-resolvent estimates are preserved. The general reflexive asymptotic extension, orbit-limit FPP, same-domain approximate fixed points and diameter-one detector remain unproved. No statement was frozen or nominated, and no correctness/contribution reviews or grades are assigned. See [parent assessment](campaigns/2026-10-14/discovery-structural-r204-parent/assessment.md).\n\nRead-only verification matched 50 selected payload files plus the separately anchored MANIFEST, seven directories and five copied controls; all 125 observed files/28 directories remained unchanged. All12canonical and two formal bindings matched. Cached Bruck text, physically clipped manuscript lines, scoped original history and sorry comparator limitations remain explicit. Artifact identity does not inherit semantic reading or supply a mathematical gate.\n\nPreserve this archive and continue only to a distinct discovery. **19/20, latest R041, one remaining; zero acceptance/count added; publication STOPPED.**\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr
(P/'intake.json').write_text(json.dumps(intake,indent=2)+'\n')
tmp=registry.with_suffix('.structural204-archive.tmp');tmp.write_text(json.dumps(t,indent=2)+'\n');assert registry.read_bytes()==raw;os.replace(tmp,registry)
assert ledger.read_bytes()==lr;ledger.write_bytes(lr+append.encode())
out={'observed_utc':now,'changed_existing_tasks':changed,'new_tasks':0,'all_other_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0}
(P/'archive-record.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
