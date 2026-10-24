#!/usr/bin/env python3
"""Register the unchanged full-scope author nominee, without adopting grades."""
from pathlib import Path
import copy,datetime,hashlib,json,os
P=Path(__file__).resolve().parent; C=P.parent; PROJECT=C.parents[2]
read=lambda p:json.loads(p.read_bytes()); sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
d=read(P/'task-status.json'); r=read(P/'replay.json'); owner='164b1204-be68-4540-94bb-0b91055c4381'; now=datetime.datetime.now(datetime.timezone.utc).isoformat()
assert d['status']=='completed' and not d['hasPendingChildRuns'] and r['originals_bytes_modes_unchanged']
assert d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra' and {e['id']:e['value'] for e in d['options']}=={'reasoningEffort':'xhigh','serviceTier':'default'}
registry=C/'tasks.json'; ledger=PROJECT/'frontier/NEW-TEN-2026-10-14.md'; raw=registry.read_bytes(); t=json.loads(raw); old=copy.deepcopy(t); lr=ledger.read_bytes()
assert (t['newAccepted'],t['latestAcceptance'],t['remaining'])==(19,'R041',1)
e=t['tasks'][714]; assert e['taskId']==d['taskId'] and e['parent_thread']==owner and e['parent_full_intake_pending']
assert sha(PROJECT/e['brief'])==e['brief_sha256']=='f8d3a8c870d9dcfe9fbd12dfabaf2ebbbec26dca51d8abdf271b73812f317541'
disposition='FULL_SCOPE_AUTHOR_PROOF_NOMINEE_PENDING_INDEPENDENT_REVIEWS'
intake={'observed_utc':now,'parent_thread':owner,'task_index':714,'taskId':d['taskId'],'disposition':disposition,'source_index':331,'frozen_statement':'fresh-structural-discovery-r207/packet/FROZEN.md','frozen_sha256':r['frozen_sha256'],'proof':'fresh-structural-discovery-r207/packet/AUTHOR-PROOF.md','proof_sha256':r['proof_sha256'],'nominee':True,'correctness':'PENDING','contribution':'PENDING','review_dispatches':[],'accepted':False,'count_change':0,'newAccepted':19,'latestAcceptance':'R041','remaining':1,'publication':'STOPPED','anchors':r['anchors'],'assessment_sha256':sha(P/'assessment.md'),'artifact_replay':{k:r[k] for k in ['verification','root_files','root_directories','originals_bytes_modes_unchanged','canonical_blobs','formal_bindings','primary_pdf_bindings','extent_metadata_bindings','history_exact_spans','administrative_history_selection_not_reread','direct_input_spans']},'copied_controls_passed':6,'limits':r['limits'],'next':'Separate independent correctness and contribution reviews of the entire unchanged scope; no grades adopted.'}
for k in ['status','workState','hasPendingChildRuns','latestTerminalRunId','latestTerminalStatus','latestTerminalSummary','latestTerminalResultContextTransferId','summary','resultContextTransferId','hasPendingQuestion','pendingApproval','waitTimedOut','observed_utc']: e[k]=d[k]
e.update(parent_disposition=disposition,parent_full_intake_pending=False,parent_intake='discovery-structural-r207-parent/intake.json',parent_intake_utc=now,nominee=True,frozen_statement=intake['frozen_statement'],frozen_sha256=r['frozen_sha256'],proof_sha256=r['proof_sha256'],correctness='PENDING',contribution='PENDING',accepted=False,count_change=0,status_provenance='Terminal lookup after delivered owned completion only; no foreign liveness lookup.')
s=t['current_work_snapshot']; note='Structural207 full-scope author-proof nominee received and identity-verified at unchanged compact-law product-tree scope. Separate correctness/contribution reviews pending; no grade or count adopted. Campaign19/20 latestR041 one remains; publicationSTOPPED. Foreign records preserved.'
t['last_parent_progress']=note; s.update(observed_utc=now,note=note)
s['structural207_dispatch'].update(status='completed',disposition=disposition,intake='discovery-structural-r207-parent/intake.json')
s['structural207_parent_intake']={'task_index':714,'disposition':disposition,'intake':'discovery-structural-r207-parent/intake.json','frozen_sha256':r['frozen_sha256'],'count_change':0}
if 'active_task_indices' in s: s['active_task_indices']=[i for i in s['active_task_indices'] if i!=714]
if 't3_last_polled_running' in s: s['t3_last_polled_running']=[x for x in s['t3_last_polled_running'] if x!=d['taskId']]
changed=[i for i,e in enumerate(old['tasks']) if t['tasks'][i]!=e]; assert changed==[714] and len(t['tasks'])==len(old['tasks'])
assert all(t[k]==old[k] for k in old if k not in ['tasks','current_work_snapshot','last_parent_progress'])
assert all(s[k]==v for k,v in old['current_work_snapshot'].items() if k not in ['observed_utc','note','structural207_dispatch','active_task_indices','t3_last_polled_running'])
heading='## Structural207 full-scope author-proof nominee: compact-law product-tree criterion'; assert heading.encode() not in lr
append='\n'+heading+'\n\nParent read the unchanged [frozen statement](campaigns/2026-10-14/fresh-structural-discovery-r207/packet/FROZEN.md), [complete author proof](campaigns/2026-10-14/fresh-structural-discovery-r207/packet/AUTHOR-PROOF.md), derivations, checks and reading limits. The proposed theorem characterizes the inherited AMUC norm of one parent-dependent product tree using every law in a compact first-Wasserstein closure, with first moments only, an explicit law-dependent modulus and a full equivalent-norm AUC obstruction. All frozen conclusions and submitted proof remain for separate independent correctness and contribution reviews. Neither grade is adopted. See [parent assessment](campaigns/2026-10-14/discovery-structural-r207-parent/assessment.md).\n\nExact replay matched146 packet files/39 directories and six copied controls. All303 observed author files/80 directories remained unchanged. All99 canonical blobs, eight formal bindings, seven primary PDFs,109 extent records and two eligible original-history spans matched. The administrative false-admission original section was not re-read. These are artifact checks, not semantic reading or mathematical grades. Primary-access, partial-reading, sorry comparator and isolation limits remain disclosed.\n\n**Author-proof nominee only;19/20, latest R041, one remaining; zero acceptance/count added; publication STOPPED.**\n'
assert registry.read_bytes()==raw and ledger.read_bytes()==lr
(P/'intake.json').write_text(json.dumps(intake,indent=2)+'\n')
tmp=registry.with_suffix('.structural207-intake.tmp'); tmp.write_text(json.dumps(t,indent=2)+'\n'); assert registry.read_bytes()==raw; os.replace(tmp,registry)
assert ledger.read_bytes()==lr; ledger.write_bytes(lr+append.encode())
out={'observed_utc':now,'changed_existing_tasks':changed,'new_tasks':0,'all_other_tasks_unchanged':True,'foreign_snapshot_entries_preserved':True,'count_change':0}
(P/'intake-record.json').write_text(json.dumps(out,indent=2)+'\n'); print(json.dumps(out,indent=2))
