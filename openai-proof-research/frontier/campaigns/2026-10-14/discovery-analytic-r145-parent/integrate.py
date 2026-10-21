"""One-time analytic145 no-nominee archive and actual analytic146 dispatch."""
import datetime, importlib.util, json
from pathlib import Path
O=Path(__file__).resolve().parent; B=O.parent; P=B.parents[2]
spec=importlib.util.spec_from_file_location('a145_replay',O/'replay.py')
h=importlib.util.module_from_spec(spec); spec.loader.exec_module(h)
def read(p): return json.loads(p.read_text())
def dump(p,d): p.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
t=read(B/'tasks.json'); assert len(t['tasks'])==509
intake={'observed_utc':now,'disposition':'PREFREEZE_NO_NOMINEE','scope_frozen':False,'nominee':None,'correctness':'UNREVIEWED','contribution':'UNREVIEWED','assessment_sha256':h.sha(O/'assessment.md'),'external_handoff_anchors':h.ANCHORS,'payload_files':57,'whole_root_files':60,'subdirectories':20,'source_blobs':11,'primary_incoming':7,'selected_or_derived_members':13,'tar_members_bound_in_memory':8,'stable_named_originals':22,'mutable_journal':1,'artifact_cases':6,'negative_cases':4,'accepted':False,'count_change':0,'publication':'STOPPED'}
dump(O/'intake.json',intake)
r=read(O/'task-status.json')['structuredContent']
assert r['status']=='completed' and not r['hasPendingChildRuns']
t['tasks'][505].update(r)
t['tasks'][505].update(parent_observed_terminal_utc=now,parent_disposition='PREFREEZE_NO_NOMINEE',scope_frozen=False,nominee=None,correctness='UNREVIEWED',contribution='UNREVIEWED',parent_assessment='discovery-analytic-r145-parent/assessment.md',parent_intake='discovery-analytic-r145-parent/intake.json',accepted=False,count_change=0,status_provenance='Actual completed original task_status with detached anchors and parent artifact archive;no independent mathematical/contribution grade.')
d=read(O/'r146-dispatch.json')['structuredContent']
assert d['status']=='running' and d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra'
assert {e['id']:e['value'] for e in d['options']}=={'reasoningEffort':'high','serviceTier':'default'}
brief='expanded-target-2026-10-17/fresh-analytic-r146-brief.txt'
t['tasks'].append({'observed_utc':now,'target':{'providerInstanceId':'codex','model':'gpt-6-astra','options':{'reasoningEffort':'high','serviceTier':'default'}},**d,'role':'research','output':'fresh-analytic-discovery-r146','brief':brief,'brief_sha256':h.sha(B/brief),'parent_count_at_dispatch':19,'accepted':False,'count_change':0,'publication':'STOPPED','status_provenance':'Actual async delegate_task response,not later liveness polling.'})
msg=('Analytic145 archived PREFREEZE/no nominee:one Source373 family retains old full P,everywhere-positive normalized Schwartz-square density,finite attained Coulomb minimum,EVERY preserving Borel pair and finite-cost approximation. Old preserved calibration has exact binding equality and explicit singular mass2/3 relaxed optimizer;this does not preclude positive full mass. Moving-dual mixture route pays calibrated slack,local squared-gradient control,interior epsilon^(1/5) gradient control,tubes and O(epsilon) exceptional mass. Exact contact branches with strict pullback marginal domination or equally strong selection obstruction remain unpaid;gradient/semiconcavity estimates do not pay Jacobian control. Old fixed-contact positive-density completion remains unpaid;conditional atlas gluing credited. All old scopes/dispositions retained,no supporting nominee or grade. Reading bounds,late primary/history recoveries,initial catalogue overrun,derivative false admissions/late corrected scan and prospective116 exclusion are preserved. Parent matched57payloads+3envelopes/20subdirectories,11canonical sources,7primary incoming/13selected-or-derived members,8tar member comparisons,22stable originals+1mutable journal,and6complete-copy controls/4negatives. Artifact checks are not mathematical gates. Analytic146 actually dispatched Astra high/default,full standing preserved;BOTH active INITIAL briefs exclude146,new146 excludes151/116 and future152/117.19/20/latestR041,one remains;publication STOPPED.')
t['last_parent_progress']={'observed_utc':now,'note':msg,'newAccepted':19,'remaining':1,'publication':'STOPPED'}
s=t['current_work_snapshot']
s.update(observed_utc=now,note=msg,status_note=msg,fresh_discovery_current=[t['tasks'][i]['output'] for i in [507,508,509]],t3_current_confirmed_running=[t['tasks'][i]['taskId'] for i in [507,508,509]])
s['t3_dispatch_observations'].append({'observed_utc':now,'record':'discovery-analytic-r145-parent/r146-dispatch.json',**d})
s['analytic_r145_archive']=intake|{'assessment':'discovery-analytic-r145-parent/assessment.md','taskId':r['taskId']}
s['analytic146_prospective_isolation']={'receipt':'discovery-analytic-r145-parent/prospective-isolation.json','both_active_initial_briefs_exclude_future146':True,'active_peers':['fresh-structural-discovery-r151','fresh-arithmetic-discovery-r116'],'new146_initial_brief':brief,'new146_initial_brief_sha256':h.sha(B/brief),'new146_initial_future_exclusions':['*structural*r152*','*arithmetic*r117*'],'liveness_polling':False}
dump(B/'tasks.json',t)
with (P/'frontier/NEW-TEN-2026-10-14.md').open('a') as f:
    f.write('\n\n## Parent update — analytic145 archive and analytic146 dispatch\n\n'+msg+' See [parent assessment](campaigns/2026-10-14/discovery-analytic-r145-parent/assessment.md). No mathematical gate or acceptance assigned.\n')
root=B/'fresh-analytic-discovery-r145'
original=['AUTH-RECHECK.json','CHECKPOINT.md','CHRONOLOGY.md','CONTROLS.json','DERIVATION.md','FINAL.md','GAPS.md','ISOLATION.md','MANIFEST.json','ORIGINAL-AUTH.json','PRIMARY-AUTH.json','READING-LIMITS.md','REPORT.md','SOURCE-AUTH.json','VERIFY-README.md','verify.py']
programs=['scratch/'+n for n in ['acquire_primary.py','acquire_source.py','authenticate.py','controls.py','scan.py','scan-corrected.py','seal.py']]
parent=['assessment.md','replay.py','integrate.py','integration-check.py','integration-baseline.json','integration-validation.json','observed-root.json','copied-controls.json','input-authentication.json','replay.json','intake.json','task-status.json','capabilities.json','r146-dispatch.json','prospective-isolation.json','staging-allowlist.json']
files=[str((root/n).relative_to(P)) for n in original+programs]+[str((O/n).relative_to(P)) for n in parent]+[str((B/brief).relative_to(P)),str((B/'tasks.json').relative_to(P)),'frontier/NEW-TEN-2026-10-14.md']
dump(O/'staging-allowlist.json',{'files':files,'private_metadata_only':[],'named_original_scratch_programs':programs,'limits':'Original public prose/code and named metadata,including seven explicit original scratch programs only;no private source/primary/history/search/extract/render or copied fixture bodies.'})
