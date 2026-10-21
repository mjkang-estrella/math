"""One-time structural148 archive and explicit interrupted-task recovery records."""
import datetime, importlib.util, json, subprocess
from pathlib import Path
O=Path(__file__).resolve().parent; B=O.parent; P=B.parents[2]; R=B/'server-restart-2026-10-20-parent'
spec=importlib.util.spec_from_file_location('s148_helpers',O/'replay.py'); h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
def dump(p,d): p.write_text(json.dumps(d,indent=2)+'\n')
def read(p): return json.loads(p.read_text())
def result(p): return read(p)['structuredContent']
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
t=read(B/'tasks.json'); assert len(t['tasks'])==497
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()==read(O/'integration-baseline.json')['head']
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P)
assert h.snap(B/'fresh-structural-discovery-r148')==read(O/'observed-root.json')['root']
intake={'observed_utc':now,'disposition':'PREFREEZE_NO_NOMINEE','scope_frozen':False,'nominee':None,'correctness':'UNREVIEWED','contribution':'UNREVIEWED','assessment_sha256':h.sha(O/'assessment.md'),'external_handoff_anchors':h.ANCHORS,'payload_files':65,'whole_root_files':68,'directories_including_root':27,'source_blobs':14,'primary_pdf_text_pairs':5,'stable_originals':10,'whole_copies':10,'artifact_cases':7,'negative_cases':5,'moment_entry_checks':32258,'accepted':False,'count_change':0,'publication':'STOPPED'}
dump(O/'intake.json',intake)
d=result(O/'task-status.json'); assert d['status']=='completed' and not d['hasPendingChildRuns'] and not d['hasPendingQuestion']
t['tasks'][494].update(d)
t['tasks'][494].update(parent_observed_terminal_utc=now,parent_disposition='PREFREEZE_NO_NOMINEE',scope_frozen=False,nominee=None,correctness='UNREVIEWED',contribution='UNREVIEWED',parent_assessment='discovery-structural-r148-parent/assessment.md',parent_intake='discovery-structural-r148-parent/intake.json',accepted=False,count_change=0,status_provenance='Actual completed original-run task_status with detached anchors and completed parent artifact/finite archive. No independent mathematical or contribution grade.')
target={'providerInstanceId':'codex','model':'gpt-6-astra','options':{'reasoningEffort':'high','serviceTier':'default'}}
observations=[]; chains=[]
for lane,n,old_i in [('arithmetic',113,495),('analytic',143,496)]:
    old=result(R/f'{lane}{n}-cancelled.json'); assert old['status']=='cancelled' and not old['hasPendingChildRuns']
    t['tasks'][old_i].update(old)
    t['tasks'][old_i].update(parent_observed_terminal_utc=now,parent_disposition='SERVER_RESTART_CANCELLED_UNFINISHED',status_provenance='Actual cancelled r1 task_status. No seal, theorem disposition or mathematical gate inferred from partial work.')
    chains.append({'lane':lane,'root':f'fresh-{lane}-discovery-r{n}','original_task_index':old_i,'original_taskId':old['taskId']})
for round_name,suffix in [('r2',''),('r3','-r3')]:
    for chain in chains:
        lane=chain['lane']; n=113 if lane=='arithmetic' else 143
        dispatch_file=R/f'{lane}{n}-recovery{suffix}-dispatch.json'; d=result(dispatch_file)
        assert d['status']=='running' and d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra'
        assert {x['id']:x['value'] for x in d['options']}==target['options']
        brief=R/f'{lane}{n}-recovery{suffix}-brief.txt'; index=len(t['tasks'])
        entry={'observed_utc':now,'target':target,**d,'role':'research','output':chain['root'],'brief':str(brief.relative_to(B)),'brief_sha256':h.sha(brief),'parent_count_at_dispatch':19,'accepted':False,'count_change':0,'publication':'STOPPED','recovery_round':round_name,'original_taskId':chain['original_taskId'],'status_provenance':'Actual async recovery dispatch response; new delegated task, not same original running turn or later liveness poll.'}
        observations.append({'observed_utc':now,'record':str(dispatch_file.relative_to(B)),**d})
        if round_name=='r2':
            stopped=result(R/f'{lane}{n}-r2-interrupted.json'); assert stopped['taskId']==d['taskId'] and stopped['status']=='interrupted' and not stopped['hasPendingChildRuns']
            entry.update(stopped);entry.update(parent_observed_terminal_utc=now,parent_disposition='SECOND_SERVER_RESTART_INTERRUPTED_UNFINISHED',status_provenance='Actual interrupted r2 task_status, no live nested work. This recovery stopped before a complete result; no mathematical gate assigned.')
        chain[round_name+'_task_index']=index;chain[round_name+'_taskId']=d['taskId'];t['tasks'].append(entry)
for chain in chains:
    t['tasks'][chain['original_task_index']]['recovery_taskId']=chain['r2_taskId']
    t['tasks'][chain['r2_task_index']]['recovery_taskId']=chain['r3_taskId']
    t['tasks'][chain['r3_task_index']]['previous_interrupted_taskId']=chain['r2_taskId']
d=result(O/'r149-dispatch.json'); assert d['status']=='running' and d['model']=='gpt-6-astra' and d['providerInstanceId']=='codex'
assert {x['id']:x['value'] for x in d['options']}==target['options']
brief='expanded-target-2026-10-17/fresh-structural-r149-brief.txt'
t['tasks'].append({'observed_utc':now,'target':target,**d,'role':'research','output':'fresh-structural-discovery-r149','brief':brief,'brief_sha256':h.sha(B/brief),'parent_count_at_dispatch':19,'accepted':False,'count_change':0,'publication':'STOPPED','status_provenance':'Actual async delegate_task running response, not later liveness polling.'})
observations.append({'observed_utc':now,'record':'discovery-structural-r148-parent/r149-dispatch.json',**d})
assert len(t['tasks'])==502
msg='Structural148 archived PREFREEZE/no nominee at unchanged i13 biregular-PATTERN/ALLhom target. Host biregularization leaves pattern fixed; native fixed-parameter half-rank transfer on degree>=6 triangular patterns has a positive singular-collapse exponent. Global signed type-map control and uniform all-support singular-mass control at the same deficit scale remain unpaid. This is a route limitation, not upstream audit or impossibility. Parent authenticated65payloads+3envelopes/27directory entries including root,14source blobs,5primary pairs,10stable whole-original copies;7full-copy controls and32258 bounded moment entries passed without changing inputs. No independent math/contribution grade. Two server restarts cancelled r1 and interrupted r2 of Arithmetic113/Analytic143; actual terminal records and distinct r2/r3 recovery dispatches are preserved. Both r3 tasks use their own saved roots/full earlier briefs; their before-recovery inventories are historical observations, not stability inputs after resumption. Structural149 actually dispatched; mutual initial peer exclusions precede its creation. All three latest dispatches verified Codex/Astra/high/default.19/20/latestR041,one remains;publicationSTOPPED.'
t['last_parent_progress']={'observed_utc':now,'note':msg,'newAccepted':19,'remaining':1,'publication':'STOPPED'}
s=t['current_work_snapshot'];s.update(observed_utc=now,note=msg,status_note=msg,fresh_discovery_current=[t['tasks'][i]['output'] for i in [499,500,501]],t3_current_confirmed_running=[t['tasks'][i]['taskId'] for i in [499,500,501]])
s['t3_dispatch_observations'].extend(observations)
s['structural_r148_archive']=intake|{'assessment':'discovery-structural-r148-parent/assessment.md','taskId':t['tasks'][494]['taskId']}
s['server_restart_recovery_20261020']={'observed_utc':now,'records':'server-restart-2026-10-20-parent/','chains':chains,'new_recovery_tasks_not_original_turns':True,'before_root_inventories_are_historical_only':True,'active_root_bodies_not_read_by_parent_after_dispatch':True,'liveness_polling':False,'options_verified':target}
s['structural149_prospective_isolation']={'receipt':'discovery-structural-r148-parent/prospective-isolation.json','both_active_initial_recovery_briefs_exclude_future149':True,'active_peers':['fresh-arithmetic-discovery-r113','fresh-analytic-discovery-r143'],'new149_initial_brief':brief,'new149_initial_brief_sha256':h.sha(B/brief),'new149_initial_future_exclusions':['*arithmetic*r114*','*analytic*r144*'],'liveness_polling':False}
dump(B/'tasks.json',t)
with (P/'frontier/NEW-TEN-2026-10-14.md').open('a') as f: f.write('\n\n## Parent update — structural148 archive and interrupted research recovery\n\n'+msg+' See [parent assessment](campaigns/2026-10-14/discovery-structural-r148-parent/assessment.md). No mathematical gate or acceptance assigned.\n')
root=B/'fresh-structural-discovery-r148'
metadata=['private/source/receipts.json','private/tree-authentication.json','private/history/selected-original-receipts.json','private/primary/receipts.json','private/controls/source-copy-receipts.json']
original=['FINAL.md','REPORT.md','MANIFEST.json']+[f'notes/{n}' for n in ['00-provenance-and-isolation.md','01-prefreeze-calculations.md','02-integrated-reduction-and-gap.md','03-evidence-and-reading-limits.md','control-results.json','diagnostic-results.json']]+[f'code/{n}' for n in ['acquire_source.py','copied_controls.py','diagnostic.py','history_mechanism_scan.py','history_scan.py','seal_once.py','snapshot_selected.py','verify.py']]
parents=['assessment.md','replay.py','integrate.py','integration-check.py','integration-baseline.json','integration-validation.json','observed-root.json','copied-controls.json','diagnostic-replay.json','input-authentication.json','replay.json','intake.json','task-status.json','capabilities.json','r149-dispatch.json','prospective-isolation.json','staging-allowlist.json']
recovery=['integration-baseline.json','capabilities.json','capabilities-r3.json']
for lane,n in [('arithmetic',113),('analytic',143)]:
    recovery += [f'fresh-{lane}-discovery-r{n}-before.json']+[f'{lane}{n}{suffix}' for suffix in ['-cancelled.json','-recovery-brief.txt','-recovery-dispatch.json','-r2-interrupted.json','-before-r3.json','-recovery-r3-brief.txt','-recovery-r3-dispatch.json']]
files=[str((root/n).relative_to(P)) for n in original+metadata]+[str((O/n).relative_to(P)) for n in parents]+[str((R/n).relative_to(P)) for n in recovery]+[str((B/brief).relative_to(P)),str((B/'tasks.json').relative_to(P)),'frontier/NEW-TEN-2026-10-14.md']
dump(O/'staging-allowlist.json',{'files':files,'private_metadata_only':metadata,'recovery_parent_files':recovery,'limits':'Only original structural148 prose/code/calculations, named metadata and parent recovery prompts/status/dispatch/byte inventories. No active recovery-root bodies or protected source/primary/history/search/render/copied bodies.'})
