#!/usr/bin/env python3
"""Archive one no-nominee discovery and register the distinct next source."""
from pathlib import Path
import copy
import datetime
import hashlib
import json
import subprocess

p=Path.cwd();b=p/'frontier/campaigns/2026-10-14';o=b/'discovery-arithmetic-r162o-parent'
r=b/'fresh-arithmetic-discovery-r162o';tp=b/'tasks.json';jp=p/'frontier/NEW-TEN-2026-10-14.md'
git=lambda *a:subprocess.check_output(['git',*a])
sha=lambda d:hashlib.sha256(d).hexdigest()
load=lambda f:json.loads(f.read_bytes())
def write(f,x):f.write_text(json.dumps(x,indent=2)+'\n')
def snap(root):
    return {f.relative_to(root).as_posix():{'bytes':f.stat().st_size,'mode':f.stat().st_mode,'sha256':sha(f.read_bytes())}
        for f in root.rglob('*') if f.is_file()}
baseline=load(o/'integration-baseline.json')
assert not git('diff','--cached','--name-only')
for f,h in baseline['protected'].items():assert sha((p/f).read_bytes())==h
assert snap(r)==load(o/'private/root-before.json')
head=git('rev-parse','HEAD').decode().strip()
tb=git('show',head+':openai-proof-research/'+tp.relative_to(p).as_posix())
jb=git('show',head+':openai-proof-research/'+jp.relative_to(p).as_posix())
assert tb==tp.read_bytes() and jb==jp.read_bytes(),'Uncommitted other-owner coordination; do not overwrite.'
base=json.loads(tb);t=copy.deepcopy(base)
assert (t['newAccepted'],t['target'],t['remaining'],t['latestAcceptance'])==(19,20,1,'R041')
terminal=load(o/'task-status.json')['structuredContent'];d=load(o/'arithmetic-r162p-dispatch.json')['structuredContent'];args=load(o/'private/submitted-prompt.json')
for x in [terminal,d]:
    assert (x['providerInstanceId'],x['model'])==('codex','gpt-6-astra')
    assert {z['id']:z['value'] for z in x['options']}=={'reasoningEffort':'high','serviceTier':'default'}
    assert not x['hasPendingChildRuns'] and not x['hasPendingQuestion'] and x['pendingApproval'] is None
assert terminal['status']=='completed' and terminal['workState']=='result_available'
assert d['status']=='running' and d['workState']=='working'
assert [i for i,x in enumerate(t['tasks']) if x.get('taskId')==terminal['taskId']]==[678]
assert not any(x.get('taskId')==d['taskId'] or x.get('clientRequestId')==args['clientRequestId'] for x in t['tasks'])
now=datetime.datetime.now(datetime.timezone.utc).isoformat();v=load(o/'verification.json');intake=load(o/'intake.json')
assert v['status']=='MATCH' and intake['status']=='PREFREEZE_NO_NOMINEE_ARCHIVED'
t['tasks'][678].update(terminal)
t['tasks'][678].update({'observed_utc':now,'parent_disposition':'PREFREEZE_NO_NOMINEE_ARCHIVED',
    'parent_intake':'discovery-arithmetic-r162o-parent/intake.json','correctness_gate':None,
    'contribution_gate':None,'accepted':False,'count_change':0,
    'status_provenance':'Single actual notified terminal task_status response; no pending child/question/approval.'})
prep=load(o/'brief-preparation.json');brief=p/prep['path'];assert len(brief.read_bytes())==prep['bytes'] and sha(brief.read_bytes())==prep['sha256']
new_index=len(t['tasks']);record=copy.deepcopy(d)
record.update({'observed_utc':now,'target':args['target'],'role':'research','title':args['title'],
    'clientRequestId':args['clientRequestId'],'round':1,'parent_thread':'6742db91-d35c-44d0-a762-e5d9232f5177',
    'output':prep['root']+'/','brief':prep['path'],'brief_sha256':prep['sha256'],'brief_bytes':prep['bytes'],
    'submitted_prompt_contains_full_brief':True,
    'source_family_navigation':'DISTINCT Source080; catalogue[134257,135955),two canonical folders,41 descendants/35 blobs; actual build/main.tex and build/paper.tex wrappers. Parent metadata only; full operative/primary/original reading before extended deductions.',
    'round_namespace':'New distinct Source080 inside previously excluded arithmetic162 namespace; no retry/restriction of wave common-graph target,old critical Schrodinger graph-Schatten target,sparse corner or closed technical results.',
    'parent_count_at_dispatch':19,'accepted':False,'count_change':0,'publication':'STOPPED',
    'dispatch_receipt':'discovery-arithmetic-r162o-parent/arithmetic-r162p-dispatch.json',
    'prospective_isolation':'discovery-arithmetic-r162o-parent/prospective-isolation-arithmetic162p.json',
    'status_provenance':'Actual async delegate_task response at dispatch; no polling.'})
observed=load(o/'private/r162p-notified-terminal.json')['structuredContent']
assert observed['taskId']==d['taskId'] and observed['status']=='completed' and not observed['hasPendingChildRuns'] and not observed['hasPendingQuestion'] and observed['pendingApproval'] is None
record.update(observed)
record.update({'parent_disposition':'TERMINAL_AWAITING_MATHEMATICAL_INTAKE','status_provenance':'Original async dispatch running; subsequent notified terminal task_status completed before deferred ledger integration. Mathematical intake pending.'})
t['tasks'].append(record)
note='Arithmetic162o(idx678) archived PREFREEZE/no nominee. Full common-time orthonormal wave density at multiplier<D>^-3/4 log(e+<D>)^-5/8 chi(2^-K D),every rough finite complex L2-orthonormal system and coefficient vector,requires joint uniformity in rank andK on every measurable common graph. Strongest same-graph/full-kernel composition retains(1+K)^1/4;scalar critical endpoint retains square-root rank. Uniform squared-kernel bound remains unpaid;no weaker substitute. Complete canonical but incomplete transitive primary reading,late stronger endpoint,false admission and recovery disclosed. Exact64payload/three-anchor packet,15canonical,62readlog,sixhistory/fourdirect bindings matched;68root files/modes unchanged;three saved copied controls matched. Distinct Source080 exact Sobolev endpoint Schrodinger-convergence discovery dispatched Arithmetic162p,idx'+str(new_index)+',codex/gpt-6-astra/high/default,actual running without pending child/question/approval. All343 inherited guards and5570standing bytes preserved;foreign original initial guards before creation. No foreign live status/body/findings/activity queried. All old scopes and dispositions preserved. Campaign19/20,latestR041,one remains;publication STOPPED.'
note += ' Arithmetic162p subsequently completed PREFREEZE/no nominee before this deferred integration; actual notified terminal receipt registered,mathematical intake next,no current running claim.'
t['last_parent_progress']=note;s=t['current_work_snapshot']
s.update({'observed_utc':now,'note':note,'accepted_count':19,'remaining':1,'publication':'STOPPED'})
s['t3_current_confirmed_running']=[x for x in s.get('t3_current_confirmed_running',[]) if x!=terminal['taskId']]
s['t3_current_confirmed_running']=[x for x in s['t3_current_confirmed_running'] if x!=d['taskId']]
s['arithmetic162p_terminal_pending_intake']={'task_index':new_index,'taskId':d['taskId'],'status':'completed','mathematical_intake_pending':True}
s['arithmetic_r162o_archive']={'task_index':678,'status':'PREFREEZE_NO_NOMINEE','intake':'discovery-arithmetic-r162o-parent/intake.json',
    'full_diagnostic':intake['full_diagnostic'],'unpaid_operation':intake['unpaid_operation'],
    'correctness_gate':None,'contribution_gate':None,'accepted':False,'count_change':0}
s['arithmetic162p_prospective_isolation']={'task_index':new_index,'taskId':d['taskId'],'brief':prep['path'],
    'initial_guards_checked_before_creation':True,'source':'080','catalogue_extent':[134257,135955],
    'status_at_dispatch':'running','foreign_liveness_findings_not_queried':True,'publication':'STOPPED'}
for i,x in enumerate(base['tasks']):
    if i!=678:assert t['tasks'][i]==x
for k,x in base.items():
    if k not in ['tasks','last_parent_progress','current_work_snapshot']:assert t[k]==x
for name in ['prospective-parent-isolation.json','prospective-isolation-arithmetic162p.json']:
    iso=load(o/name)
    for x in iso.get('foreign_original_initial_briefs',iso.get('peer_original_initial_briefs',[])):
        assert sha((p/x['brief']).read_bytes())==x['brief_sha256']
append=('\n\n### Arithmetic162o no-nominee archive; distinct Source080 discovery\n\n'+note+
    '\n\nThe full wave diagnostic retains one common time for the entire density,arbitrary finite complex orthonormal systems,complex coefficients,allK>=1,and all measurable time graphs. Elementary trace duality and measurable grids reduce it to a squared-kernel quadratic bound. Full cross-frequency radial summation and the stronger cone operation give the squared budget1+sum_(k<=K)(1+k)^(-4a)sum_(l<=k)(1+k-l),uniformfora>3/4 but losing(1+K)^1/4 at a=5/8. Scalar critical boundedness is uniforminK but costs sqrt(rank). The log-free common-graph cone bound is sufficient,not proved or asserted necessary. No regular-graph,cutoff,rank or positive-Sobolev-loss substitute;no theorem freeze,author proof,review gate,count or impossibility claim.\n\nParent assessment: frontier/campaigns/2026-10-14/discovery-arithmetic-r162o-parent/assessment.md. Read-only artifact checks matched64packetfiles,3236304bytes,three anchors,15canonical blobs,62hash/interval read records,six original-history andfour completed direct inputs. All68currentroot files/modes unchanged;three saved tiny copied controls matched. Verifier authenticates exact file membership,sizes and hashes;parent checks current mode preservation separately. These are not mathematical gates. Parent read the full derivation,primary/source understanding and limits,not actual canonical/primary proofs. Complete local canonical reading595707nonPDFbytes preceded calculation;late stronger scalar endpoint,comment suppression,unread imported/transitive primary proofs,false Ricci-flow admission,coarse omissions and clipping recoveries remain disclosed.\n\nArithmetic162p is DISTINCT Source080 exact Sobolev endpoint Schrodinger convergence. The entire alln>=2 criticalH^[n/(2(n+1))] convergence theorem,actual Gaussian regularization limit order,one-full-measure/all-time assertions and ALL operative proof operations are stipulated paid. Old r45 critical graph-Schatten and r162o wave scopes remain unpaid as archived;no rename or desired-grade retry. One bounded14000byte catalogue navigation decoded onlytwo numeric titles and080body[134257,135955). Two folders,41descendants/35blobs,actual main.tex/paper.tex wrappers;parent proof reading absent. All343inherited guards and5570standing bytes preserved,with two explicit162p guards. Six exact completed exceptions never widen namespaces. Full operative/primary/original reading precedes extended child work. No nested agents or downstream/public actions. Publication remains stopped.\n').encode()
assert head==git('rev-parse','HEAD').decode().strip() and tb==tp.read_bytes() and jb==jp.read_bytes()
write(o/'coordination-rebase.json',{'initial_head':baseline['head'],'integration_head':head,'rebased':head!=baseline['head'],
    'initial_tasks':baseline['taskCount'],'integration_tasks':len(base['tasks']),
    'changed_task_indices':[678],'new_task_index':new_index,'all_other_tasks_preserved':True,'foreign_live_state_not_queried':True})
write(tp,t);jp.write_bytes(jb+append)
write(o/'private/journal-append.json',{'prior_bytes':len(jb),'prior_sha256':sha(jb),'append_bytes':len(append),'append_sha256':sha(append)})
stage=[tp,jp,brief,r/'REPORT.md',r/'FINAL.md',r/'ANCHORS.json',r/'packet/STATUS.md',r/'packet/verify.py']
stage += [o/x for x in ['assessment.md','intake.json','verification.json','verify-intake.py','integration-baseline.json','pending-integration.json',
    'task-status.json','prospective-parent-isolation.json','prospective-isolation-arithmetic162p.json','capabilities.json',
    'prepare-brief.py','brief-preparation.json','arithmetic-r162p-dispatch.json','manage.py','coordination-rebase.json','integration-guard.json']]
rel=[f.relative_to(p).as_posix() for f in stage]
assert all('/private/' not in x and not x.endswith('MANIFEST.json') for x in rel)
write(o/'integration-guard.json',{'integration_head':head,'changed_task_indices':[678],'new_task_index':new_index,
    'new_taskId':d['taskId'],'all_other_task_records_preserved':True,'other_top_level_preserved_except_progress_snapshot':True,
    'journal_prefix_preserved':True,'root68_files_modes_unchanged':True,
    'disposition':'PREFREEZE_NO_NOMINEE_ARCHIVED','correctness_gate':None,'contribution_gate':None,
    'accepted':False,'count_change':0,'count':19,'remaining':1,'latestAcceptance':'R041','publication':'STOPPED',
    'no_review_or_downstream_for_unproved_diagnostic':True,'new_provider_model_options_checked':True,
    'stage_allowlist':rel,'protected_excluded':baseline['protected']})
assert snap(r)==load(o/'private/root-before.json')
assert head==git('rev-parse','HEAD').decode().strip()
subprocess.run(['git','add','--',*rel],check=True)
assert set(git('diff','--cached','--name-only').decode().splitlines())=={'openai-proof-research/'+x for x in rel}
for x in rel:assert git('show',':openai-proof-research/'+x)==(p/x).read_bytes()
print(json.dumps({'status':'NO_NOMINEE_ARCHIVED_AND_DISTINCT_TASK_REGISTERED','head':head,'staged_files':len(rel),
    'new_task_index':new_index,'count':19,'remaining':1},indent=2))
