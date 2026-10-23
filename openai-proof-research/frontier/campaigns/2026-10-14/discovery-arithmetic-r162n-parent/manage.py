#!/usr/bin/env python3
"""Archive one no-nominee discovery and register the distinct next source."""
from pathlib import Path
import copy
import datetime
import hashlib
import json
import subprocess

p=Path.cwd();b=p/'frontier/campaigns/2026-10-14';o=b/'discovery-arithmetic-r162n-parent'
r=b/'fresh-arithmetic-discovery-r162n';tp=b/'tasks.json';jp=p/'frontier/NEW-TEN-2026-10-14.md'
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
terminal=load(o/'task-status.json')['structuredContent'];d=load(o/'arithmetic-r162o-dispatch.json')['structuredContent'];args=load(o/'private/submitted-prompt.json')
for x in [terminal,d]:
    assert (x['providerInstanceId'],x['model'])==('codex','gpt-6-astra')
    assert {z['id']:z['value'] for z in x['options']}=={'reasoningEffort':'high','serviceTier':'default'}
    assert not x['hasPendingChildRuns'] and not x['hasPendingQuestion'] and x['pendingApproval'] is None
assert terminal['status']=='completed' and terminal['workState']=='result_available'
assert d['status']=='running' and d['workState']=='working'
assert [i for i,x in enumerate(t['tasks']) if x.get('taskId')==terminal['taskId']]==[676]
assert not any(x.get('taskId')==d['taskId'] or x.get('clientRequestId')==args['clientRequestId'] for x in t['tasks'])
now=datetime.datetime.now(datetime.timezone.utc).isoformat();v=load(o/'verification.json');intake=load(o/'intake.json')
assert v['status']=='MATCH' and intake['status']=='PREFREEZE_NO_NOMINEE_ARCHIVED'
t['tasks'][676].update(terminal)
t['tasks'][676].update({'observed_utc':now,'parent_disposition':'PREFREEZE_NO_NOMINEE_ARCHIVED',
    'parent_intake':'discovery-arithmetic-r162n-parent/intake.json','correctness_gate':None,
    'contribution_gate':None,'accepted':False,'count_change':0,
    'status_provenance':'Single actual notified terminal task_status response; no pending child/question/approval.'})
prep=load(o/'brief-preparation.json');brief=p/prep['path'];assert len(brief.read_bytes())==prep['bytes'] and sha(brief.read_bytes())==prep['sha256']
new_index=len(t['tasks']);record=copy.deepcopy(d)
record.update({'observed_utc':now,'target':args['target'],'role':'research','title':args['title'],
    'clientRequestId':args['clientRequestId'],'round':1,'parent_thread':'6742db91-d35c-44d0-a762-e5d9232f5177',
    'output':prep['root']+'/','brief':prep['path'],'brief_sha256':prep['sha256'],'brief_bytes':prep['bytes'],
    'submitted_prompt_contains_full_brief':True,
    'source_family_navigation':'DISTINCT Source079; catalogue[133395,134257),one canonical folder,17 descendants/15 blobs; actual build/main.tex wrapper. Parent metadata only; full operative/primary/original reading before extended deductions.',
    'round_namespace':'New distinct Source079 inside previously excluded arithmetic162 namespace; no retry/restriction of sparse corner,closed extremizer theorem,positive-order variation,weighted endpoint,full4D maximal or old targets.',
    'parent_count_at_dispatch':19,'accepted':False,'count_change':0,'publication':'STOPPED',
    'dispatch_receipt':'discovery-arithmetic-r162n-parent/arithmetic-r162o-dispatch.json',
    'prospective_isolation':'discovery-arithmetic-r162n-parent/prospective-isolation-arithmetic162o.json',
    'status_provenance':'Actual async delegate_task response at dispatch; no polling.'})
t['tasks'].append(record)
note='Arithmetic162n(idx676) archived PREFREEZE/no nominee. Full fixed-radius order1/8 sparse(24/17,12/5) diagnostic remains unproved;paid open-q side and order1/4 Hilbert endpoint are not substitutes. Uniform cumulative disjoint-cube L12/7 with weight2^(-3L(Q)/8),arbitrary rough complex cube inputs,bounded scale coefficients and occupied-scale count remains unpaid,with both cardinality and cumulative-scale budgets. Full local canonical reading but transitive primary gaps,false admissions and recoveries disclosed. Exact66payload/24directory/three-anchor packet,21canonical/14primary/nine-original bindings verified;69root files/modes unchanged;four saved copied controls matched. Distinct Source079 Euclidean three-dimensional wave local-smoothing discovery dispatched Arithmetic162o,idx'+str(new_index)+',codex/gpt-6-astra/high/default,actual running without pending child/question/approval. All341 inherited guards and5570standing bytes preserved,foreign original initial guards before creation. No foreign live status/body/findings/activity queried. All old scopes and dispositions preserved. Campaign19/20,latestR041,one remains;publication STOPPED.'
t['last_parent_progress']=note;s=t['current_work_snapshot']
s.update({'observed_utc':now,'note':note,'accepted_count':19,'remaining':1,'publication':'STOPPED'})
s['t3_current_confirmed_running']=[x for x in s.get('t3_current_confirmed_running',[]) if x!=terminal['taskId']]
if d['taskId'] not in s['t3_current_confirmed_running']:s['t3_current_confirmed_running'].append(d['taskId'])
s['arithmetic_r162n_archive']={'task_index':676,'status':'PREFREEZE_NO_NOMINEE','intake':'discovery-arithmetic-r162n-parent/intake.json',
    'full_diagnostic':intake['full_diagnostic'],'unpaid_sufficient_operation':intake['unpaid_sufficient_operation'],
    'correctness_gate':None,'contribution_gate':None,'accepted':False,'count_change':0}
s['arithmetic162o_prospective_isolation']={'task_index':new_index,'taskId':d['taskId'],'brief':prep['path'],
    'initial_guards_checked_before_creation':True,'source':'079','catalogue_extent':[133395,134257],
    'status_at_dispatch':'running','foreign_liveness_findings_not_queried':True,'publication':'STOPPED'}
for i,x in enumerate(base['tasks']):
    if i!=676:assert t['tasks'][i]==x
for k,x in base.items():
    if k not in ['tasks','last_parent_progress','current_work_snapshot']:assert t[k]==x
for name in ['prospective-parent-isolation.json','prospective-isolation-arithmetic162o.json']:
    iso=load(o/name)
    for x in iso.get('foreign_original_initial_briefs',iso.get('peer_original_initial_briefs',[])):
        assert sha((p/x['brief']).read_bytes())==x['brief_sha256']
append=('\n\n### Arithmetic162n no-nominee archive; distinct Source079 discovery\n\n'+note+
    '\n\nThe full sparse diagnostic concerns every bounded compactly supported complex pair at order1/8 and exponents(24/17,12/5). The sufficient cumulative-array bridge carries fixed cutoff/cancellation/localization parameters and every finite disjoint dyadic-cube family;its constant must not depend on functions,coefficients,truncation or occupied scales. The Whitney normalization and complete sparse recursion compatibility are preserved without asserting the bridge necessary or proved. Full source/primary open-critical-side and special Hilbert cancellation are paid;endpoint interpolation,cardinality and common-law/scale encoding attempts remain unresolved. No full theorem freeze,author proof,review gate,count,weaker replacement or global-impossibility assertion.\n\nParent assessment: frontier/campaigns/2026-10-14/discovery-arithmetic-r162n-parent/assessment.md. Read-only artifact checks authenticated66payloads,3615156bytes,24directories,allthree anchors,21canonical blobs,14primary objects andnine completed originals;all69root files/modes unchanged. Four saved copied controls behaved as expected. These are not mathematical gates. Parent read full derivation,source understanding and limits,not actual canonical/primary proofs. Child completed local mathematical source reading before calculations;transitive primary originals,omitted localized restriction proofs and background planar OCR remain incomplete. False selector admissions,coarse omissions and clipping recoveries remain disclosed.\n\nArithmetic162o is a DISTINCT Source079 task for Euclidean wave local smoothing in three spatial dimensions. Full strict-range p>2,regularity>max{0,1-3/p},criticalL3 with everypositive loss,and ALL actual operative proof operations are stipulated paid. One bounded14000byte catalogue navigation decoded onlytwo numeric titles and079body[133395,134257). One canonical folder,17descendants/15blobs,actual build/main.tex;parent proof reading absent. All341 inherited wildcard guards and5570byte original standing brief preserved,with two new explicit162o guards. Exact four completed exceptions do not widen namespaces. No desired-grade retry,nested agents or downstream work. Publication remains stopped.\n').encode()
assert head==git('rev-parse','HEAD').decode().strip() and tb==tp.read_bytes() and jb==jp.read_bytes()
write(o/'coordination-rebase.json',{'initial_head':baseline['head'],'integration_head':head,'rebased':head!=baseline['head'],
    'initial_tasks':baseline['taskCount'],'integration_tasks':len(base['tasks']),
    'changed_task_indices':[676],'new_task_index':new_index,'all_other_tasks_preserved':True,'foreign_live_state_not_queried':True})
write(tp,t);jp.write_bytes(jb+append)
write(o/'private/journal-append.json',{'prior_bytes':len(jb),'prior_sha256':sha(jb),'append_bytes':len(append),'append_sha256':sha(append)})
stage=[tp,jp,brief,r/'REPORT.md',r/'FINAL.md',r/'packet/RESEARCH.md',r/'packet/verify.py']
stage += [o/x for x in ['assessment.md','intake.json','verification.json','verify-intake.py','integration-baseline.json',
    'task-status.json','prospective-parent-isolation.json','prospective-isolation-arithmetic162o.json','capabilities.json',
    'prepare-brief.py','brief-preparation.json','arithmetic-r162o-dispatch.json','manage.py','coordination-rebase.json','integration-guard.json']]
rel=[f.relative_to(p).as_posix() for f in stage]
assert all('/private/' not in x and not x.endswith('MANIFEST.json') for x in rel)
write(o/'integration-guard.json',{'integration_head':head,'changed_task_indices':[676],'new_task_index':new_index,
    'new_taskId':d['taskId'],'all_other_task_records_preserved':True,'other_top_level_preserved_except_progress_snapshot':True,
    'journal_prefix_preserved':True,'root69_files_modes_unchanged':True,
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
