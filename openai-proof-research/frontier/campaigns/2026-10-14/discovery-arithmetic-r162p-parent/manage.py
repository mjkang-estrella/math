#!/usr/bin/env python3
"""Archive one no-nominee discovery and register the distinct next source."""
from pathlib import Path
import copy
import datetime
import hashlib
import json
import subprocess

p=Path.cwd();b=p/'frontier/campaigns/2026-10-14';o=b/'discovery-arithmetic-r162p-parent'
r=b/'fresh-arithmetic-discovery-r162p';tp=b/'tasks.json';jp=p/'frontier/NEW-TEN-2026-10-14.md'
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
terminal=load(o/'task-status.json')['structuredContent'];d=load(o/'arithmetic-r162q-dispatch.json')['structuredContent'];args=load(o/'private/submitted-prompt.json')
for x in [terminal,d]:
    assert (x['providerInstanceId'],x['model'])==('codex','gpt-6-astra')
    assert {z['id']:z['value'] for z in x['options']}=={'reasoningEffort':'high','serviceTier':'default'}
    assert not x['hasPendingChildRuns'] and not x['hasPendingQuestion'] and x['pendingApproval'] is None
assert terminal['status']=='completed' and terminal['workState']=='result_available'
assert d['status']=='running' and d['workState']=='working'
assert [i for i,x in enumerate(t['tasks']) if x.get('taskId')==terminal['taskId']]==[682]
assert not any(x.get('taskId')==d['taskId'] or x.get('clientRequestId')==args['clientRequestId'] for x in t['tasks'])
now=datetime.datetime.now(datetime.timezone.utc).isoformat();v=load(o/'verification.json');intake=load(o/'intake.json')
assert v['status']=='MATCH' and intake['status']=='PREFREEZE_NO_NOMINEE_ARCHIVED'
t['tasks'][682].update(terminal)
t['tasks'][682].update({'observed_utc':now,'parent_disposition':'PREFREEZE_NO_NOMINEE_ARCHIVED',
    'parent_intake':'discovery-arithmetic-r162p-parent/intake.json','correctness_gate':None,
    'contribution_gate':None,'accepted':False,'count_change':0,
    'status_provenance':'Single actual notified terminal task_status response; no pending child/question/approval.'})
prep=load(o/'brief-preparation.json');brief=p/prep['path'];assert len(brief.read_bytes())==prep['bytes'] and sha(brief.read_bytes())==prep['sha256']
new_index=len(t['tasks']);record=copy.deepcopy(d)
record.update({'observed_utc':now,'target':args['target'],'role':'research','title':args['title'],
    'clientRequestId':args['clientRequestId'],'round':1,'parent_thread':'6742db91-d35c-44d0-a762-e5d9232f5177',
    'output':prep['root']+'/','brief':prep['path'],'brief_sha256':prep['sha256'],'brief_bytes':prep['bytes'],
    'submitted_prompt_contains_full_brief':True,
    'source_family_navigation':'DISTINCT Source081; catalogue[135955,137284),one canonical folder,16 descendants/14 blobs; actual build/paper.tex wrapper. Parent metadata only; full operative/primary/original reading before extended deductions.',
    'round_namespace':'New distinct Source081 inside previously excluded arithmetic162 namespace; no retry/restriction of temporal variation,wave common-graph,sparse-corner,critical graph-Schatten or other old targets.',
    'parent_count_at_dispatch':19,'accepted':False,'count_change':0,'publication':'STOPPED',
    'dispatch_receipt':'discovery-arithmetic-r162p-parent/arithmetic-r162q-dispatch.json',
    'prospective_isolation':'discovery-arithmetic-r162p-parent/prospective-isolation-arithmetic162q.json',
    'status_provenance':'Actual async delegate_task response at dispatch; no polling.'})
t['tasks'].append(record)
note='Arithmetic162p(idx682) archived PREFREEZE/no nominee. The common-envelope source time tree already pays absolute dyadic-frequency summation,not a nominee. Full temporalq_n=2(n+1)/(n-1) variation at criticals_n=n/[2(n+1)],EVERYn>=2,rough complex data,translated unitball,allcutoffs and measurable ordered partitions remains unproved;completed estimates retain2^[K(n-1)/(2(n+1)^2)] or m^(1/q_n). Uniform coherent multi-time dual summation preservingell^(q-prime) and cancellation remains unpaid. Complete canonical but incomplete transitive primary reading,access failure,false admissions and recoveries disclosed. Exact70payload/three-anchor packet,35canonical,53hash/interval,threehistory/sixdirect records matched;75root files/modes unchanged;two saved copied controls matched. Distinct Source081 higher-codimension Riesz-transform rectifiability discovery dispatched Arithmetic162q,idx'+str(new_index)+',codex/gpt-6-astra/high/default,actual running without pending child/question/approval. All345 inherited guards and5570standing bytes preserved;foreign original initial guards before creation. No foreign live status/body/findings/activity queried. All old scopes and dispositions preserved. Previously deferred r162o archive/r162p record was reconciled in separate commit before this intake. Campaign19/20,latestR041,one remains;publication STOPPED.'
t['last_parent_progress']=note;s=t['current_work_snapshot']
s.update({'observed_utc':now,'note':note,'accepted_count':19,'remaining':1,'publication':'STOPPED'})
s['t3_current_confirmed_running']=[x for x in s.get('t3_current_confirmed_running',[]) if x!=terminal['taskId']]
if d['taskId'] not in s['t3_current_confirmed_running']:s['t3_current_confirmed_running'].append(d['taskId'])
s.pop('arithmetic162p_terminal_pending_intake',None)
s['arithmetic_r162p_archive']={'task_index':682,'status':'PREFREEZE_NO_NOMINEE','intake':'discovery-arithmetic-r162p-parent/intake.json',
    'full_diagnostic':intake['full_diagnostic'],'unpaid_operation':intake['unpaid_operation'],
    'correctness_gate':None,'contribution_gate':None,'accepted':False,'count_change':0}
s['arithmetic162q_prospective_isolation']={'task_index':new_index,'taskId':d['taskId'],'brief':prep['path'],
    'initial_guards_checked_before_creation':True,'source':'081','catalogue_extent':[135955,137284],
    'status_at_dispatch':'running','foreign_liveness_findings_not_queried':True,'publication':'STOPPED'}
for i,x in enumerate(base['tasks']):
    if i!=682:assert t['tasks'][i]==x
for k,x in base.items():
    if k not in ['tasks','last_parent_progress','current_work_snapshot']:assert t[k]==x
for name in ['prospective-parent-isolation.json','prospective-isolation-arithmetic162q.json']:
    iso=load(o/name)
    for x in iso.get('foreign_original_initial_briefs',iso.get('peer_original_initial_briefs',[])):
        assert sha((p/x['brief']).read_bytes())==x['brief_sha256']
append=('\n\n### Arithmetic162p no-nominee archive; distinct Source081 discovery\n\n'+note+
    '\n\nThe full temporal-variation diagnostic includes|fK|+V^q in localL2,EVERYtranslatedunitball,EVERYrough complexH^s input,EVERYK>=1 and every finite measurable ordered partition on[0,1],uniformin cutoff and cardinality. The moving packet excludes smallerq but does not disprove the endpoint. Stronger common-envelope source payment already gives absolute dyadic-frequency summation at one common time. Temporal phase increments need a uniform weighted FourierL2 dual estimate with pointwiseell^(q-prime) coefficients and short-increment cancellation;independent one-graph estimates loseell1 mass. Cutoff/cardinality/stronger-regularity substitutes are not nominated. No freeze,author proof,review gate,count,exhaustion or impossibility claim.\n\nParent assessment: frontier/campaigns/2026-10-14/discovery-arithmetic-r162p-parent/assessment.md. Artifact checks matched70packetfiles,7610085bytes,three detached anchors,35canonical blobs,53hash/interval read records,three history intervals on two originals,and six completed direct inputs. All75currentroot files/modes unchanged;two saved copied controls matched. File integrity is separate from mathematical gates. Parent read full derivation,source/primary understanding and limits,not actual canonical/primary proofs. Full canonical textual reading651044bytes completed before extended drafting;transitive primary gaps,original local-smoothing PDF403,late corroboration,clipping recovery,false keyword admissions and coarse omissions remain disclosed.\n\nArithmetic162q is DISTINCT Source081 higher-codimension Riesz transforms and uniform rectifiability. ENTIRE theorem for everyd>=4,2<=n<=d-2,n-ADregular Radon measure,uniform scalar-to-vectorL2hardtruncations implying quantitative uniformn-rectifiability/BPLI with only dimensions/regularity/operator dependence and ALL operative proof operations are stipulated paid. One bounded14000byte catalogue navigation decoded onlytwo numeric titles and081body[135955,137284). One folder,16descendants/14blobs,actual paper.tex wrapper;parent proof reading absent. All345inherited guards and5570standing bytes preserved,with two explicit162q guards. Four exact completed exceptions never widen namespaces. Full operative/primary/original reading precedes extended child work. No nested agents or downstream/public actions. Publication remains stopped.\n').encode()
assert head==git('rev-parse','HEAD').decode().strip() and tb==tp.read_bytes() and jb==jp.read_bytes()
write(o/'coordination-rebase.json',{'initial_head':baseline['head'],'integration_head':head,'rebased':head!=baseline['head'],
    'initial_tasks':baseline['taskCount'],'integration_tasks':len(base['tasks']),
    'changed_task_indices':[682],'new_task_index':new_index,'all_other_tasks_preserved':True,'foreign_live_state_not_queried':True})
write(tp,t);jp.write_bytes(jb+append)
write(o/'private/journal-append.json',{'prior_bytes':len(jb),'prior_sha256':sha(jb),'append_bytes':len(append),'append_sha256':sha(append)})
stage=[tp,jp,brief,r/'REPORT.md',r/'FINAL.md',r/'ANCHORS.json',r/'packet/public/verify_packet.py']
stage += [o/x for x in ['assessment.md','intake.json','verification.json','verify-intake.py','integration-baseline.json',
    'task-status.json','prospective-parent-isolation.json','prospective-isolation-arithmetic162q.json','capabilities.json',
    'prepare-brief.py','brief-preparation.json','arithmetic-r162q-dispatch.json','manage.py','coordination-rebase.json','integration-guard.json']]
rel=[f.relative_to(p).as_posix() for f in stage]
assert all('/private/' not in x and not x.endswith('MANIFEST.json') for x in rel)
write(o/'integration-guard.json',{'integration_head':head,'changed_task_indices':[682],'new_task_index':new_index,
    'new_taskId':d['taskId'],'all_other_task_records_preserved':True,'other_top_level_preserved_except_progress_snapshot':True,
    'journal_prefix_preserved':True,'root75_files_modes_unchanged':True,
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
