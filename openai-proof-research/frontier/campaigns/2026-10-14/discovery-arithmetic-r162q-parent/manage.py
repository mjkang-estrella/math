#!/usr/bin/env python3
"""Archive one no-nominee discovery and register the distinct next source."""
from pathlib import Path
import copy
import datetime
import hashlib
import json
import subprocess

p=Path.cwd();b=p/'frontier/campaigns/2026-10-14';o=b/'discovery-arithmetic-r162q-parent'
r=b/'fresh-arithmetic-discovery-r162q';tp=b/'tasks.json';jp=p/'frontier/NEW-TEN-2026-10-14.md'
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
terminal=load(o/'task-status.json')['structuredContent'];d=load(o/'arithmetic-r162r-dispatch.json')['structuredContent'];args=load(o/'private/submitted-prompt.json')
for x in [terminal,d]:
    assert (x['providerInstanceId'],x['model'])==('codex','gpt-6-astra')
    assert {z['id']:z['value'] for z in x['options']}=={'reasoningEffort':'high','serviceTier':'default'}
    assert not x['hasPendingChildRuns'] and not x['hasPendingQuestion'] and x['pendingApproval'] is None
assert terminal['status']=='completed' and terminal['workState']=='result_available'
assert d['status']=='running' and d['workState']=='working'
assert [i for i,x in enumerate(t['tasks']) if x.get('taskId')==terminal['taskId']]==[683]
assert not any(x.get('taskId')==d['taskId'] or x.get('clientRequestId')==args['clientRequestId'] for x in t['tasks'])
now=datetime.datetime.now(datetime.timezone.utc).isoformat();v=load(o/'verification.json');intake=load(o/'intake.json')
assert v['status']=='MATCH' and intake['status']=='PREFREEZE_NO_NOMINEE_ARCHIVED'
t['tasks'][683].update(terminal)
t['tasks'][683].update({'observed_utc':now,'parent_disposition':'PREFREEZE_NO_NOMINEE_ARCHIVED',
    'parent_intake':'discovery-arithmetic-r162q-parent/intake.json','correctness_gate':None,
    'contribution_gate':None,'accepted':False,'count_change':0,
    'status_provenance':'Single actual notified terminal task_status response; no pending child/question/approval.'})
prep=load(o/'brief-preparation.json');brief=p/prep['path'];assert len(brief.read_bytes())==prep['bytes'] and sha(brief.read_bytes())==prep['sha256']
new_index=len(t['tasks']);record=copy.deepcopy(d)
record.update({'observed_utc':now,'target':args['target'],'role':'research','title':args['title'],
    'clientRequestId':args['clientRequestId'],'round':1,'parent_thread':'6742db91-d35c-44d0-a762-e5d9232f5177',
    'output':prep['root']+'/','brief':prep['path'],'brief_sha256':prep['sha256'],'brief_bytes':prep['bytes'],
    'submitted_prompt_contains_full_brief':True,
    'source_family_navigation':'DISTINCT Source082; catalogue[137284,139784),three canonical companion folders,47 descendants/39 blobs; actual build/main.tex wrappers. Parent metadata only; full operative/primary/original reading before extended deductions.',
    'round_namespace':'New distinct Source082 inside previously excluded arithmetic162 namespace; no retry/restriction of reflectionless classification,temporal variation,common-graph,sparse-corner or earlier targets.',
    'parent_count_at_dispatch':19,'accepted':False,'count_change':0,'publication':'STOPPED',
    'dispatch_receipt':'discovery-arithmetic-r162q-parent/arithmetic-r162r-dispatch.json',
    'prospective_isolation':'discovery-arithmetic-r162q-parent/prospective-isolation-arithmetic162r.json',
    'status_provenance':'Actual async delegate_task response at dispatch; no polling.'})
t['tasks'].append(record)
note='Arithmetic162q(idx683) archived PREFREEZE/no nominee. Full higher-codimension reflectionless AD/L2Riesz diagnostic remains unproved. Strongest source/primary composition pays compact-support elimination,flat seeds in EVERY ball and finite-orthogonal-energy-to-constant-plane rigidity without graph/density-tail assumptions. Obtaining ONE fixed plane with finite total orthogonal energy for EVERY full input,or coherent same-flat-measure annular/global control retaining all cross forces,remains unpaid. LocalR^(n+1)energy and independently selected planes do not close it. Complete canonical but incomplete transitive primary reading,late stronger reads,false admissions and format/encoding recoveries disclosed. Exact42payload/three-anchor packet,14canonical/12primary/fourdirect/onehistory bindings matched;45root files/modes unchanged;two saved copied controls matched. Distinct Source082 triangular-Hilbert annular-variation/dyadic-absolute discovery dispatched Arithmetic162r,idx'+str(new_index)+',codex/gpt-6-astra/high/default,actual running without pending child/question/approval. All347 inherited guards and5570standing bytes preserved;foreign original initial guards before creation. No foreign live status/body/findings/activity queried. All old scopes/dispositions preserved. User publication preparation can proceed independently;no uploads or external actions resumed. Campaign19/20,latestR041,one remains;publication STOPPED.'
t['last_parent_progress']=note;s=t['current_work_snapshot']
s.update({'observed_utc':now,'note':note,'accepted_count':19,'remaining':1,'publication':'STOPPED'})
s['t3_current_confirmed_running']=[x for x in s.get('t3_current_confirmed_running',[]) if x!=terminal['taskId']]
if d['taskId'] not in s['t3_current_confirmed_running']:s['t3_current_confirmed_running'].append(d['taskId'])
s['arithmetic_r162q_archive']={'task_index':683,'status':'PREFREEZE_NO_NOMINEE','intake':'discovery-arithmetic-r162q-parent/intake.json',
    'full_diagnostic':intake['full_diagnostic'],'unpaid_operation':intake['unpaid_operation'],
    'correctness_gate':None,'contribution_gate':None,'accepted':False,'count_change':0}
s['arithmetic162r_prospective_isolation']={'task_index':new_index,'taskId':d['taskId'],'brief':prep['path'],
    'initial_guards_checked_before_creation':True,'source':'082','catalogue_extent':[137284,139784],
    'status_at_dispatch':'running','foreign_liveness_findings_not_queried':True,'publication':'STOPPED'}
for i,x in enumerate(base['tasks']):
    if i!=683:assert t['tasks'][i]==x
for k,x in base.items():
    if k not in ['tasks','last_parent_progress','current_work_snapshot']:assert t[k]==x
for name in ['prospective-parent-isolation.json','prospective-isolation-arithmetic162r.json']:
    iso=load(o/name)
    for x in iso.get('foreign_original_initial_briefs',iso.get('peer_original_initial_briefs',[])):
        assert sha((p/x['brief']).read_bytes())==x['brief_sha256']
append=('\n\n### Arithmetic162q no-nominee archive; distinct Source082 discovery\n\n'+note+
    '\n\nThe full diagnostic retains everyd>=4,2<=n<=d-2,positive n-ADRadon measure,uniform scalar-to-vectorL2bounds for allhard Riesz truncations,and the ACTUAL mean-zero exterior-subtracted reflectionless pairing on allcompact Lipschitz tests. Globalconstant-density affineplane rigidity is unproved. Nondegenerate compact supports are eliminated,not excluded;zero-diameter conventions stay explicit. Finite-energy-to-plane and coherent same-flat annular-to-core operations are paid. One global finite-energy plane for everyfullinput,or a different coherent global construction preserving cross forces,remains unpaid. Favorable finite-energy,graph,exterior-flat,smooth or independently reselected-plane cases are not substitutes. No freeze,author proof,review gate,count,priority or impossibility claim.\n\nParent assessment: frontier/campaigns/2026-10-14/discovery-arithmetic-r162q-parent/assessment.md. Artifact verification matched42payloadfiles,1821876bytes,three detached anchors,14canonical blobs,12primary objects,four completed direct inputs and oneexact original-history span[15044,33437). All45currentroot files/modes unchanged;two saved copied controls matched. Parent mode preservation is separate from sealedfilehash scope. Parent read full derivation,source/primary understanding and limits,not actual canonical/primary proofs. Full canonical text189302bytes read before extended notes;incomplete transitive primary ancestry,later half-order/truncation reads,gzip/cp1252recoveries,false lexical admissions,clipped navigation and coarse omissions remain disclosed. These authenticate artifacts,not mathematical gates.\n\nArithmetic162r is DISTINCT Source082 triangular-Hilbert annular variation and dyadic absolute bounds. AllTHREE companion manuscripts and operative proofs are paid,including complexL3xL3->L3/2annularr-variation for everyr>2,point-dependent partitions/allpositive scales,two-endpoint hard maximal/jointa.e.andnorm convergence,symmetric trilinear estimate,and independent admissible-triple coefficient absolute dyadic bound40 for unrestricted real inputs. Onebounded14000byte catalogue navigation decoded onlytwo numeric titles and082body[137284,139784). Threefolders,47descendants/39blobs,actualmain.tex wrappers;parent proof reading absent. All347inherited guards and5570standing bytes preserved,with two explicit162r guards. Four exactcompleted exceptions never widen namespaces. Full operative/primary/original reading precedes extended child research. Publication preparation remains available to user;no automatic public actions,contacts,browserUI,nested agents or downstream work. Publication stopped.\n').encode()
assert head==git('rev-parse','HEAD').decode().strip() and tb==tp.read_bytes() and jb==jp.read_bytes()
write(o/'coordination-rebase.json',{'initial_head':baseline['head'],'integration_head':head,'rebased':head!=baseline['head'],
    'initial_tasks':baseline['taskCount'],'integration_tasks':len(base['tasks']),
    'changed_task_indices':[683],'new_task_index':new_index,'all_other_tasks_preserved':True,'foreign_live_state_not_queried':True})
write(tp,t);jp.write_bytes(jb+append)
write(o/'private/journal-append.json',{'prior_bytes':len(jb),'prior_sha256':sha(jb),'append_bytes':len(append),'append_sha256':sha(append)})
stage=[tp,jp,brief,r/'REPORT.md',r/'FINAL.md',r/'ANCHORS.json',r/'verify_packet.py']
stage += [o/x for x in ['assessment.md','intake.json','verification.json','verify-intake.py','integration-baseline.json',
    'task-status.json','prospective-parent-isolation.json','prospective-isolation-arithmetic162r.json','capabilities.json',
    'prepare-brief.py','brief-preparation.json','arithmetic-r162r-dispatch.json','manage.py','coordination-rebase.json','integration-guard.json']]
rel=[f.relative_to(p).as_posix() for f in stage]
assert all('/private/' not in x and not x.endswith('MANIFEST.json') for x in rel)
write(o/'integration-guard.json',{'integration_head':head,'changed_task_indices':[683],'new_task_index':new_index,
    'new_taskId':d['taskId'],'all_other_task_records_preserved':True,'other_top_level_preserved_except_progress_snapshot':True,
    'journal_prefix_preserved':True,'root45_files_modes_unchanged':True,
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
