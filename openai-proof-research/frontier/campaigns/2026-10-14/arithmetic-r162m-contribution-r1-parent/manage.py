#!/usr/bin/env python3
"""Adopt whole contribution closure and register one distinct discovery task."""
from pathlib import Path
import copy
import datetime
import hashlib
import json
import subprocess

p = Path.cwd()
b = p / 'frontier/campaigns/2026-10-14'
o = b / 'arithmetic-r162m-contribution-r1-parent'
r = b / 'arithmetic-r162m-contribution-r1'
a = b / 'fresh-arithmetic-discovery-r162m'
tp, jp = b / 'tasks.json', p / 'frontier/NEW-TEN-2026-10-14.md'
git = lambda *args: subprocess.check_output(['git', *args])
sha = lambda d: hashlib.sha256(d).hexdigest()
load = lambda f: json.loads(f.read_bytes())
def write(f, x):
    f.write_text(json.dumps(x, indent=2)+'\n')
def snapshot(root):
    return {f.relative_to(root).as_posix(): {'bytes': f.stat().st_size,
        'mode': f.stat().st_mode, 'sha256': sha(f.read_bytes())}
        for f in root.rglob('*') if f.is_file()}
baseline = load(o / 'integration-baseline.json')
assert not git('diff','--cached','--name-only')
for f,h in baseline['protected'].items():
    assert sha((p/f).read_bytes()) == h
assert snapshot(a) == load(o/'private/author-root-before.json')
assert snapshot(r) == load(o/'private/review-root-before.json')
head = git('rev-parse','HEAD').decode().strip()
old_t = git('show',head+':openai-proof-research/'+tp.relative_to(p).as_posix())
old_j = git('show',head+':openai-proof-research/'+jp.relative_to(p).as_posix())
assert old_t == tp.read_bytes() and old_j == jp.read_bytes(), 'Other-owner uncommitted coordination; do not overwrite.'
base = json.loads(old_t)
t = copy.deepcopy(base)
assert (t['newAccepted'],t['target'],t['remaining'],t['latestAcceptance']) == (19,20,1,'R041')
v = load(o/'verification.json')
terminal = load(o/'task-status.json')['structuredContent']
d = load(o/'arithmetic-r162n-dispatch.json')['structuredContent']
args = load(o/'private/submitted-prompt.json')
for x in [terminal,d]:
    assert (x['providerInstanceId'],x['model']) == ('codex','gpt-6-astra')
    assert {z['id']:z['value'] for z in x['options']} == {'reasoningEffort':'high','serviceTier':'default'}
    assert not x['hasPendingChildRuns'] and not x['hasPendingQuestion'] and x['pendingApproval'] is None
assert terminal['status']=='completed' and terminal['workState']=='result_available'
assert d['status']=='running' and d['workState']=='working'
assert [i for i,x in enumerate(t['tasks']) if x.get('taskId')==terminal['taskId']] == [673]
assert not any(x.get('taskId')==d['taskId'] or x.get('clientRequestId')==args['clientRequestId'] for x in t['tasks'])
author = t['tasks'][671]
correctness = author['correctness_gate']
assert correctness['verdict']=='PASS' and correctness['review_task_index']==672
assert correctness['frozen_sha256']==author['frozen_sha256']==v['frozen_sha256']
assert correctness['proof_sha256']==author['author_proof_sha256']==v['proof_sha256']
assert author['contribution_gate'] is None
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
gate = {'verdict':'TECHNICAL','scope':'entire unchanged frozen theorem',
    'conditional_on_full_correctness':True,'condition':'DISCHARGED',
    'discharged_by_correctness_task_index':672,'review_task_index':673,
    'review_taskId':terminal['taskId'],'frozen_sha256':v['frozen_sha256'],
    'proof_sha256':v['proof_sha256'],'essential_unresolved_comparison_obligations':[],
    'parent_intake':'arithmetic-r162m-contribution-r1-parent/intake.json','adopted_utc':now}
author.update({'contribution_gate':gate,'parent_disposition':'CLOSED_WHOLE_SCOPE_PASS_TECHNICAL_ZERO_COUNT',
    'contribution_parent_intake':gate['parent_intake'],'contribution_condition':'DISCHARGED',
    'accepted':False,'count_change':0,'no_grade_shopping_or_downstream_work':True})
t['tasks'][673].update(terminal)
t['tasks'][673].update({'observed_utc':now,'parent_gate':gate,
    'parent_disposition':'FULL_SCOPE_TECHNICAL_ADOPTED_CONDITION_DISCHARGED_ZERO_COUNT',
    'parent_intake':gate['parent_intake'],'accepted':False,'count_change':0,
    'status_provenance':'Single notified terminal task_status; no pending child/question/approval.'})
prep = load(o/'brief-preparation.json')
new_index = len(t['tasks'])
brief = Path(prep['path'])
brief_data = brief.read_bytes()
assert sha(brief_data)==prep['sha256'] and len(brief_data)==prep['bytes']
record = copy.deepcopy(d)
record.update({'observed_utc':now,'target':args['target'],'role':'research','title':args['title'],
    'clientRequestId':args['clientRequestId'],'round':1,'parent_thread':'6742db91-d35c-44d0-a762-e5d9232f5177',
    'output':Path(prep['root']).relative_to(p).as_posix()+'/',
    'brief':brief.relative_to(p).as_posix(),'brief_sha256':prep['sha256'],'brief_bytes':prep['bytes'],
    'submitted_prompt_contains_full_brief':True,
    'source_family_navigation':'DISTINCT Source078; exact catalogue[132535,133395),one canonical folder,30 descendants/21 blobs; build/paper.tex wrapper. Parent metadata navigation only; full operative reading before extended deductions.',
    'round_namespace':'New distinct Source078 within previously excluded arithmetic162 namespace; no retry of closed extremizer theorem,positive-order variation,weighted endpoint,full4D maximal or earlier targets.',
    'parent_count_at_dispatch':19,'accepted':False,'count_change':0,'publication':'STOPPED',
    'dispatch_receipt':'arithmetic-r162m-contribution-r1-parent/arithmetic-r162n-dispatch.json',
    'prospective_isolation':'arithmetic-r162m-contribution-r1-parent/prospective-isolation-arithmetic162n.json',
    'status_provenance':'Actual async delegate_task response at dispatch; no polling.'})
t['tasks'].append(record)
note = 'Arithmetic162m unchanged whole-scope correctness PASS / contribution TECHNICAL closed with condition DISCHARGED and ZERO count. Full compatible source/primary/classical derivation covers every frozen quantifier; no essential contribution-comparison gap,desired-grade retry or downstream work. Exact69-file/21-directory contribution packet and21 immutable author-input checks passed;104 author-root/72 review-root files unchanged. Distinct Source078 three-dimensional Bochner-Riesz discovery dispatched as Arithmetic162n,idx'+str(new_index)+',codex/gpt-6-astra/high/default,actual running without pending child/question/approval. All prior literal guards and5570-byte standing brief preserved; foreign original initial guards checked before creation. No foreign live status,body,findings or activity queried. Campaign19/20,latestR041,one remains;publication STOPPED.'
t['last_parent_progress']=note
s=t['current_work_snapshot']
s.update({'observed_utc':now,'note':note,'accepted_count':19,'remaining':1,'publication':'STOPPED'})
s['t3_current_confirmed_running']=[x for x in s.get('t3_current_confirmed_running',[]) if x!=terminal['taskId']]
if d['taskId'] not in s['t3_current_confirmed_running']:
    s['t3_current_confirmed_running'].append(d['taskId'])
s['arithmetic_r162m_nominee'].update({'status':'CLOSED_WHOLE_SCOPE_PASS_TECHNICAL_ZERO_COUNT',
    'contribution_gate':gate,'contribution_condition':'DISCHARGED','accepted':False,'count_change':0,
    'final_parent_intake':gate['parent_intake']})
s['arithmetic_r162m_contribution_adoption']=gate
s['arithmetic162n_prospective_isolation']={'task_index':new_index,'taskId':d['taskId'],
    'brief':record['brief'],'initial_guards_checked_before_creation':True,
    'source':'078','catalogue_extent':[132535,133395],'status_at_dispatch':'running',
    'foreign_liveness_and_findings_not_queried':True,'publication':'STOPPED'}
for i,x in enumerate(base['tasks']):
    if i not in [671,673]: assert t['tasks'][i]==x
for k,x in base.items():
    if k not in ['tasks','last_parent_progress','current_work_snapshot']: assert t[k]==x
for name in ['prospective-parent-isolation.json','prospective-isolation-arithmetic162n.json']:
    iso=load(o/name)
    for x in iso.get('foreign_original_initial_briefs',iso.get('peer_original_initial_briefs',[])):
        assert sha((p/x['brief']).read_bytes())==x['brief_sha256']
append = ('\n\n### Arithmetic162m whole-scope PASS/TECHNICAL closed; distinct Source078 dispatched\n\n'+note+
    '\n\nThe contribution condition is discharged by the already adopted full unchanged correctness PASS at identical frozen theorem/proof hashes. The complete review retains actual L3->Lq payment,original-sequence weakLp profiles,fixed-J two-output-exponent remainder control,localized Hilbert square mass,strict complex plus/minus convexity,analytic injectivity,uniform convexity and modulation invariance. It covers arbitrary rough complex normalized inputs,every finitep>3,every frozen smooth compact positive-curvature surface including boundary,every extremizing sequence,strong compactness with the exact modulation sign,attainment and qualitative whole-extremizer-set stability. No essential comparison gap remains. No acceptance,count,revised theorem,grade-shopping retry or downstream work.\n\nParent assessment: frontier/campaigns/2026-10-14/arithmetic-r162m-contribution-r1-parent/assessment.md. Frozen SHA256'+v['frozen_sha256']+';proof SHA256'+v['proof_sha256']+'. Read-only artifact verification matched69 payloads,2780230bytes,21directories,three anchors,29canonical blobs,nine primary-member bindings,five exact original spans and21author-input records.104author-root/72review-root files and modes unchanged;three saved copied controls matched. These authenticate bytes,not mathematics. Parent read full review,operative comparison and limits;canonical/primary proofs were not reread by parent. Late canonical ancestor reads,truncation recovery,partial/uninvoked transitive proofs,missing search receipt and parent clipped metadata print are retained honestly.\n\nArithmetic162n is a DISTINCT pinned Source078 discovery. Full strict-order three-dimensional Bochner-Riesz theorem and all actual source/classical operations are stipulated paid;earlier positive-order radius-variation application retains its technical/PREFREEZE disposition. The full original standing brief5570bytes and all339 inherited literal guards survive,with two new explicit162n guards. One bounded14000byte catalogue navigation decoded onlytwo numeric titles and the exact078body[132535,133395);two initial regex failures decoded no new body. Canonical metadata confirms onefolder,30descendants/21blobs,actual build/paper.tex wrapper. Parent read no source proof. Full operative/primary/original reading precedes extended child research. No foreign task queries or steering. Publication stopped.\n').encode()
assert head==git('rev-parse','HEAD').decode().strip()
assert old_t==tp.read_bytes() and old_j==jp.read_bytes()
write(o/'coordination-rebase.json',{'initial_head':baseline['head'],'integration_head':head,
    'rebased':head!=baseline['head'],'initial_tasks':baseline['taskCount'],
    'integration_tasks':len(base['tasks']),'changed_task_indices':[671,673],
    'new_task_index':new_index,'all_other_tasks_preserved':True,'foreign_live_state_not_queried':True})
write(tp,t)
jp.write_bytes(old_j+append)
write(o/'private/journal-append.json',{'prior_bytes':len(old_j),'prior_sha256':sha(old_j),
    'append_bytes':len(append),'append_sha256':sha(append)})
stage=[tp,jp,brief,r/'REPORT.md',r/'ANCHORS.json',r/'packet/FINAL.md',r/'packet/REVIEW.md',r/'packet/verify_packet.py']
stage += [o/x for x in ['assessment.md','intake.json','verification.json','verify-intake.py',
    'integration-baseline.json','task-status.json','prospective-parent-isolation.json',
    'prospective-isolation-arithmetic162n.json','capabilities.json','prepare-brief.py',
    'brief-preparation.json','arithmetic-r162n-dispatch.json','manage.py','coordination-rebase.json','integration-guard.json']]
relative=[f.relative_to(p).as_posix() for f in stage]
assert all('/private/' not in x and not x.endswith('MANIFEST.json') for x in relative)
write(o/'integration-guard.json',{'integration_head':head,'changed_task_indices':[671,673],
    'new_task_index':new_index,'new_taskId':d['taskId'],'all_other_task_records_preserved':True,
    'all_other_top_level_fields_preserved_except_progress_snapshot':True,
    'journal_prefix_preserved':True,'author104_and_review72files_modes_unchanged':True,
    'frozen_sha256':v['frozen_sha256'],'proof_sha256':v['proof_sha256'],
    'correctness':'PASS_ENTIRE_UNCHANGED_SCOPE','contribution':gate,'condition':'DISCHARGED',
    'accepted':False,'count_change':0,'count':19,'remaining':1,'latestAcceptance':'R041',
    'publication':'STOPPED','no_downstream_work_for_closed_candidate':True,
    'new_task_provider_model_options_checked':True,'stage_allowlist':relative,
    'protected_excluded':baseline['protected']})
assert snapshot(a)==load(o/'private/author-root-before.json')
assert snapshot(r)==load(o/'private/review-root-before.json')
assert head==git('rev-parse','HEAD').decode().strip()
subprocess.run(['git','add','--',*relative],check=True)
assert set(git('diff','--cached','--name-only').decode().splitlines())=={'openai-proof-research/'+x for x in relative}
for rel in relative: assert git('show',':openai-proof-research/'+rel)==(p/rel).read_bytes()
print(json.dumps({'status':'CLOSED_PASS_TECHNICAL_AND_DISTINCT_TASK_REGISTERED','head':head,
    'staged_files':len(relative),'new_task_index':new_index,'count':19,'remaining':1},indent=2))
