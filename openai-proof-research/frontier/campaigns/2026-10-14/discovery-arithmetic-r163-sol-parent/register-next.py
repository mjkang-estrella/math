from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent;N=B/'discovery-arithmetic-r164-sol-parent'
TP='frontier/campaigns/2026-10-14/tasks.json';JP='frontier/NEW-TEN-2026-10-14.md'
def git(*args,input=None):return subprocess.check_output(['git',*args],cwd=P,input=input)
def sha(a):return hashlib.sha256(a).hexdigest()
def enc(x):return (json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode()
assert not git('diff','--cached','--name-only').strip()
h=git('rev-parse','HEAD').decode().strip();ht=git('show',h+':openai-proof-research/'+TP);hj=git('show',h+':openai-proof-research/'+JP);wt=(P/TP).read_bytes();wj=(P/JP).read_bytes();base=json.loads(ht);work=json.loads(wt)
assert len(base['tasks'])==len(work['tasks'])==862 and base['tasks'][861]==work['tasks'][861]
assert base['newAccepted']==work['newAccepted']==19 and base['latestAcceptance']==work['latestAcceptance']=='R041'
assert base['gpt_subagent_preferences']==work['gpt_subagent_preferences']
foreign=[i for i,(a,b) in enumerate(zip(base['tasks'],work['tasks'])) if a!=b];foreign_top=[k for k in base if k!='tasks' and base[k]!=work[k]]
prep=json.loads((N/'brief-preparation.json').read_bytes());brief=(P/prep['brief']).read_bytes();assert len(brief)==prep['bytes'] and sha(brief)==prep['sha256'] and len(brief.decode())<120000
dispatch=json.loads((N/'dispatch.json').read_bytes())['structuredContent'];assert dispatch['status']=='running' and dispatch['workState']=='working' and dispatch['model']=='gpt-6.1-sol' and dispatch['providerInstanceId']=='codex'
assert {x['id']:x['value'] for x in dispatch['options']}==dict(reasoningEffort='high',serviceTier='ultrafast') and not dispatch['hasPendingQuestion'] and dispatch['pendingApproval'] is None
assert prep['all_previous_literal_guards_retained'] and prep['standing_bytes_preserved']==5570
client='twenty-20261025-fresh-arithmetic-r164-sol-r1';assert not any(x.get('clientRequestId')==client for x in work['tasks'])
now=datetime.now(timezone.utc).isoformat();fresh=copy.deepcopy(dispatch)
fresh.update(observed_utc=now,role='research',round=1,title='Arithmetic164Sol: correspondence-coloring discovery',clientRequestId=client,parent_thread='6742db91-d35c-44d0-a762-e5d9232f5177',target=dict(providerInstanceId='codex',model='gpt-6.1-sol',options=dict(reasoningEffort='high',serviceTier='ultrafast')),output='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r164-sol/',brief=prep['brief'],brief_bytes=prep['bytes'],brief_sha256=prep['sha256'],submitted_prompt_contains_full_brief=True,source_index=184,source_family_navigation='One catalogue window[288176,302176):184/185titles and only184body[288176,290060) decoded,185body unread. Two correspondence-coloring/independence manuscripts;24blobs32entries22texts164770bytes. Parent operative proof unread.',round_namespace='Distinct from Source183. Full source correspondence-coloring and independence bounds paid;all old scopes unchanged,including R162BX.',completed_direct_inputs=5,dispatch_receipt='discovery-arithmetic-r164-sol-parent/dispatch.json',prospective_isolation='discovery-arithmetic-r164-sol-parent/prospective-isolation.json',all_previous_literal_guards_and5570_standing_bytes_retained=True,independent_review=False,accepted=False,count_change=0,parent_count_at_dispatch=19,publication='STOPPED',status_provenance='Fresh async Sol/high/ultrafast receipt;one active task per model;no polling.')
def update(original):
 x=copy.deepcopy(original);x['tasks'].append(copy.deepcopy(fresh));k='arithmetic_r164_sol_dispatch';assert k not in x['current_work_snapshot'];x['current_work_snapshot'][k]={'observed_utc':now,'task_index':862,'source':184,'model':'gpt-6.1-sol','serviceTier':'ultrafast','count_change':0,'publication':'STOPPED'}
 assert x['tasks'][:-1]==original['tasks'] and all(x[k]==original[k] for k in original if k not in {'tasks','current_work_snapshot'})
 return x
idx=enc(update(base));merged=enc(update(work));note=('\n\n### Sol correspondence-coloring discovery — '+now+'\n\nCompleted R162CU and R163-Sol are both PREFREEZE/no nominee and separately archived. New Source184 author uses Codex/GPT-6.1-Sol/high/ultrafast,one active task per named model. One catalogue window288176..302176,only184body and184/185titles decoded;185body unread. Two canonical manuscripts,24blobs32entries22texts164770bytes,parent operative proofs unread. Full source correspondence-coloring and independence conclusions paid;R162BX and every older scope unchanged. All prior literal guards and5570standing bytes retained;29 redundant administrative headings removed without changing mathematical scopes. Five exact completed exceptions;guarded exclusive root. No mathematical grade or increment. Campaign19/20,latestR041;publication/downstreamSTOPPED.\n').encode();ij=hj+note;mj=wj+note
for e in json.loads((N/'private/completed-direct-inputs.json').read_bytes()):
 p=P/e['path'];a=p.read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256'] and p.stat().st_mode==e['mode']
protected={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
for n,s in protected.items():assert sha((P/n).read_bytes())==s
(D/'next-registration.json').write_bytes(enc({'head':h,'changed_old_tasks':[],'new_task_index':862,'foreign_task_indices_preserved':foreign,'foreign_top_fields_preserved':foreign_top,'foreign_journal_preserved':wj!=hj,'count_change':0,'live_author_payloads_unmodified':True}))
(N/'registration.json').write_bytes(enc({'task_index':862,'taskId':dispatch['taskId'],'status_at_dispatch':'running','model':'gpt-6.1-sol','serviceTier':'ultrafast','count_change':0}))
paths=[(D/n).relative_to(P).as_posix() for n in ['prepare-next.py','register-next.py','next-registration.json']]+[(N/n).relative_to(P).as_posix() for n in ['brief-preparation.json','capabilities.json','dispatch.json','prospective-isolation.json','registration.json']]+[prep['brief'],TP,JP];assert len(paths)==len(set(paths))==11
assert git('rev-parse','HEAD').decode().strip()==h and (P/TP).read_bytes()==wt and (P/JP).read_bytes()==wj and not git('diff','--cached','--name-only').strip()
(P/TP).write_bytes(merged);(P/JP).write_bytes(mj)
subprocess.run(['git','add','--',*[n for n in paths if n not in {TP,JP}]],cwd=P,check=True)
for path,content in [(TP,idx),(JP,ij)]:
 blob=git('hash-object','-w','--stdin',input=content).decode().strip();subprocess.run(['git','update-index','--add','--cacheinfo','100644',blob,'openai-proof-research/'+path],cwd=P,check=True)
assert {n for n in git('diff','--cached','--name-only','-z').decode().split('\0') if n}=={'openai-proof-research/'+n for n in paths}
assert git('show',':openai-proof-research/'+TP)==idx and git('show',':openai-proof-research/'+JP)==ij
subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
assert git('rev-parse','HEAD').decode().strip()==h and (P/TP).read_bytes()==merged and (P/JP).read_bytes()==mj
subprocess.run(['git','commit','-m','Start Sol ultrafast correspondence-coloring discovery'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip() and git('show','HEAD:openai-proof-research/'+TP)==idx and (P/TP).read_bytes()==merged and git('show','HEAD:openai-proof-research/'+JP)==ij and (P/JP).read_bytes()==mj
for n,s in protected.items():assert sha((P/n).read_bytes())==s
print(json.dumps({'commit':git('rev-parse','HEAD').decode().strip(),'task_index':862,'model':'gpt-6.1-sol','serviceTier':'ultrafast','foreign_edits_preserved':foreign,'count':19}))
