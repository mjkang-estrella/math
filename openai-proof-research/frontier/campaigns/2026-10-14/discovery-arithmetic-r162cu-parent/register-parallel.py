from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent;N=B/'discovery-arithmetic-r163-sol-parent'
TP='frontier/campaigns/2026-10-14/tasks.json';JP='frontier/NEW-TEN-2026-10-14.md'
def git(*args,input=None):return subprocess.check_output(['git',*args],cwd=P,input=input)
def sha(a):return hashlib.sha256(a).hexdigest()
def enc(x):return (json.dumps(x,ensure_ascii=False,indent=2)+'\n').encode()
assert not git('diff','--cached','--name-only').strip()
h=git('rev-parse','HEAD').decode().strip();ht=git('show',h+':openai-proof-research/'+TP);hj=git('show',h+':openai-proof-research/'+JP);wt=(P/TP).read_bytes();wj=(P/JP).read_bytes();base=json.loads(ht);work=json.loads(wt)
assert len(base['tasks'])==len(work['tasks'])==861 and base['tasks'][860]==work['tasks'][860]
assert base['newAccepted']==work['newAccepted']==19 and base['latestAcceptance']==work['latestAcceptance']=='R041'
assert base['gpt_subagent_preferences']==work['gpt_subagent_preferences']
foreign=[i for i,(a,b) in enumerate(zip(base['tasks'],work['tasks'])) if a!=b];foreign_top=[k for k in base if k!='tasks' and base[k]!=work[k]]
prep=json.loads((N/'brief-preparation.json').read_bytes());brief=(P/prep['brief']).read_bytes();assert len(brief)==prep['bytes'] and sha(brief)==prep['sha256'] and len(brief.decode())<120000
dispatch=json.loads((N/'dispatch.json').read_bytes())['structuredContent'];assert dispatch['status']=='running' and dispatch['workState']=='working' and dispatch['model']=='gpt-6.1-sol' and dispatch['providerInstanceId']=='codex'
assert {x['id']:x['value'] for x in dispatch['options']}==dict(reasoningEffort='high',serviceTier='ultrafast') and not dispatch['hasPendingQuestion'] and dispatch['pendingApproval'] is None
assert prep['all_previous_literal_guards_retained'] and prep['standing_bytes_preserved']==5570
client='twenty-20261025-fresh-arithmetic-r163-sol-r1';assert not any(x.get('clientRequestId')==client for x in work['tasks'])
now=datetime.now(timezone.utc).isoformat();fresh=copy.deepcopy(dispatch)
fresh.update(observed_utc=now,role='research',round=1,title='Arithmetic163Sol: parallel halving-line discovery',clientRequestId=client,parent_thread='6742db91-d35c-44d0-a762-e5d9232f5177',target=dict(providerInstanceId='codex',model='gpt-6.1-sol',options=dict(reasoningEffort='high',serviceTier='ultrafast')),output='frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r163-sol/',brief=prep['brief'],brief_bytes=prep['bytes'],brief_sha256=prep['sha256'],submitted_prompt_contains_full_brief=True,source_index=183,source_family_navigation='One catalogue window[287105,301105):183/184titles and only183body[287105,288176) decoded,184body unread. One planar halving-line/k-set manuscript;12blobs15entries11texts111708bytes. Parent operative proof unread.',round_namespace='Distinct from live Source182. Full source halving-line and k-set power savings paid;all older scopes unchanged.',completed_direct_inputs=5,dispatch_receipt='discovery-arithmetic-r163-sol-parent/dispatch.json',prospective_isolation='discovery-arithmetic-r163-sol-parent/prospective-isolation.json',all_previous_literal_guards_and5570_standing_bytes_retained=True,existing_peer_original_guards_cover_new_namespace=True,independent_review=False,accepted=False,count_change=0,parent_count_at_dispatch=19,publication='STOPPED',status_provenance='Fresh async receipt;ultrafast parallel work explicitly requested. One active child per named model. No polling or foreign live query.')
def update(original):
 x=copy.deepcopy(original)
 x['tasks'][860]['thread_configuration_override']={'observed_utc':now,'model':'gpt-6-astra','reasoningEffort':'high','serviceTier':'ultrafast','receipt':'discovery-arithmetic-r162cu-parent/ultrafast-configure.json','steer':'discovery-arithmetic-r162cu-parent/ultrafast-steer.json','historical_dispatch_options_unchanged':True,'progress_preserved':True,'scope_unchanged':True}
 prefs=x['gpt_subagent_preferences'];prefs['serviceTier']='ultrafast';prefs['source']='Explicit user instruction: use ultrafast with as parallel task as possible; supersedes standard speed.';prefs['transport']='Explicit target.options.serviceTier=ultrafast for new Codex research/review delegates; preserve historical dispatch receipts.'
 prefs['parallel_non_review_models']=['gpt-6-astra','gpt-6.1-sol'];prefs['parallel_policy']='Latest user request authorizes concurrent independent research on the already authorized Codex models;one active child per named model;separate guarded roots;no change to proof or contribution gates.'
 prefs['latest_service_tier_override']={'observed_utc':now,'user_instruction':'use ultrafast with as parallel task as possible','serviceTier':'ultrafast','scope':'New runs;existing Astra thread configured for subsequent turns and progress preserved.','existing_runs':'No cancellation,scope change or duplicate research/review;historical receipt preserved.'}
 x['tasks'].append(copy.deepcopy(fresh));k='ultrafast_parallel_research_20261025';assert k not in x['current_work_snapshot'];x['current_work_snapshot'][k]={'observed_utc':now,'primary_task_index':860,'parallel_task_index':861,'models':['gpt-6-astra','gpt-6.1-sol'],'serviceTier':'ultrafast','count_change':0,'publication':'STOPPED'}
 assert [i for i,(a,b) in enumerate(zip(original['tasks'],x['tasks'])) if a!=b]==[860]
 assert all(x[k]==original[k] for k in original if k not in {'tasks','current_work_snapshot','gpt_subagent_preferences'})
 return x
idx=enc(update(base));merged=enc(update(work));note=('\n\n### Ultrafast parallel research — '+now+'\n\nLatest user instruction enables ultrafast and maximum supported parallel work. Existing Source182 Astra research retains its scope and historical default-tier receipt;its thread is configured high/ultrafast for subsequent turns. A separate Source183 halving-line/k-set discovery starts on Codex/GPT-6.1-Sol/high/ultrafast. One active child per named model;both branches exclude each other using original full-path guards. One catalogue window287105..301105;only183body and183/184titles decoded. Complete source selection12blobs15entries11texts111708bytes,parent proof unread. Full source savings and prior gates remain paid/immutable. Parallel does not merge grades or increment the campaign:19/20,latestR041. Publication/downstreamSTOPPED.\n').encode();ij=hj+note;mj=wj+note
for e in json.loads((N/'private/completed-direct-inputs.json').read_bytes()):
 p=P/e['path'];a=p.read_bytes();assert len(a)==e['bytes'] and sha(a)==e['sha256'] and p.stat().st_mode==e['mode']
protected={'frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r72/source-receipts.json':'6ef7d0bd1f41335856e729095a52b86ca510c2d12e4821ace4d437c29c3705a9','frontier/iterations/i31-nonconical-no-mcm.md':'d606530b18cdd64dcffd4e2e85f871c80842f37a22bf552c180d91f44e7af70a'}
for n,s in protected.items():assert sha((P/n).read_bytes())==s
(D/'parallel-coordination.json').write_bytes(enc({'head':h,'changed_old_tasks':[860],'new_task_index':861,'foreign_task_indices_preserved':foreign,'foreign_top_fields_preserved':foreign_top,'foreign_journal_preserved':wj!=hj,'count_change':0,'live_author_payloads_unmodified':True}))
(N/'registration.json').write_bytes(enc({'task_index':861,'taskId':dispatch['taskId'],'status_at_dispatch':'running','model':'gpt-6.1-sol','serviceTier':'ultrafast','count_change':0}))
paths=[(D/n).relative_to(P).as_posix() for n in ['prepare-parallel.py','ultrafast-configure.json','ultrafast-steer.json','register-parallel.py','parallel-coordination.json']]+[(N/n).relative_to(P).as_posix() for n in ['brief-preparation.json','capabilities.json','dispatch.json','prospective-isolation.json','registration.json']]+[prep['brief'],TP,JP];assert len(paths)==len(set(paths))==13
assert git('rev-parse','HEAD').decode().strip()==h and (P/TP).read_bytes()==wt and (P/JP).read_bytes()==wj and not git('diff','--cached','--name-only').strip()
(P/TP).write_bytes(merged);(P/JP).write_bytes(mj)
subprocess.run(['git','add','--',*[n for n in paths if n not in {TP,JP}]],cwd=P,check=True)
for path,content in [(TP,idx),(JP,ij)]:
 blob=git('hash-object','-w','--stdin',input=content).decode().strip();subprocess.run(['git','update-index','--add','--cacheinfo','100644',blob,'openai-proof-research/'+path],cwd=P,check=True)
assert {n for n in git('diff','--cached','--name-only','-z').decode().split('\0') if n}=={'openai-proof-research/'+n for n in paths}
assert git('show',':openai-proof-research/'+TP)==idx and git('show',':openai-proof-research/'+JP)==ij
subprocess.run(['git','diff','--cached','--check'],cwd=P,check=True)
assert git('rev-parse','HEAD').decode().strip()==h and (P/TP).read_bytes()==merged and (P/JP).read_bytes()==mj
subprocess.run(['git','commit','-m','Enable ultrafast parallel research and start halving-line discovery'],cwd=P,check=True)
assert not git('diff','--cached','--name-only').strip() and git('show','HEAD:openai-proof-research/'+TP)==idx and (P/TP).read_bytes()==merged and git('show','HEAD:openai-proof-research/'+JP)==ij and (P/JP).read_bytes()==mj
for n,s in protected.items():assert sha((P/n).read_bytes())==s
print(json.dumps({'commit':git('rev-parse','HEAD').decode().strip(),'task_index':861,'parallel_models':['gpt-6-astra','gpt-6.1-sol'],'serviceTier':'ultrafast','foreign_edits_preserved':foreign,'count':19}))
