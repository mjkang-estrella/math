"""One-time two discovery dispatch integration after closed T360S147 reviews."""
import datetime,hashlib,json
from pathlib import Path
O=Path(__file__).resolve().parent;B=O.parent;P=B.parents[2]
def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
now=datetime.datetime.now(datetime.timezone.utc).isoformat();t=read(B/'tasks.json');assert len(t['tasks'])==518;assert t['tasks'][512]['correctness']=='PASS' and t['tasks'][512]['contribution']=='TECHNICAL'
dispatches=[]
for kind,n in [('structural',154),('analytic',148)]:
 name=kind+str(n)+'-dispatch.json';d=read(O/name)['structuredContent'];assert d['status']=='running' and d['providerInstanceId']=='codex' and d['model']=='gpt-6-astra' and {e['id']:e['value'] for e in d['options']}=={'reasoningEffort':'high','serviceTier':'default'}
 brief='expanded-target-2026-10-17/fresh-'+kind+'-r'+str(n)+'-brief.txt';t['tasks'].append({'observed_utc':now,'target':{'providerInstanceId':'codex','model':'gpt-6-astra','options':{'reasoningEffort':'high','serviceTier':'default'}},**d,'role':'research','output':'fresh-'+kind+'-discovery-r'+str(n),'brief':brief,'brief_sha256':sha(B/brief),'parent_count_at_dispatch':19,'accepted':False,'count_change':0,'publication':'STOPPED','status_provenance':'Actual fresh async delegate_task response,not later liveness polling.'});dispatches.append({'observed_utc':now,'record':'post-t360s147-discovery/'+name,**d})
msg='After committed T360S147 full correctnessPASS/contributionTECHNICAL(conditiondischarged,no count),distinct Structural154 and Analytic148 actually dispatched CodexGPT-6Astra/high/default. Arithmetic119 retained its third slot. Before both new briefs/roots,saved original arithmetic119 initial prompt already excluded154and148;new initial prompts mutually exclude each other/119,allT360S147 and stated future120/155/149 at every depth/flat alias. No active-peer status/body read,steer,watcher,grade-shopping review or idle followup. Completed full technical scopes/proofs remain immutable. Sustained distinct mathematical research,at mosttwofamilies includingnavigation,actual source/primary/history proof reading and strongest integrated reduction required. All evidence/read/right limitations retained.19/20/latestR041,one substantial acceptance remains;publication STOPPED.'
t['last_parent_progress']={'observed_utc':now,'note':msg,'newAccepted':19,'remaining':1,'publication':'STOPPED'}
s=t['current_work_snapshot'];s.update(observed_utc=now,note=msg,status_note=msg,fresh_discovery_current=[t['tasks'][i]['output'] for i in [517,518,519]],t3_current_confirmed_running=[t['tasks'][i]['taskId'] for i in [517,518,519]])
s['t3_dispatch_observations']+=dispatches;s['t360s147_reviews']['discovery_deferred']=False;s['arithmetic_discovery_deferred_for_t360s147_reviews']['review_outcomes_still_pending']=False
s['post_t360s147_distinct_discovery']={'observed_utc':now,'prospective_isolation':'post-t360s147-discovery/prospective-isolation.json','structural154_taskId':t['tasks'][518]['taskId'],'analytic148_taskId':t['tasks'][519]['taskId'],'arithmetic119_original_initial_brief_excludes_both':True,'new_initial_briefs_mutually_excluded':True,'no_peer_status_body_read_or_steer':True,'no_new_t360s147_review':True,'accepted':False,'count_change':0,'publication':'STOPPED'}
dump(B/'tasks.json',t)
with (P/'frontier/NEW-TEN-2026-10-14.md').open('a') as f:f.write('\n\n## Parent update — distinct discovery after T360S147 review disposition\n\n'+msg+'\n')
parent=['prospective-isolation.json','integration-baseline.json','capabilities.json','structural154-dispatch.json','analytic148-dispatch.json','integrate.py','integration-check.py','integration-validation.json','staging-allowlist.json'];briefs=[t['tasks'][i]['brief'] for i in [518,519]]
files=[str((O/n).relative_to(P)) for n in parent]+[str((B/n).relative_to(P)) for n in briefs]+[str((B/'tasks.json').relative_to(P)),'frontier/NEW-TEN-2026-10-14.md'];assert len(files)==13
dump(O/'staging-allowlist.json',{'files':files,'limits':'Parent dispatch metadata,original two initial briefs and shared ledger/journal only.No active research outputs or protected bodies.'})
