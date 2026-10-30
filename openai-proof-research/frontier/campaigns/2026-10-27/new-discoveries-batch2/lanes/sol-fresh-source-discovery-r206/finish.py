import work, json, re
from pathlib import Path
L=work.L;B=work.B
terms=['2610.40321','Terry Easlick','Computer-Assisted Results','non-transitive dice','nontransitive dice','minimal winning advantage','uniform and minimal','10.1002/jcd.21563','10.4169/college.math.j.48.1.10','10.37236/11918','2505.21950','Joshua Rooney']
work.screen(terms,'final-qualified-screen.json')
a=json.loads((L/'indexes/inherited-aliases.json').read_text());records=[];hits={t:[] for t in terms}
for r in a['records']:
 p=Path(r['reference_path']);p=p if p.is_absolute() else work.R/p
 if not p.exists():records.append({'reference_path':str(p),'missing':True});continue
 d=p.read_bytes();h=work.sha(d);oldcopy=B/'lanes/sol-fresh-source-discovery-r205'/r['copy']
 if oldcopy.exists() and work.sha(oldcopy.read_bytes())==h:c=str(oldcopy)
 else:
  c='alias-delta/'+work.sha(str(p).encode())[:24]+'-'+p.name;work.put(c,d);c=str(L/c)
 records.append({'reference_path':str(p),'snapshot':c,'sha256':h,'previous':r['sha256'],'changed':h!=r['sha256'],'qualification':'inherited alias, not original'})
 s=d.decode(errors='replace').lower()
 for t in terms:
  if t.lower() in s:hits[t].append(str(p))
work.js('alias-screen.json',{'utc':work.now(),'records':records,'hits':hits,'limit':'Inherited original-path aliases retained separately; provenance not inferred from equal bytes.'})
primary=[]
for p in sorted((L/'retrieval').glob('*.json')):
 x=json.loads(p.read_text())
 if 'sha256' not in x:continue
 n=p.name[:-5];o=L/'primary/original'/n;c=L/'primary/copy'/n
 assert work.sha(o.read_bytes())==work.sha(c.read_bytes())==x['sha256']
 primary.append({'url':x['url'],'utc':x['utc'],'original':str(o),'copy':str(c),'sha256':x['sha256'],'acquisition_digest_before_read':True,'separate_pre_read_disk_check':False,'after_disk_check':True,'frozen_before_read':True})
guard=B/'lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
work.put('assigned/helper_guard.py',guard.read_bytes())
work.js('scientific-bindings.json',{'utc':work.now(),'primary':primary,'guard':{'original':str(guard),'copy':'assigned/helper_guard.py','sha256':work.sha(guard.read_bytes())},'qualification':'Raw scientific source original/copy pairs frozen before extraction; historical reports are point-in-time snapshots; administrative files are not scientific bindings.'})
work.put('indexes/inherited-corrected-index-bindings.json',(B/'lanes/sol-fresh-source-discovery-r205/index-bindings.json').read_bytes())
idx=json.loads((L/'qualified-original-index.json').read_text())
work.js('historical-after.json',{'utc':work.now(),'records':[{'original':r['original'],'snapshot':r.get('snapshot',r.get('reused_snapshot')),'snapshot_sha256':work.sha((L/r['snapshot'] if 'snapshot'in r else Path(r['reused_snapshot'])).read_bytes()),'expected':r['sha256'],'live_sha256':work.sha(Path(r['original']).read_bytes()) if Path(r['original']).exists() else None} for r in idx['records'] if not r.get('missing')],'qualification':'Live report drift is administrative history evolution, not scientific source drift.'})
work.js('registry-screen.json',{'utc':work.now(),'coverage':'arXiv current title and exact identifier public retrieval only','receipts':['retrieval/search.html.json','retrieval/balanced-search.html.json','retrieval/target-search.html.json'],'limits':['Exact identifier search redirects to primary abstract, not independent citing search.','No current complete public proof registry head or body coverage. GitHub API/raw/codeload/diff/patch routes were excluded by instruction, not retried.','No MathDB mutation or unresolvedness inference. No subscription-index or worldwide novelty clearance.','No parked historical merge tree or capped interval reopened.']})
work.js('provenance.json',{'utc':work.now(),'status':'UNRESOLVED; zero nominations','scientific_bindings':'scientific-bindings.json','history_index':'qualified-original-index.json','aliases':'alias-screen.json','administrative_snapshot_only':'administrative/','chronology':{'Easlick':'arXiv:2610.40321v1 submitted 2026-10-29 15:54:42 UTC; primary PDF internal date October 30, 2026. Abstract lists only v1.','Rooney':'arXiv:2505.21950v1 submitted 2025-05-28 04:03:03 UTC. Unversioned PDF response explicitly names v1; abstract lists only v1.','classical':'Rooney public proof predates Easlick; applies to unrestricted labels and existential face count, not fixed resource question. No separate version-of-record asserted.'},'counts':[9,39,40],'lane_credit':0,'limits':'Bounded historical screen and actual primary proof comparison only. Current full registry and all-history clearance unavailable. No worldwide priority claim.'})
print('primary',len(primary),'qualified originals',len(idx['records']),'aliases',len(records),'alias hits',{t:len(v) for t,v in hits.items()})
