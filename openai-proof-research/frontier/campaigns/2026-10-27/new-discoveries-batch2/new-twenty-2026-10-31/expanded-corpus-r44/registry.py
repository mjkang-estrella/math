import requests,json,hashlib,datetime,resource,os,re
from pathlib import Path
P=Path(__file__).resolve().parent;resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(100,100));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);receipts=json.loads((P/'source-receipts.json').read_text());report={}
for name,sha in [('omega-combinatorics','521c5a3b519f682ac79330c39dc0aa9f3d8752e2'),('omega-blueprint-combinatorics','097c5ed0599da982d43e9ef682d555dfe744fe6b')]:
 u='https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+sha+'?recursive=1';r=requests.get(u,timeout=40);(P/'sources'/(name+'.json')).write_bytes(r.content);receipts.append({'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':r.status_code,'sha256':hashlib.sha256(r.content).hexdigest(),'file':'sources/'+name+'.json'})
 if r.status_code==200:
  t=r.json();report[name]={'truncated':t.get('truncated'),'entries':len(t.get('tree',[])),'path_hits':[x['path'] for x in t.get('tree',[]) if re.search('crumby|hyperopic|bicyclic|spum|matchingforcing|forcingset',x['path'],re.I)]}
f=P.parent/'fresh-corpus-r10/sources/registry-preprints.json';raw=f.read_bytes();assert hashlib.sha256(raw).hexdigest()=='6ac178a0ebcece8f2c2c9aa1c22022068110bbdae4bb3d1ffa9f1b693b9e0305';t=json.loads(raw);report['openai']={'file':str(f.resolve()),'sha256':hashlib.sha256(raw).hexdigest(),'head':'4eaee87548250b2682affda7d05d947c05554bae','truncated':t.get('truncated'),'entries':len(t['tree']),'hits':[x['path'] for x in t['tree'] if re.search('crumby|hyperopic|bicyclic|spum|forcing.number|Peisert',x['path'],re.I)]}
report['limit']='Path screen only; Omega root tree truncated, two relevant combinatorics subtrees separately checked. No proof-body or global novelty clearance.'
(P/'registry-screen.json').write_text(json.dumps(report,indent=2)+'\n');(P/'source-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n');print(json.dumps(report,indent=2))
