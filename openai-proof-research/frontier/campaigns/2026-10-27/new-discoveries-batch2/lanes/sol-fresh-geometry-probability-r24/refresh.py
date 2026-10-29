import os
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
import resource,signal,json,urllib.request,urllib.error,hashlib,datetime
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(35,35));signal.alarm(100)
b=Path(__file__).parent;s=b/'sources';old=b.parent/'sol-mean-cascade-current-prior-audit-r1/sources';log=[];blocked=set()
def get(name,url):
 host=urllib.request.urlparse(url).netloc if False else url.split('/')[2]
 if host in blocked:return None
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'source-research/1.0'}),timeout=18) as r:data=r.read(16000000);status=r.status
  (s/name).write_bytes(data);log.append(dict(name=name,url=url,status=status,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),sha256=hashlib.sha256(data).hexdigest()));return json.loads(data) if name.endswith('.json') else data
 except Exception as e:
  log.append(dict(name=name,url=url,error=str(e),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
  if getattr(e,'code',None) in [403,429]:blocked.add(host)
 finally:(b/'http-log.json').write_text(json.dumps(log,indent=2))
if (b/'http-log.json').exists() and any(x.get('error','').startswith('HTTP Error 403') or x.get('error','').startswith('HTTP Error 429') for x in json.loads((b/'http-log.json').read_text())):
 raise SystemExit('Saved access failure: no API refresh; use verified complete bases and coverage.json.')
coverage={}
for n,repo in [('omega','the-omega-institute/trureturing'),('openai','openai/math'),('count','suvrit/count-ex-machina'),('aim','MColbrook/AIM')]:
 h=get(n+'-head.json','https://api.github.com/repos/'+repo+'/commits/HEAD')
 if not h:coverage[n]={'gap':'head fetch failure'};continue
 coverage[n]={'head':h['sha'],'date':h['commit']['committer']['date'],'trees':[]}
 if n=='aim':bases=[b.parent/'root-log-arctangent-acceptance-r1/aim-screen/tree.json']
 elif n=='omega':bases=[old/'omega-D5-tree.json',old/'omega-Problems-tree.json']
 elif n=='openai':bases=[old/'openai-preprints-tree.json']
 else:bases=[old/'count-full-tree.json']
 root=get(n+'-root.json','https://api.github.com/repos/'+repo+'/git/trees/'+h['commit']['tree']['sha'])
 if not root:continue
 for p in bases:
  j=json.loads(p.read_text());sha=j['sha'];target='D5' if '-D5-' in p.name else 'Problems' if '-Problems-' in p.name else 'preprints' if n=='openai' else None
  now=next((e['sha'] for e in root['tree'] if e['path']==target),None) if target else root['sha']
  if now==sha:
   (s/(n+'-'+p.name)).write_bytes(p.read_bytes());coverage[n]['trees'].append({'base':str(p),'base_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'tree_sha':sha,'entries':len(j['tree']),'truncated':j.get('truncated'),'unchanged':True})
  else:
   t=get(n+'-'+(target or 'full')+'-current-tree.json','https://api.github.com/repos/'+repo+'/git/trees/'+now+'?recursive=1')
   coverage[n]['trees'].append({'tree_sha':now,'entries':len(t.get('tree',[])) if t else None,'truncated':t.get('truncated') if t else None,'unchanged':False})
(b/'coverage.json').write_text(json.dumps(coverage,indent=2));print(json.dumps(coverage,indent=2))
get('clopen.html','https://clopen.solutions/')
