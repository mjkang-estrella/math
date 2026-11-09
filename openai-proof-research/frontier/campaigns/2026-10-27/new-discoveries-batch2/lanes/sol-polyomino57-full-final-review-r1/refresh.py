import resource,signal,os,json,urllib.request,hashlib,datetime
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(230)
os.environ.update(OPENBLAS_NUM_THREADS='1',OMP_NUM_THREADS='1');D=Path('live');D.mkdir(exist_ok=True);records=[]
def get(url,name):
 t=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'mathematical-review-public-source'}),timeout=25) as r:data=r.read();status=r.status
 except Exception as e:
  records.append(dict(url=url,utc=t,error=str(e)));Path('http.json').write_text(json.dumps(records,indent=2));return None
 (D/name).write_bytes(data);records.append(dict(url=url,utc=t,status=status,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data)));Path('http.json').write_text(json.dumps(records,indent=2));return json.loads(data)
repos={'omega':'the-omega-institute/trureturing','openai':'openai/math','aim':'MColbrook/AIM','count':'suvrit/count-ex-machina'}
for label,repo in repos.items():
 base='https://api.github.com/repos/'+repo
 h=get(base+'/commits/'+('dev' if label=='omega' else 'HEAD'),label+'-head.json')
 if not h:continue
 root=get(base+'/git/trees/'+h['sha'],label+'-root.json')
 if not root:continue
 if label in ['omega','openai']:
  for node in root['tree']:
   if node['path'] in (['D5','Problems'] if label=='omega' else ['preprints']):get(base+'/git/trees/'+node['sha']+'?recursive=1',label+'-'+node['path']+'.json')
 else:get(base+'/git/trees/'+h['sha']+'?recursive=1',label+'-tree.json')
# also main's current head; no undocumented main subtree clearance
get('https://api.github.com/repos/the-omega-institute/trureturing/commits/main','omega-main-head.json')
