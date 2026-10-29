import resource,signal,os
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,resource.RLIM_INFINITY));resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(230)
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
import json,hashlib,urllib.request,datetime,itertools,time
from pathlib import Path
R=Path(__file__).parent; rows=json.loads((R/'http.json').read_text())
def fetch(n,u):
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Independent-research-review/1.0'}),timeout=12) as f:b=f.read(12000000);status=f.status
  (R/'live'/n).write_bytes(b);rows.append(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),url=u,file='live/'+n,status=status,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()));return json.loads(b) if n.endswith('.json') else b
 except Exception as e:rows.append(dict(url=u,error=str(e),retry=False));return None
fetch('count-correct-head.json','https://api.github.com/repos/suvrit/count-ex-machina/commits/main')
# Own complete path/blob delta against latest supplied r43 snapshot.
delta={}
for n in ['D5','Problems']:
 old=json.loads((R.parent/'sol-fresh-source-discovery-r43/sources'/('omega-'+n+'.json')).read_text());new=json.loads((R/'live'/('omega-'+n+'.json')).read_text())
 assert not old['truncated'] and not new['truncated']
 a={i['path']:i for i in old['tree'] if i['type']=='blob'};b={i['path']:i for i in new['tree'] if i['type']=='blob'}
 changed=[p for p in a.keys()|b.keys() if a.get(p,{}).get('sha')!=b.get(p,{}).get('sha')];delta[n]={'old_entries':len(old['tree']),'new_entries':len(new['tree']),'changed_blobs':changed,'matches':[p for p in b if any(t in p.lower() for t in ['steiner','hyperdetermin','cooper','reflection'])]}
 head=json.loads((R/'heads.json').read_text())['omega']
 for k,p in enumerate(changed):
  if p in b:fetch(f'delta-{n}-{k}.txt',f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{head}/{n}/{p}')
(R/'delta.json').write_text(json.dumps(delta,indent=2));(R/'http.json').write_text(json.dumps(rows,indent=2));print(json.dumps(delta,indent=2))
# Integer evaluation of every triple contraction at four nodes proves cubic identity.
t=time.monotonic();checks=[]
for s in range(4):
 x=[s+29]+[-1]*29;y15=[s-15*v for v in x];g=[0]*30
 for j,k,h in itertools.product(range(30),repeat=3):
  terms={j,k,h};w=x[j]*x[k]*y15[h]
  for i in range(30):
   q=terms|{i};dist=len(q-{0}) if len(q)>1 else 0
   g[i]+=dist*w
 d=2*s**3-26*s**2+32*s+30;L=86*s**3-728*s**2+894*s+810
 assert all(2*g[i]==(29*d if i==0 else L) for i in range(30))
 checks.append({'s':s,'15g_center':g[0],'15g_leaves':sorted(set(g[1:]))})
def d(s):return 2*s**3-26*s**2+32*s+30
def L(s):return 86*s**3-728*s**2+894*s+810
def P(s):return 29*d(s)+(s+29)**3*L(s)
assert P(5)==-85295770 and P(8)==273617240
assert 29*d(5)==-6090 and L(5)==-2170
result={'status':'PASS','route':'Integer triple sums from distinct terminal-set leaf count, all30 coordinates at four integer nodes; both sides degree at most3, so coefficient identities follow exactly. No candidate checker used.','checks':checks,'P5':P(5),'P8':P(8),'elapsed_seconds':time.monotonic()-t,'quartic_at5':'-14413/3','maxrss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
(R/'own-math.json').write_text(json.dumps(result,indent=2));print(result)
