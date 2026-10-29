import resource,signal,os
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,resource.RLIM_INFINITY));resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(230)
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
import json,hashlib,zipfile,urllib.request,datetime
from pathlib import Path
R=Path(__file__).parent; B=R.parent.parent; F=R.parent/'root-steiner-reflection-final-review-freeze-r1'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
freeze=json.loads((R/'review-freeze.json').read_text()); checks={}
for n,v in freeze.items():
 assert sha(R/n)==v['sha256'] and sha(F/n)==v['sha256']; checks[n]=v
with zipfile.ZipFile(R/'steiner-final-review-packet.zip') as z:
 assert len(z.namelist())==65 and len(set(z.namelist()))==65
 assert not any(n.endswith(('.olean','.ilean','.o','.ir','.so')) for n in z.namelist())
manifest=json.loads((R/'extracted/packet-manifest.json').read_text());assert len(manifest)==64
for n,h in manifest.items():assert sha(R/'extracted'/n)==h,n
nested=R/'extracted/evidence/root-steiner-reflection-formal-replay-r1/steiner-source-component.zip'
assert sha(nested)=='7065840eed6aab457eb9e50e5c59e04aed5c8e37433d8063bc815f6c6707ba61'
(R/'hash-before.json').write_text(json.dumps({'freeze':checks,'payload':manifest,'entries':65,'nested':sha(nested)},indent=2))
(R/'live').mkdir(exist_ok=True); rows=[]
def fetch(n,u):
 t=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Independent-research-review/1.0'}),timeout=12) as f:b=f.read(12000000);status=f.status
  (R/'live'/n).write_bytes(b);rows.append(dict(utc=t,url=u,file='live/'+n,status=status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b)));return json.loads(b) if n.endswith('.json') else b
 except Exception as e:rows.append(dict(utc=t,url=u,error=str(e),retry=False));return None
fetch('target.pdf','https://arxiv.org/pdf/2505.10501v1')
fetch('target.html','https://arxiv.org/abs/2505.10501')
fetch('qi.pdf','https://www.polyu.edu.hk/ama/staff/new/qilq/qi-eigen-1.pdf')
fetch('author.html','https://people.math.sc.edu/cooper/works.html')
heads={}
for n,repo,branch in [('omega','the-omega-institute/trureturing','dev'),('omega-main','the-omega-institute/trureturing','main'),('openai','openai/math','main'),('aim','MColbrook/AIM','main'),('count','teorth/erdosproblems','main')]:
 data=fetch(n+'-head.json',f'https://api.github.com/repos/{repo}/commits/{branch}')
 if data:heads[n]=data['sha']
if 'omega' in heads:
 root=fetch('omega-root.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+heads['omega'])
 if root:
  for i in root['tree']:
   if i['path'] in ['D5','Problems']:fetch('omega-'+i['path']+'.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+i['sha']+'?recursive=1')
 for name in ['jana-mahato-sivasubramanian-2025-steiner-path-peak.md','zhang-tian-2025-steiner-diameter-radius-trees.md']:
  fetch(name,'https://raw.githubusercontent.com/the-omega-institute/trureturing/'+heads['omega']+'/Problems/'+name)
(R/'http.json').write_text(json.dumps(rows,indent=2));(R/'heads.json').write_text(json.dumps(heads,indent=2));print(json.dumps(rows,indent=2))
