import resource,signal
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,resource.RLIM_INFINITY));resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(230)
import json,hashlib,urllib.request,datetime,shutil
from pathlib import Path
R=Path(__file__).parent;rows=json.loads((R/'http.json').read_text());head=json.loads((R/'heads.json').read_text())['omega']
def fetch(n,u):
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Independent-research-review/1.0'}),timeout=12) as f:b=f.read(12000000)
  (R/'live'/n).write_bytes(b);rows.append(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),url=u,file='live/'+n,status=200,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
 except Exception as e:rows.append(dict(url=u,error=str(e),retry=False))
fetch('author-current.html','https://people.math.sc.edu/cooper/')
for n,p in [('radius.lean','D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius.lean'),('peak.lean','D5/S3/Combinatorics/SpectralGraph/JanaMahatoSivasubramanianPeakRefutation.lean')]:fetch(n,f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{head}/{p}')
(R/'http.json').write_text(json.dumps(rows,indent=2))
C=R/'cached-primary';C.mkdir(exist_ok=True)
for n in ['companion.pdf','companion.txt','even.pdf','even.txt','old-spectrum-published.pdf','old-spectrum-published.txt','steiner-post.txt']:
 p=R.parent/'sol-steiner-reflection-preliminary-review-r1/frozen/sources'/n
 if p.exists():shutil.copyfile(p,C/n)
scope={}
for name,p in [('omega-main',R.parent/'sol-fresh-source-discovery-r43/sources/omega-main-tree.json'),('aim',R.parent/'sol-fresh-source-discovery-r43/sources/aim-tree.json'),('count',R.parent/'sol-fresh-source-discovery-r43/sources/count-tree.json'),('openai',R.parent/'sol-steiner-reflection-preliminary-review-r1/frozen/sources/inherited-cached-cached-inherited-openai-openai-preprints-tree.json')]:
 data=json.loads(p.read_text());assert not data['truncated'];shutil.copyfile(p,C/(name+'-tree.json'))
 matches=[i['path'] for i in data['tree'] if any(q in i['path'].lower() for q in ['steiner','hyperdetermin','cooper'])]
 scope[name]={'cached_tree_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'entries':len(data['tree']),'truncated':False,'path_matches':matches}
(R/'registry-scopes.json').write_text(json.dumps(scope,indent=2));print(json.dumps(scope,indent=2))
