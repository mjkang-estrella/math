import os
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
import resource,signal,json,hashlib,datetime
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(15,15));signal.alarm(20)
b=Path(__file__).parent;B=b.parent.parent;s=b.parent/'sol-fresh-analysis-source-r22/sources'
terms=['girgensohn','borwein','zapata','sinusoidal','2603.14548','373621','thetaquot','theta-quot','kovalev']
heads={'omega':'fb587b0e94c9169d5d1076c186dd766253eb5255','openai':'7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a','aim':'8729eab98bafe409b66c5e39253bf56569a62327','count':'dbf673741a54c7dc9d88a6aec0e8148a538f4a3a'}
rows=[]
for name,repo in [('omega-D5-current-tree.json','omega'),('omega-Problems-current-tree.json','omega'),('openai-openai-preprints-tree.json','openai'),('aim-full-current-tree.json','aim'),('count-count-full-tree.json','count')]:
 p=s/name;j=json.loads(p.read_text());rows.append({'input':str(p.resolve()),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'head':heads[repo],'tree_sha':j['sha'],'entries':len(j['tree']),'truncated':j.get('truncated'),'matches':[x['path'] for x in j['tree'] if any(t in x['path'].lower() for t in terms)]})
prior=[]
for p in sorted(b.parent.glob('*/SUMMARY.md')):
 txt=p.read_text();prior.append({'path':str(p.resolve()),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'first_line':txt.splitlines()[0] if txt else ''})
(b/'path-screen.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'coverage':'dated complete snapshots; path-only, no current-head clearance','terms':terms,'registries':rows,'summaries':prior},indent=2))
print([(x['input'].split('/')[-1],x['entries'],len(x['matches'])) for x in rows])
