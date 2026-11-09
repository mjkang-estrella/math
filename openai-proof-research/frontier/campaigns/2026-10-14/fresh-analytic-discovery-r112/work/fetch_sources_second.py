import json,re,hashlib,urllib.request,concurrent.futures
from pathlib import Path
B=Path(__file__).resolve().parents[1]; T=json.load(open('sources/preprints-tree.json')); PIN='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
select={'088':['01_introduction.tex','05_position.tex','06_conclusion.tex','07_consequences.tex','main.tex'],'100':['introduction.tex','finite-approximation.tex','linear-coverings.tex'],'230':['introduction.tex','hausdorff.tex','gauge.tex'],'356':['introduction.tex','every-geodesic.tex','calculus.tex','comparison.tex'],'359':['01-introduction.tex','02-reduction.tex','07-hartogs-metric.tex','09-pinching.tex']}
jobs=[]
for k,names in select.items():
 s=(B/'work'/f'catalog-{k}.txt').read_text(); dirs=set(str(Path(x).parent) for x in re.findall(r'\]\((preprints/[^)]+\.pdf)\)',s))
 for e in T['tree']:
  if e['type']=='blob' and any(e['path'].startswith(d+'/') for d in dirs) and Path(e['path']).name in names: jobs.append((k,e))
def fetch(job):
 k,e=job;url=f'https://raw.githubusercontent.com/openai/math/{PIN}/{e["path"]}';out=B/'packet/private/upstream'/e['path'];out.parent.mkdir(parents=True,exist_ok=True)
 try:
  data=urllib.request.urlopen(url,timeout=45).read();blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest();assert blob==e['sha'];out.write_bytes(data)
  return {'family':k,'url':url,'tree_path':e['path'],'tree_blob':e['sha'],'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data),'file':str(out.relative_to(B/'packet')),'status':'success','semantic_read':False}
 except Exception as exc:return {'family':k,'url':url,'error':str(exc),'status':'failed'}
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as pool:r=list(pool.map(fetch,jobs))
old=json.loads((B/'packet/private/upstream/receipts.json').read_text()); (B/'packet/private/upstream/receipts.json').write_text(json.dumps(old+r,indent=2)+'\n');print('Fetched',sum(x['status']=='success' for x in r),'of',len(r),'bytes',sum(x.get('bytes',0) for x in r));print([x for x in r if x['status']!='success'])
