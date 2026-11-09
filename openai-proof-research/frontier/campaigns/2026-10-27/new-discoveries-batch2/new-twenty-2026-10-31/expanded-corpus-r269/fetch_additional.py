from pathlib import Path
import json,urllib.request,hashlib,datetime,resource,concurrent.futures
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent;s=p/'sources';s.mkdir(exist_ok=True)
rows=json.loads((p/'extracted-records.json').read_text())
jobs=[]
import re
for i,v in rows.items():
 html=(s/(i+'-abs.html')).read_text()
 versions=sorted(set(map(int,re.findall(r'\[v(\d+)\]',html))))
 for ver in versions[:-1]: jobs.append((i+'-v'+str(ver)+'.pdf',v['record']['source_url'].replace('/abs/','/pdf/')+'v'+str(ver)))
jobs += [('cutler.pdf','https://arxiv.org/pdf/1410.7726'),('bahmanian.pdf','https://d-nb.info/1387819259/34'),('shift-prior.html','https://holdfirst.wordpress.com/2012/09/17/divisibility-property-of-the-number-of-permutations-realized-by-a-shift-2/'),('rigidity.pdf','https://arxiv.org/pdf/2204.02503'),('registry-openai.md','https://raw.githubusercontent.com/openai/math/HEAD/CONTENTS.md'),('registry-pool.yml','https://raw.githubusercontent.com/Vilin97/lean-pool/HEAD/LeanPool/projects.yml'),('registry-trureturing.md','https://raw.githubusercontent.com/the-omega-institute/trureturing/HEAD/README.md')]
def fetch(job):
 name,url=job;r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':str(s/name)}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source review'}),timeout=10) as q:
   b=q.read(12*1024**2);r.update(status=q.status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(s/name).write_bytes(b)
 except Exception as e:r['error']=str(e)
 (s/(name+'.receipt.json')).write_text(json.dumps(r,indent=2)+'\n');return r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 for r in pool.map(fetch,jobs):print(json.dumps(r),flush=True)
