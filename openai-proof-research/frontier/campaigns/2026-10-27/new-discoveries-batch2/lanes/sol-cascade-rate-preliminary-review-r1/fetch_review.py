import os,resource,json,urllib.request,hashlib,datetime
from pathlib import Path
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));resource.setrlimit(resource.RLIMIT_CPU,(30,30))
b=Path(__file__).parent; (b/'sources').mkdir(exist_ok=True); receipts=[]
urls={
'supplement':'https://doi.org/10.3150/20-BEJ1299SUPP',
'openai-head':'https://api.github.com/repos/openai/math/commits/HEAD',
'count-head':'https://api.github.com/repos/suvrit/count-ex-machina/commits/HEAD',
'omega-head':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD',
'kraft.pdf':'https://stanford.edu/class/ee377/lecture-notes.pdf',
'vlmc2012.pdf':'https://arxiv.org/pdf/1007.2986',
'nonregular.pdf':'https://arxiv.org/pdf/1907.02442v2'}
for name,url in urls.items():
 r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'independent-mathematical-review'}),timeout=25) as f:data=f.read();r.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));(b/'sources'/name).write_bytes(data)
 except Exception as e:r['error']=str(e)
 receipts.append(r); (b/'http-receipts.json').write_text(json.dumps(receipts,indent=2));print(r)
