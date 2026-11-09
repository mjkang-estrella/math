import requests,json,hashlib,datetime,concurrent.futures,subprocess,resource,os
from pathlib import Path
P=Path(__file__).resolve().parent
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(180,180));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);(P/'sources').mkdir(exist_ok=True)
urls={'openai-head.json':'https://api.github.com/repos/openai/math/commits/HEAD','omega-head.json':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD'}
for a in ['2106.09209','2106.09238','2107.09025','2108.02363','2108.08118','2107.07368','2108.03943','2105.13357','2107.04998']:urls[a+'.pdf']='https://arxiv.org/pdf/'+a
receipts=[]
def get(kv):
 n,u=kv;d={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  r=requests.get(u,timeout=35);d.update(status=r.status_code,final_url=r.url,sha256=hashlib.sha256(r.content).hexdigest(),bytes=len(r.content),file='sources/'+n);(P/'sources'/n).write_bytes(r.content)
  if n.endswith('json') and r.status_code==200:d['head']=r.json().get('sha')
  if r.status_code==200 and r.content.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(P/'sources'/n),str(P/'sources'/n.replace('.pdf','.txt'))],timeout=25,check=True)
 except Exception as e:d['error']=str(e)
 return d
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for r in ex.map(get,urls.items()):receipts.append(r);print(json.dumps(r),flush=True)
(P/'source-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
