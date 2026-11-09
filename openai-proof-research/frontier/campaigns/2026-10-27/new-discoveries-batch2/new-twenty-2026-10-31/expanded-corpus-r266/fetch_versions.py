import resource,os,json,hashlib,urllib.request,datetime,concurrent.futures,subprocess,re,time
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
p=Path(__file__).resolve().parent;(p/'sources').mkdir(exist_ok=True)
r=json.loads((p/'reservation.json').read_text());receipts=[]
def fetch(job):
 name,url=job;t=datetime.datetime.now(datetime.timezone.utc).isoformat();v={'name':name,'url':url,'utc':t}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathematicalResearch/1.0'}),timeout=14) as f:
   data=f.read(18000000);v.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));(p/'sources'/name).write_bytes(data)
  if name.endswith('.pdf') and data.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p/'sources'/name),str(p/'sources'/name.replace('.pdf','.txt'))],timeout=15,check=True)
 except Exception as e:v['error']=str(e)
 return v
jobs=[]
for row in r['rows']:
 ident=str(row['mathdb_id']);a=row['source_url'].split('/abs/')[1]
 versions=re.findall(r'\[v(\d+)\]',(p/'sources'/(ident+'.abs.html')).read_text())
 for v in versions: jobs.append((ident+'v'+v+'.pdf','https://arxiv.org/pdf/'+a+'v'+v))
jobs.extend([('descycles.pdf','https://math.dartmouth.edu/~sergi/papers/descycles_webpage.pdf'),('edge-depth-summary.pdf','https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/1769-12.pdf'),('bialostocki-journal.pdf','https://www.impan.pl/shop/en/publication/transaction/download/product/82561')])
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for v in ex.map(fetch,jobs):receipts.append(v);print(v['name'],v.get('status',v.get('error')),flush=True)
(p/'sources/version-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
