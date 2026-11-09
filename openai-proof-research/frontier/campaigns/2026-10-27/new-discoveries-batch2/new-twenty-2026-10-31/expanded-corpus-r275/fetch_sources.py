import resource,os,time,json,hashlib,urllib.request,concurrent.futures,subprocess
from pathlib import Path
from datetime import datetime,timezone
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
p=Path(__file__).resolve().parent;s=p/'sources';s.mkdir(exist_ok=True)
r=json.loads((p/'reservation.json').read_text()); receipts=[]
def fetch(pair):
 name,url=pair; a={'url':url,'utc':datetime.now(timezone.utc).isoformat(),'file':str(s/name)}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source review (public read-only)'}),timeout=12) as f:
   data=f.read(12000000);a.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));(s/name).write_bytes(data)
  if data.startswith(b'%PDF'): subprocess.run(['pdftotext','-layout',str(s/name),str((s/name).with_suffix('.txt'))],timeout=12,check=True)
 except Exception as e:a['error']=str(e)
 return a
jobs=[]
for row in r['rows']:
 url=row['source_url']; i=row['mathdb_id']
 if 'arxiv.org/abs/' in url:
  ar=url.split('/abs/')[1];jobs.extend([(f'{i}-abs.html',url),(f'{i}-latest.pdf','https://arxiv.org/pdf/'+ar)])
 else:jobs.append((f'{i}-source.html',url))
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 for a in pool.map(fetch,jobs):receipts.append(a);print(json.dumps(a),flush=True)
(p/'receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
