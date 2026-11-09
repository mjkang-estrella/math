import requests,json,resource,hashlib,datetime,concurrent.futures,subprocess
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent;(p/'sources').mkdir(exist_ok=True)
d=json.loads((p/'literal-provenance.json').read_text()); tasks=[]
for i,x in d.items():
 a=x['record']['source_url'].split('/abs/')[1]
 if not any(t[0]==a for t in tasks):tasks.append((a,i))
def run(t):
 a,i=t; rows=[]
 for kind,url in [('abs','https://arxiv.org/abs/'+a),('pdf','https://arxiv.org/pdf/'+a)]:
  r=dict(id=i,arxiv=a,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
  try:
   z=requests.get(url,timeout=7);r.update(status=z.status_code,sha256=hashlib.sha256(z.content).hexdigest(),bytes=len(z.content)); f=p/'sources'/f'{i}.{kind}';f.write_bytes(z.content);r['file']=str(f)
   if kind=='pdf' and z.content.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(f),str(f.with_suffix('.txt'))],timeout=12,check=True)
  except Exception as e:r['error']=str(e)
  rows.append(r)
 return rows
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for rows in ex.map(run,tasks):
  with (p/'receipts.jsonl').open('a') as f:
   for r in rows:f.write(json.dumps(r)+'\n')
  print([(r['id'],r.get('status'),r.get('error')) for r in rows],flush=True)
