import sys,json,hashlib,urllib.request,datetime,subprocess
from pathlib import Path
L=Path(__file__).resolve().parent
url,name=sys.argv[1:3]
p=L/'sources'/name
try:
 if p.exists(): raise RuntimeError('immutable file exists')
 with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Academic-source-audit/1.0'}),timeout=30) as r:
  d=r.read(12000000);status=r.status;headers=dict(r.headers)
 if len(d)>=12000000:raise RuntimeError('size cap')
 p.write_bytes(d)
 rec={'url':url,'file':name,'sha256':hashlib.sha256(d).hexdigest(),'bytes':len(d),'status':status,'headers':headers,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 with (L/'source-receipts.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 if name.endswith('.pdf'):
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
  t=p.with_suffix('.txt');rec={'derived':t.name,'from':name,'sha256':hashlib.sha256(t.read_bytes()).hexdigest()}
  with (L/'source-receipts.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 assert hashlib.sha256(p.read_bytes()).hexdigest()==hashlib.sha256(d).hexdigest()
 print(json.dumps(rec))
except Exception as e:
 with (L/'failures.jsonl').open('a') as f:f.write(json.dumps({'url':url,'error':str(e)})+'\n')
 print(type(e).__name__,str(e));sys.exit(1)
