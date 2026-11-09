from pathlib import Path
import urllib.request,hashlib,json,datetime,subprocess
O=Path(__file__).resolve().parent
ids=['2507.17981','2307.07495','2305.19632','2610.24456','2608.26854','2608.21790','2608.21202','2608.17863','2502.10068','1911.08129']
for id in ids:
 url='https://arxiv.org/pdf/'+id
 row={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=18) as r:data=r.read(8000000);row.update(status=r.status,final_url=r.url)
 except Exception as e:row['error']=str(e);data=str(e).encode()
 p=O/'sources'/(id+'.pdf');p.write_bytes(data)
 row.update(path=str(p.relative_to(O)),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
 with (O/'http.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
 if data.startswith(b'%PDF'):
  q=O/'frozen'/p.name;q.write_bytes(data);assert hashlib.sha256(q.read_bytes()).hexdigest()==row['sha256']
  w=O/'work'/p.name;w.write_bytes(data);assert w.read_bytes()==q.read_bytes()
  r=subprocess.run(['pdftotext','-layout',str(w),str(O/'work'/(id+'.txt'))],capture_output=True)
  (O/'receipts'/(id+'-extract.stderr')).write_bytes(r.stderr)
 print(id,row.get('status',row.get('error')),flush=True)
