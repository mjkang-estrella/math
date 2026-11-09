from pathlib import Path
import urllib.request,urllib.error,sys,json,hashlib,datetime,subprocess
L=Path(__file__).resolve().parent
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 row=dict(name=name,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'research-source-review/1.0'})
  with urllib.request.urlopen(req,timeout=25) as r:
   row.update(status=r.status,final_url=r.url);data=r.read(12*1024*1024+1)
   assert len(data)<=12*1024*1024
  p=L/'sources'/name;p.parent.mkdir(exist_ok=True);p.write_bytes(data)
  row.update(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
  # Binding exists before extraction/scientific reading.
  (L/'access.jsonl').open('a').write(json.dumps(row)+'\n')
  if data.startswith(b'%PDF'):
   subprocess.run(['pdftotext','-layout',str(p),str(p)+'.txt'],check=True,timeout=30)
   q=Path(str(p)+'.txt');(L/'access.jsonl').open('a').write(json.dumps(dict(derived=str(q.relative_to(L)),sha256=hashlib.sha256(q.read_bytes()).hexdigest()))+'\n')
  print(json.dumps(row))
 except Exception as e:
  row['failure']=str(e);(L/'access.jsonl').open('a').write(json.dumps(row)+'\n');print(json.dumps(row))
