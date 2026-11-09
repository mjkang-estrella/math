import urllib.request,hashlib,json,datetime,pathlib,sys
L=pathlib.Path(__file__).resolve().parent
url,name=sys.argv[1:]; out=L/'sources'/name
rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':str(out.relative_to(L))}
try:
 with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'math-source-research/1.0'}),timeout=35) as r:
  data=r.read(20000001); assert len(data)<=20000000,'cap';rec.update(status=r.status,content_type=r.headers.get('Content-Type'),final_url=r.url)
 if name.endswith('.pdf'): assert data.startswith(b'%PDF-'),'not PDF'
 out.write_bytes(data);rec.update(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
except Exception as e: rec['failure']=str(e)
with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
print(json.dumps(rec))
