import sys,urllib.request,pathlib,json,datetime,hashlib
L=pathlib.Path(__file__).resolve().parents[1]
for x in sys.argv[1:]:
 name,url=x.split('=',1);r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'sources/'+name}
 try:
  with urllib.request.urlopen(url,timeout=20) as f:b=f.read();r.update(status=f.status,final_url=f.url)
  (L/'sources'/name).write_bytes(b);r.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 except Exception as e:r['error']=str(e)
 with (L/'outputs/http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(json.dumps(r),flush=True)
