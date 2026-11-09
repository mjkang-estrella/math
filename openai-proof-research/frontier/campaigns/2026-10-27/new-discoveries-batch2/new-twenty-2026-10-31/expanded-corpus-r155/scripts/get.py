import pathlib,urllib.request,json,hashlib,datetime,sys
L=pathlib.Path(__file__).resolve().parents[1]
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':name}
 try:
  with urllib.request.urlopen(url,timeout=15) as f:b=f.read();r.update(status=f.status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(L/'sources'/name).write_bytes(b)
 except Exception as e:r['error']=str(e)
 with (L/'outputs/http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(r,flush=True)
