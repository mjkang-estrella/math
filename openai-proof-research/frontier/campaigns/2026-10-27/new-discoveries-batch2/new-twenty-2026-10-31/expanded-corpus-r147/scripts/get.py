import pathlib,urllib.request,json,hashlib,datetime,sys
D=pathlib.Path(__file__).resolve().parents[1]
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=15) as r:
   b=r.read();(D/'sources'/name).write_bytes(b);rec.update(status=r.status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),final_url=r.url)
 except Exception as e:rec['error']=str(e)
 (D/'sources'/(name+'.receipt.json')).write_text(json.dumps(rec,indent=2)+'\n');print(name,rec,flush=True)
