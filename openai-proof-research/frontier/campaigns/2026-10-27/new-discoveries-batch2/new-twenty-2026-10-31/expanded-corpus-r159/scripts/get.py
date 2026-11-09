import pathlib,sys,urllib.request,json,datetime,hashlib
D=pathlib.Path(__file__).resolve().parents[1]
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=15) as f:
   b=f.read();r.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  (D/'sources'/name).write_bytes(b)
 except Exception as e:r['error']=str(e)
 (D/'sources'/ (name+'.receipt.json')).write_text(json.dumps(r,indent=2)+'\n')
 print(name,r,flush=True)
