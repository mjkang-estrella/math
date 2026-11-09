import urllib.request,pathlib,json,hashlib,datetime
D=pathlib.Path(__file__).resolve().parents[1]
items=[('grid-2023.pdf','https://doiserbia.nb.rs/img/doi/1452-8630/2023/1452-86302300006D.pdf')]
for key,url in items:
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=12) as f:b=f.read(20000000);r['status']=f.status
  (D/'sources'/key).write_bytes(b);r.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 except Exception as e:r['error']=str(e)
 (D/'sources'/(key+'.receipt.json')).write_text(json.dumps(r,indent=2));print(r)
