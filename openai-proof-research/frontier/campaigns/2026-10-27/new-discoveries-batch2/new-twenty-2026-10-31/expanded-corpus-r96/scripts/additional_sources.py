import urllib.request,pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parents[1]
for name,url in [('341896-pdf','https://arxiv.org/pdf/1902.07301'),('363770-abs','https://arxiv.org/abs/2407.02102'),('368807-pdf','https://arxiv.org/pdf/2506.10671')]:
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-review'}),timeout=20) as f:b=f.read();r.update(status=f.status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  (L/'sources'/ (name+('.pdf' if name.endswith('pdf') else '.html'))).write_bytes(b)
 except Exception as e:r['error']=str(e)
 (L/f'sources/{name}-receipt.json').write_text(json.dumps(r,indent=2));print(name,r)
