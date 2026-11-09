import urllib.request,pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parents[1]
for name,url in [('382272-v1','https://arxiv.org/html/2403.11191v1'),('354984-pdf','https://arxiv.org/pdf/2206.06118')]:
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=15) as f:b=f.read();r.update(status=f.status,sha256=hashlib.sha256(b).hexdigest())
  (L/'sources'/ (name+('.pdf' if name.endswith('pdf') else '.html'))).write_bytes(b)
 except Exception as e:r['error']=str(e)
 (L/f'sources/{name}-receipt.json').write_text(json.dumps(r,indent=2));print(name,r)
