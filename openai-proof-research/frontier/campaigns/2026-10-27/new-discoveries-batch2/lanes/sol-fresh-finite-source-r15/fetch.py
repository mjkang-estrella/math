import pathlib,urllib.request,json,hashlib,datetime,urllib.error
P=pathlib.Path(__file__).parent; (P/'sources').mkdir(exist_ok=True)
urls=[('source.html','https://arxiv.org/html/2604.14639v1'),('source-abs.html','https://arxiv.org/abs/2604.14639'),('registry-target.md','https://raw.githubusercontent.com/the-omega-institute/trureturing/67b4fae085cf19003a33f8027410c383b49e5046/Problems/glasby-paseman-powered-ratio-maximum.md'),('successor.json','https://zenodo.org/api/records/22542573')]
receipts=[]; blocked=set()
for name,url in urls:
 host=urllib.request.urlparse(url).netloc if False else url.split('/')[2]
 if host in blocked: continue
 r={'file':'sources/'+name,'url':url,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=40) as f: b=f.read(); r['status']=f.status
  (P/'sources'/name).write_bytes(b); r.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 except urllib.error.HTTPError as e:
  r.update(status=e.code,error=str(e))
  if e.code in [403,429]: blocked.add(host)
 except Exception as e:r['error']=str(e)
 receipts.append(r)
(P/'retrievals.json').write_text(json.dumps(receipts,indent=2)+'\n')
print(json.dumps(receipts,indent=2))
