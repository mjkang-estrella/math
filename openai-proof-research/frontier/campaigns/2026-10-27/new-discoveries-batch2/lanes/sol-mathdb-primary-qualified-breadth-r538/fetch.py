import urllib.request,datetime,pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent
out=[]
for name,url in [('wow','https://arxiv.org/html/2607.27452v1'),('fekete','https://arxiv.org/html/cs/0702090v1'),('chung','https://arxiv.org/html/math/0404559v1'),('lind','https://arxiv.org/html/math/0303279v1')]:
 r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=35) as f:b=f.read();r['final_url']=f.url
  (P/(name+'.html')).write_bytes(b);r.update(size=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:r['failure']=str(e)
 out.append(r)
(P/'retrieval-bindings.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
