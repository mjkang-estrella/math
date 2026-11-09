import urllib.request,datetime,pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent
out=[]
for name,url in [('codes-primary','https://arxiv.org/html/math/0303254v1'),('codes-successor','https://arxiv.org/html/0801.0184v1'),('hom-primary','https://arxiv.org/html/math/0310056v1'),('hom-successor','https://arxiv.org/html/1601.07854v1')]:
 r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=35) as f:b=f.read();r['final_url']=f.url
  (P/(name+'.html')).write_bytes(b);r.update(size=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as e:r['failure']=str(e)
 out.append(r)
(P/'retrieval2-bindings.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
