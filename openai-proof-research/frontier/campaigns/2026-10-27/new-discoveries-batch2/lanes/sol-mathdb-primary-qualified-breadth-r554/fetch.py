import pathlib,json,hashlib,urllib.request,datetime
P=pathlib.Path(__file__).parent;out=[]
for name,url in [('billiards','https://arxiv.org/html/2004.12497'),('apn','https://arxiv.org/html/2511.04193'),('postnikov','https://sites.math.washington.edu/~billey/japan/references/hultman.linusson.shareshian.sjostrand.pdf')]:
 e={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as r:b=r.read();e.update(status=r.status,final_url=r.url,content_type=r.headers.get('Content-Type'))
  p=P/(name+('.pdf' if b[:4]==b'%PDF' else '.html'));p.write_bytes(b);e.update(path=p.name,size=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as ex:e['failure']=str(ex)
 out.append(e)
(P/'retrieval-bindings.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
