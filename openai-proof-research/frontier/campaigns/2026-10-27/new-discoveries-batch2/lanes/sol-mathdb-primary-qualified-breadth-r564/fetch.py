import pathlib,urllib.request,urllib.error,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent;out=[]
for name,url in [('korselt','https://arxiv.org/html/1911.09323v1'),('recurrence','https://arxiv.org/html/2010.03363v1'),('sandpile','https://arxiv.org/html/2008.10079v1')]:
 e={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as r:b=r.read();e.update(status=r.status,final_url=r.url)
  p=P/(name+'.html');p.write_bytes(b);e.update(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as ex:e.update(error=str(ex),stopped=True)
 out.append(e)
(P/'downloads.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
