import urllib.request,json,pathlib,datetime,hashlib
D=pathlib.Path(__file__).resolve().parent
out=[]
for name,v in [('tensor','1412.5831'),('delay','1509.06226'),('stable','1604.00704'),('partition','1609.02854')]:
 url='https://arxiv.org/html/'+v
 e={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'version':'unversioned arXiv HTML endpoint; inspect returned version'}
 try:
  with urllib.request.urlopen(url,timeout=25) as r:b=r.read();e['resolved_url']=r.url
  p=D/(name+'.html');p.write_bytes(b);e.update(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as ex:e['failure']=str(ex)
 out.append(e)
(D/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
