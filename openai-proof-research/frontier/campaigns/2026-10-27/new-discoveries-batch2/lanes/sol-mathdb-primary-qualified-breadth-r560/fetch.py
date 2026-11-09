import pathlib,urllib.request,datetime,json,hashlib
D=pathlib.Path(__file__).parent
urls={'irregular':'https://arxiv.org/html/1407.1276v2','idp':'https://arxiv.org/html/1608.03934v2','plactic':'https://arxiv.org/html/1906.03991v2','activity':'https://arxiv.org/html/1412.2081v3'}
out=[]
for n,u in urls.items():
 e={'name':n,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=25) as r:b=r.read();e['status']=r.status
  p=D/(n+'.html');p.write_bytes(b);e.update(path=str(p.resolve()),sha256=hashlib.sha256(b).hexdigest(),size=len(b))
 except Exception as ex:e['failure']=str(ex)
 out.append(e)
(D/'downloads.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
