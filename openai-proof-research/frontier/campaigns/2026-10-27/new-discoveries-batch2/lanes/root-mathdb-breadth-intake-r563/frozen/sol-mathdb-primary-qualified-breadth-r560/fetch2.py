import pathlib,urllib.request,datetime,json,hashlib
D=pathlib.Path(__file__).parent
urls={'irregular':'https://arxiv.org/html/1407.1276v1','idp-successor':'https://arxiv.org/html/1911.12459v1','plactic-primary':'https://arxiv.org/html/1611.04151v1'}
out=[]
for n,u in urls.items():
 e={'name':n,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=25) as r:b=r.read();e['status']=r.status
  p=D/(n+'.html');p.write_bytes(b);e.update(path=str(p.resolve()),sha256=hashlib.sha256(b).hexdigest(),size=len(b))
 except Exception as ex:e['failure']=str(ex)
 out.append(e)
(D/'downloads2.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
