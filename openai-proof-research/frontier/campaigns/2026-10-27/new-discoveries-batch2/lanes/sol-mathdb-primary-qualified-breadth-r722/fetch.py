import urllib.request,pathlib,json,hashlib,datetime
D=pathlib.Path(__file__).parent
out=[]
for a in ['1708.06790v1','2206.04290v1','2603.23228v1']:
 u='https://arxiv.org/html/'+a
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Python-urllib/3'}),timeout=30) as r:b=r.read();status=r.status
  p=D/(a+'.html');p.write_bytes(b);out.append(dict(url=u,version=a,status=status,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),path=p.name,sha256=hashlib.sha256(b).hexdigest(),size=len(b)))
 except Exception as e:out.append(dict(url=u,version=a,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),error=str(e),stopped=True))
(D/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
