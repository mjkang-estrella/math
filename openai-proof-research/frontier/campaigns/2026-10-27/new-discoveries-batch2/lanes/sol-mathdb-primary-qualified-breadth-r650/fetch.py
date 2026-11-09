import urllib.request,hashlib,json,pathlib,datetime
D=pathlib.Path(__file__).resolve().parent
sources=[('ems4086','https://ems.press/journals/owr/articles/4086'),('ems3473','https://ems.press/journals/owr/articles/3473'),('ems4135','https://ems.press/journals/owr/articles/4135'),('acc','https://arxiv.org/abs/1208.4150'),('dvir','https://arxiv.org/abs/0803.2336')]
out=[]
for name,url in sources:
 r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Python-urllib/3'}),timeout=25) as f:b=f.read();r['final_url']=f.url
  p=D/(name+'.html');p.write_bytes(b);r.update(path=str(p),sha256=hashlib.sha256(b).hexdigest(),size=len(b),status='downloaded_bound_before_read')
 except Exception as e:r.update(status='STOP',error=str(e))
 out.append(r)
(D/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
