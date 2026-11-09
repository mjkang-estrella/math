import urllib.request,pathlib,hashlib,json,datetime
O=pathlib.Path(__file__).resolve().parent
out=[]
for name,url in [('coins','https://arxiv.org/html/0801.0120'),('jumping','https://arxiv.org/html/0807.2890'),('somos','https://arxiv.org/html/0909.0469')]:
 d={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=35) as r:
   b=r.read();d.update(status=r.status,final_url=r.url)
  p=O/(name+'.html');p.write_bytes(b);d.update(path=str(p),sha256=hashlib.sha256(b).hexdigest(),size=len(b))
 except Exception as e:d['failure']=str(e)
 out.append(d)
(O/'downloads.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
