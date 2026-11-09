import urllib.request,urllib.error,pathlib,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent;out=[]
for v in ['1105.5490v1','1109.4117v1','1109.3930v1']:
 url='https://arxiv.org/html/'+v
 e={'url':url,'version':v,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'headers':{'User-Agent':'Python-urllib/3','Accept':'text/html'}}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers=e['headers']),timeout=25) as r:
   b=r.read(6000000);e.update(status=r.status,final_url=r.url)
  p=P/(v+'.html');p.write_bytes(b);e.update(path=p.name,sha256=hashlib.sha256(b).hexdigest(),size=len(b))
 except Exception as ex:e.update(error=str(ex),stopped=True)
 out.append(e)
(P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
