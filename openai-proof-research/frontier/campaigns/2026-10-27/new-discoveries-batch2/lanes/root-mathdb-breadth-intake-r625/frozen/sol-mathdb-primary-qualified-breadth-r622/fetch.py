import pathlib,urllib.request,datetime,json,hashlib
P=pathlib.Path(__file__).parent;out=[]
for id in ['2505.09465v1','1302.5686v2']:
 url='https://arxiv.org/html/'+id
 a={'url':url,'requested_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'headers':{'User-Agent':'Mozilla/5.0','Accept':'text/html'},'version_requested':id}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers=a['headers']),timeout=35) as r:b=r.read(10000000);a.update(status=r.status,final_url=r.url)
  f=P/(id+'.html');f.write_bytes(b);a.update(file=f.name,sha256=hashlib.sha256(b).hexdigest(),size=len(b))
 except Exception as e:a.update(error=str(e),stop_no_retry=True)
 out.append(a)
(P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
