import pathlib,urllib.request,datetime,json,hashlib
P=pathlib.Path(__file__).resolve().parent;(P/'sources').mkdir(exist_ok=True);out=[]
for aid in ['2305.10828','2310.07926']:
 url='https://arxiv.org/html/'+aid
 e={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'requested_version':'latest unversioned; record body version if available'}
 try:
  with urllib.request.urlopen(url,timeout=25) as r:
   b=r.read();e.update(status=r.status,final_url=r.url)
  p=P/'sources'/ (aid+'.html');p.write_bytes(b);e.update(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as ex:e['failure']=str(ex)
 out.append(e);print(e)
(P/'successor-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
