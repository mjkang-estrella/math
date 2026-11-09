import pathlib,urllib.request,urllib.error,hashlib,json,datetime
P=pathlib.Path(__file__).resolve().parent;(P/'sources').mkdir(exist_ok=True);out=[]
for aid in ['2406.02747','2407.12048','2408.05509','2409.20160','2408.06770','2406.12063']:
 url='https://arxiv.org/html/'+aid+'v1';e={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'version_requested':'v1'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-screen/1.0'}),timeout=35) as r:b=r.read();e['final_url']=r.url;e['http_status']=r.status
  p=P/'sources'/f'{aid}v1.html';p.write_bytes(b);e.update(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
 except Exception as ex:e.update(error=str(ex),body_read=False)
 out.append(e);(P/'source-bindings.json').write_text(json.dumps(out,indent=2)+'\n');print(e)
