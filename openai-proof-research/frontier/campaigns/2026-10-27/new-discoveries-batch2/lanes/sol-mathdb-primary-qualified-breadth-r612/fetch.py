import pathlib,json,hashlib,urllib.request,datetime
P=pathlib.Path(__file__).parent
log=[]
for id in ['2312.09482','2404.07670','2406.07109','2406.00139']:
 url='https://arxiv.org/html/'+id+'v1';dest=P/(id+'.html')
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0','Accept':'text/html'})
  with urllib.request.urlopen(req,timeout=35) as r:
   raw=r.read(12000000);status=r.status;final=r.url
  dest.write_bytes(raw);log.append({'url':url,'final_url':final,'version':'v1','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'path':str(dest),'sha256':hashlib.sha256(raw).hexdigest(),'size':len(raw),'status':status})
 except Exception as e:log.append({'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'error':str(e),'stopped':True})
(P/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n');print(json.dumps(log,indent=2))
