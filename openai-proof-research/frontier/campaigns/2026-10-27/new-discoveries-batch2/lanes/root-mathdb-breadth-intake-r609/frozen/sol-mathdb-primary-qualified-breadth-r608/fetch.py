import urllib.request,urllib.error,pathlib,hashlib,json,datetime
P=pathlib.Path(__file__).resolve().parent
out=[]
for a in ['2201.11958','2207.05599','2209.03265','2211.03599','2209.00787']:
 u='https://arxiv.org/html/'+a
 try:
  req=urllib.request.Request(u,headers={'User-Agent':'Mozilla/5.0','Accept':'text/html'})
  with urllib.request.urlopen(req,timeout=25) as f:b=f.read(8000000);url=f.geturl();status=f.status
  (P/(a+'.html')).write_bytes(b)
  out.append({'url':u,'final_url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':status,'file':a+'.html','sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'content_coverage':'bytes bound before parsing; not yet read'})
 except Exception as e:out.append({'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'failure':str(e),'retry':False})
(P/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
