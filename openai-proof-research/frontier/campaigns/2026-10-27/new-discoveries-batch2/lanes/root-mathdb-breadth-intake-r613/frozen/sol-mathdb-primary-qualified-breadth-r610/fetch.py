import urllib.request,hashlib,json,pathlib,datetime
D=pathlib.Path(__file__).parent;log=[]
for aid in ['2305.07727','2311.04487','2302.12106','2307.13684','2307.15573']:
 url='https://arxiv.org/html/'+aid+'v1';t=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0','Accept':'text/html'})
  with urllib.request.urlopen(req,timeout=25) as f:b=f.read();final=f.url;status=f.status
  p=D/(aid+'.html');p.write_bytes(b);log.append({'url':url,'final_url':final,'utc':t,'status':status,'path':p.name,'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'body_read':False})
 except Exception as e:log.append({'url':url,'utc':t,'error':str(e),'action':'HOLD; no retry or alternate route'})
(D/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n');print(json.dumps(log,indent=2))
