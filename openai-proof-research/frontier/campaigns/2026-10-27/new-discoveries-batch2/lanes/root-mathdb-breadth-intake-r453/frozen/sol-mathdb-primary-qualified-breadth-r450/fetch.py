import pathlib,json,urllib.request,urllib.error,datetime,hashlib,re
L=pathlib.Path(__file__).resolve().parent;(L/'sources').mkdir(exist_ok=True)
urls=list(dict.fromkeys(x['record']['source_url'] for x in json.loads((L/'assigned-records.json').read_text())))
log=[];blocked=set()
for u in urls:
 host=urllib.parse.urlsplit(u).netloc
 if host in blocked:log.append({'url':u,'status':'HOLD inherited host stop'});continue
 t=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Research source reading'}),timeout=25) as r:b=r.read(12000000);status=r.status
  p=L/'sources'/('ems-'+u.rsplit('/',1)[1]+'.html');p.write_bytes(b)
  log.append({'url':u,'utc':t,'status':status,'file':str(p.relative_to(L)),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)})
  print(u,status,len(b),flush=True)
 except Exception as e:
  log.append({'url':u,'utc':t,'status':'HOLD','error':str(e)})
  if isinstance(e,urllib.error.HTTPError) and e.code in [403,429]:blocked.add(host)
  print(u,str(e),flush=True)
(L/'source-access.json').write_text(json.dumps(log,indent=2)+'\n')
