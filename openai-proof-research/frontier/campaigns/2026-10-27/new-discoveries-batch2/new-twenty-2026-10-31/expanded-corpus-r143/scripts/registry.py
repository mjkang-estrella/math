import urllib.request,json,hashlib,datetime
out={}
for repo in ['openai/math','the-omega-institute/trureturing']:
 u=f'https://api.github.com/repos/{repo}/commits/HEAD'
 try:
  r=urllib.request.urlopen(u,timeout=15); b=r.read(); j=json.loads(b); out[repo]={'url':u,'status':r.status,'head':j['sha'],'sha256':hashlib.sha256(b).hexdigest(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};open('sources/'+repo.replace('/','-')+'-HEAD.json','wb').write(b)
 except Exception as e:out[repo]={'url':u,'error':str(e)}
json.dump(out,open('outputs/registries.json','w'),indent=2);print(json.dumps(out))
