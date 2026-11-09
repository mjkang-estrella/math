import urllib.request,pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parents[1]; out=[]
for repo in ['openai/math','the-omega-institute/trureturing']:
 url='https://api.github.com/repos/'+repo+'/commits/HEAD'
 try:
  with urllib.request.urlopen(url,timeout=15) as h: b=h.read()
  (L/('sources/registry-'+repo.replace('/','-')+'.json')).write_bytes(b)
  out.append({'url':url,'sha256':hashlib.sha256(b).hexdigest(),'head':json.loads(b)['sha'],'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})
 except Exception as e: out.append({'url':url,'error':str(e)})
(L/'outputs/registry.json').write_text(json.dumps(out,indent=2)); print(json.dumps(out))
