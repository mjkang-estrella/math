from pathlib import Path
import urllib.request,hashlib,json,datetime
D=Path(__file__).parent;p=D/'source-provenance.json';a=json.loads(p.read_text());u='https://arxiv.org/html/1201.6043'
try:
 with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Mozilla/5.0','Accept':'text/html'}),timeout=35) as r:b=r.read();url=r.url
 (D/'prior.html').write_bytes(b);a.append({'url':u,'final_url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'path':'prior.html','sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'status':200})
except Exception as e:a.append({'url':u,'error':str(e),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'retry':False})
p.write_text(json.dumps(a,indent=2)+'\n');print(a[-1])
