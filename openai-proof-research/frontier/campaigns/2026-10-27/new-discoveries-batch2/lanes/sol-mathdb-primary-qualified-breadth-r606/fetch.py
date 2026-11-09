from pathlib import Path
import urllib.request,json,hashlib,datetime
D=Path(__file__).parent;out=[]
for aid,name in [('2010.10762','projective'),('2010.02779','msrd'),('2010.11112','howroyd'),('2109.09183','vincular')]:
 u='https://arxiv.org/html/'+aid
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Mozilla/5.0','Accept':'text/html'}),timeout=35) as r:b=r.read();url=r.url;status=r.status
  p=D/(name+'.html');p.write_bytes(b);out.append({'url':u,'final_url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'path':p.name,'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'status':status})
 except Exception as e:out.append({'url':u,'error':str(e),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'retry':False})
(D/'source-provenance.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
