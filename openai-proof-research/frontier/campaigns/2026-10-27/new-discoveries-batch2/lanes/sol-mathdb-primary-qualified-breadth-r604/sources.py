import pathlib,json,urllib.request,hashlib,datetime
from html.parser import HTMLParser
D=pathlib.Path(__file__).parent
pro=[];fail=[]
for a in ['1904.05214','1910.13433','1909.09037','1909.07141']:
 url='https://arxiv.org/html/'+a
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0','Accept':'text/html'}),timeout=35) as f:
   b=f.read(10000000); final=f.url
  p=D/(a+'.html');p.write_bytes(b)
  pro.append({'url':url,'final_url':final,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'path':p.name,'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'kind':'HTML bytes; version must be established from content'})
 except Exception as e:fail.append({'url':url,'error':str(e),'retry':False})
(D/'source-provenance.json').write_text(json.dumps(pro,indent=2)+'\n');(D/'fetch-failures.json').write_text(json.dumps(fail,indent=2)+'\n')
print(json.dumps(pro,indent=2));print(fail)
