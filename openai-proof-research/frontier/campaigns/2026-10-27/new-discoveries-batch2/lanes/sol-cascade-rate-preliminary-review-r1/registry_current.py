import json,urllib.request,datetime,hashlib,resource,os
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));resource.setrlimit(resource.RLIMIT_CPU,(25,25))
b=Path(__file__).parent; out=[]
def get(name,url):
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:data=f.read();r.update(status=f.status,sha256=hashlib.sha256(data).hexdigest());(b/'sources'/name).write_bytes(data)
  j=json.loads(data)
 except Exception as e:r['error']=str(e);j={}
 out.append(r);(b/'registry-http.json').write_text(json.dumps(out,indent=2));return j
head=json.loads((b/'sources/omega-head').read_text()); root=get('omega-root.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+head['commit']['tree']['sha'])
for entry in root.get('tree',[]):
 if entry['type']=='tree' and entry['path'] in ['D5','Problems']:
  get('omega-'+entry['path']+'.json','https://api.github.com/repos/the-omega-institute/trureturing/git/trees/'+entry['sha']+'?recursive=1')
print([(e['path'],e['type']) for e in root.get('tree',[])])
