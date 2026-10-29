import urllib.request,json,hashlib,datetime,resource,signal,re
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(25,25));signal.alarm(55)
r=Path(__file__).parent;rows=[]
def fetch(name,url):
 t=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Independent-mathematical-review/1.0'}),timeout=8) as f:b=f.read(8*1024**2);status=f.status
  (r/'live'/name).write_bytes(b);rows.append({'utc':t,'url':url,'file':'live/'+name,'status':status,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()});return b
 except Exception as e:rows.append({'utc':t,'url':url,'error':str(e),'retry':False});return None
head=json.loads((r/'live/omega').read_text())['sha'];api='https://api.github.com/repos/the-omega-institute/trureturing/'
fetch('delta.json',api+'compare/b38b67f348712cc1d54d5619a0dceb5e57ff1119...'+head)
b=fetch('root.json',api+'git/trees/'+head)
if b:
 for item in json.loads(b)['tree']:
  if item['path'] in ['D5','Problems']:fetch(item['path']+'.json',api+'git/trees/'+item['sha']+'?recursive=1')
fetch('steiner-current.pdf','https://arxiv.org/pdf/2505.10501v1')
# Actual closest-name problem claims; immutable head.
for name in ['jana-mahato-sivasubramanian-2025-steiner-path-peak.md','zhang-tian-2025-steiner-diameter-radius-trees.md']:
 fetch(name,'https://raw.githubusercontent.com/the-omega-institute/trureturing/'+head+'/Problems/'+name)
(r/'refresh-http.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
