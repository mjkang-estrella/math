from pathlib import Path
import json,hashlib,urllib.request,datetime,resource,re
resource.setrlimit(resource.RLIMIT_CPU,(30,30));resource.setrlimit(resource.RLIMIT_AS,(768*1024**2,)*2)
r=Path(__file__).parent;a=r.parent/'expanded-corpus-r48';out=[]
urls={'source-current.pdf':'https://arxiv.org/pdf/2206.12812v1','omega-Jaco.lean':'https://raw.githubusercontent.com/the-omega-institute/trureturing/'+json.loads((r/'omega-head.json').read_text())['sha']+'/D5/S0/Certificates/JacoExponentialDominationRefutation.lean','omega-Abuku.lean':'https://raw.githubusercontent.com/the-omega-institute/trureturing/'+json.loads((r/'omega-head.json').read_text())['sha']+'/D5/S0/Certificates/Games/AbukuEnforceNimberDomination.lean'}
for name,url in urls.items():
 with urllib.request.urlopen(url,timeout=25) as q:data=q.read(5*1024**2);status=q.status
 (r/name).write_bytes(data);out.append({'url':url,'status':status,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),'file':name,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})
out.append({'source_current_matches_cached':(r/'source-current.pdf').read_bytes()==(a/'sources/2206.12812.pdf').read_bytes(),'institution_MD5_matches':hashlib.md5((a/'sources/game-published.pdf').read_bytes()).hexdigest().upper()=='632DBA700A188F73A5DD64B3BCC8F945'})
p=Path(json.loads((a/'registry-path-screen.json').read_text())['file']);d=json.loads(p.read_text());out.append({'openai_complete_listing':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'truncated':d.get('truncated'),'entries':len(d['tree']),'game_hits':[x['path'] for x in d['tree'] if re.search('staller|maker.?breaker|355140|bujt|game',x['path'],re.I)]})
(r/'final-http-and-identity.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
