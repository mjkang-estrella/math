from pathlib import Path
import json,re,urllib.request,datetime,hashlib
P=Path(__file__).resolve().parent;S=P/'sources';out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'limits':'Complete inherited baseline paths, bounded live delta and selected actual bodies; no absence-as-priority inference.'};log=[]
pat=re.compile(r'(Fisher.*(Mix|Schur|Convol|Weight|Minim)|Gaussian.*Mix|Eskenazis|Gavalakis|BallNayar|EntropyConcav)',re.I)
def get(url,name):
 row={'url':url,'file':'sources/'+name,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  r=urllib.request.urlopen(url,timeout=20);b=r.read(18000000);(S/name).write_bytes(b);row.update(status=r.status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));return json.loads(b) if name.endswith('.json') else b.decode(errors='replace')
 except Exception as e:row['error']=str(e)
 finally:log.append(row);(P/'registry-http.json').write_text(json.dumps(log,indent=2))
for key,repo in [('omega','the-omega-institute/trureturing'),('openai','openai/math')]:
 d=json.loads((S/(key+'-head.json')).read_text());head=d['sha'];out[key]={'head':head,'author':d['commit']['author'],'committer':d['commit']['committer']}
 base=P.parent/'root-edge-irregulator-final-freeze-r1'/(key+'-tree.txt');matches=[]
 for line in base.open():
  path=line.strip().split('\t')[-1]
  if pat.search(path):matches.append(path)
 out[key]['baseline_sha256']=hashlib.sha256(base.read_bytes()).hexdigest();out[key]['path_matches']=matches
 for i,path in enumerate(matches):
  if path.endswith(('.md','.lean')):get('https://raw.githubusercontent.com/'+repo+'/'+head+'/'+path,key+'-body-'+str(i)+'.txt')
 if key=='omega':
  delta=get('https://api.github.com/repos/'+repo+'/compare/c9cea079996532f43216352b68960a727b7ed8fe...'+head,'omega-latest-delta.json')
  if delta:out[key]['latest_delta']={'base':'c9cea079996532f43216352b68960a727b7ed8fe','commits':delta.get('total_commits'),'files':len(delta.get('files',[])),'possibly_capped':len(delta.get('files',[]))>=300,'paths':[f['filename'] for f in delta.get('files',[])]}
(P/'registry.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2)[:14000])
get('https://arxiv.org/abs/2308.15997','GM-abs.html')
get('https://arxiv.org/html/2609.11418v2','Luo-v2.html')
