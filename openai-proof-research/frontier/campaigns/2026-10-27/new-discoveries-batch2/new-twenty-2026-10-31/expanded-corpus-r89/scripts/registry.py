import json,pathlib,hashlib,re
from fetch import get,D
h=json.loads((D/'sources/omega-head.json').read_text())['sha']
get(('omega-root.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{h}'))
r=json.loads((D/'sources/omega-root.json').read_text());out=[]
for t in r.get('tree',[]):
 if t['path'] in ['D5','Problems']:
  key='omega-'+t['path']+'.json';get((key,t['url']+'?recursive=1'));p=D/'sources'/key;o=json.loads(p.read_text())
  hits=[v for v in o.get('tree',[]) if re.search(r'Gregory|Redei|Berge|Isolation|Heawood|Saturation|Uniform|ULSE|Schleimer|Amalgam|Hollow|Transversal|White|Splitting|Perron',v['path'],re.I)]
  out.append(dict(file=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),head=h,truncated=o.get('truncated'),count=len(o.get('tree',[])),matches=hits))
p=D.parent/'fresh-corpus-r10/sources/registry-preprints.json';o=json.loads(p.read_text());out.append(dict(file=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),reuse='OpenAI head unchanged',truncated=o.get('truncated'),count=len(o.get('tree',[]))))
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2))
for o in out: print({k:v for k,v in o.items() if k!='matches'});print('\n'.join(v['path'] for v in o.get('matches',[])))
