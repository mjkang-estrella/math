import json,pathlib,hashlib,gzip,re
L=pathlib.Path(__file__).resolve().parent;B=L.parent.parent;R=B.parents[3]
out={}
for name in ['ledger.json','prior-campaign-context.json','NEXT.md']:
 p=B/name;s=p.read_text();v=json.loads(s) if p.suffix=='.json' else s;out[name]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'content':v}
for lane in ['sol-fresh-source-discovery-r89','sol-fresh-source-discovery-r90']:
 out[lane]={p.name:p.read_text() for p in (L.parent/lane).glob('*.md')}
hits=[]
for repo in ['omega','openai']:
 p=L.parent/'root-edge-irregulator-current-prior-r1'/(repo+'-tree.txt.gz')
 for s in gzip.open(p,'rt'):
  if re.search(r'walk|poullot|monotone|hypersimp|maximum.likelihood|grosdos',s,re.I):hits.append({'repo':repo,'path':s.strip()})
(L/'context.json').write_text(json.dumps(out,indent=2));(L/'registry-hits.json').write_text(json.dumps(hits,indent=2));print(json.dumps(hits,indent=2));print('context loaded',[(k,len(str(v))) for k,v in out.items()])
