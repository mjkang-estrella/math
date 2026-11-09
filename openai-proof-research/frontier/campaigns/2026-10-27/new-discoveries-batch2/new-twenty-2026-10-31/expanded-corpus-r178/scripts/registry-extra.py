import sys,pathlib,json,re,hashlib
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch import fetch,D
r=json.loads((D/'outputs/registry-screen.json').read_text());repo='the-omega-institute/trureturing';sha=r['heads'][repo]['sha'];fetch('https://api.github.com/repos/'+repo+'/git/trees/'+sha,'omega-root.json')
for x in json.loads((D/'sources/omega-root.json').read_text())['tree']:
 if x['path'] in ['D5','Problems']:fetch(x['url']+'?recursive=1','omega-'+x['path']+'.json')
p=D.parent/'fresh-corpus-r10/sources/registry-preprints.json';r['openai_cache']={'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'head':r['heads']['openai/math']['sha'],'scope':'cached full preprint paths, HEAD unchanged vs r177'}
terms=['orientable','total.domination','open.domination','interpolation','pebbling','cochord','subtraction','cube.width','binariz','upcycle','schur','hook.length','vinogradov','clique.number.of.tournament']
r['path_hits']={}
for p in [D/'sources/omega-D5.json',D/'sources/omega-Problems.json',p]:
 data=json.loads(p.read_text());hits=[]
 for x in data.get('tree',[]):
  if any(re.search(t,x['path'],re.I) for t in terms):hits.append(x)
 r['path_hits'][str(p)]=hits
r['github_results']={p.name:json.loads(p.read_text()).get('items',[]) for p in (D/'sources').glob('ghquery*.json') if not p.name.endswith('receipt.json')}
(D/'outputs/registry-screen.json').write_text(json.dumps(r,indent=2));print(json.dumps(r['path_hits'],indent=2)[:9000])
