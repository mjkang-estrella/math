import pathlib,json,re,hashlib
D=pathlib.Path(__file__).resolve().parents[1];x=json.loads((D/'extracted.json').read_text());out={}
for p in (D/'sources').glob('*-tree.json'):
 o=json.loads(p.read_text());paths=[a['path'] for a in o.get('tree',[])];terms=['dimer','forking','circuit-cocircuit','katona','kronecker','bacher','seating','laplacian','snark','cross-cap','valid-path','pdo','bukh','star-forest','ingleton','matroid','matching-polynomial']+[i for i in x]
 out[p.name]={'truncated':o.get('truncated'),'head':json.loads((D/'sources'/p.name.replace('-tree','-head')).read_text()).get('sha'),'hits':[s for s in paths if any(t.lower() in s.lower() for t in terms)]}
(D/'registry-path-screen.json').write_text(json.dumps(out,indent=2)+'\n')
for k,v in out.items():print(k,v['head'],v['truncated'],len(v['hits']));print('\n'.join(v['hits'][:45]))
vers={}
for p in (D/'sources').glob('*.abs.html'):vers[p.name]=re.findall(r'\[v(\d+)\]',p.read_text())
(D/'versions.json').write_text(json.dumps(vers,indent=2)+'\n')
