import sys,pathlib,json,re,time
sys.path.insert(0,str(pathlib.Path(sys.argv[1])/'scripts'));from fetch import fetch
D=pathlib.Path(sys.argv[1]);p=D/'sources/Vilin97-lean-pool-tree/body';tree=json.loads(p.read_text());sha=json.loads((D/'sources/Vilin97-lean-pool-head/body').read_text())['sha']
paths=[x['path'] for x in tree['tree'] if x['path']=='projects.yml' or x['path'].startswith('candidates/') and x['type']=='blob']
for j,path in enumerate(paths):fetch('https://raw.githubusercontent.com/Vilin97/lean-pool/'+sha+'/'+path,'pool-'+str(j))
queries=['"triangular lattice" lean','"friends strangers" lean','"matroid amoeba" lean','"Kashima" lean','"2603.18915" lean','"2303.11893" lean','"2604.11495" lean','"simple Parry" lean']
for j,q in enumerate(queries):
 x=fetch('https://api.github.com/search/repositories?q='+__import__('urllib.parse').parse.quote(q),'github-search-'+str(j))
 if x is None:break
 time.sleep(8)
(D/'outputs/registry-screen.json').write_text(json.dumps({'lean_pool_head':sha,'paths':paths,'queries_planned':queries,'note':'See individual immutable receipts; grep hits require scope reading. No global novelty clearance.'},indent=2))
