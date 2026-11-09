import pathlib,json,sys,time,urllib.parse
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch import get
D=pathlib.Path(__file__).resolve().parents[1]
t=json.loads((D/'sources/pool-tree.json').read_text())['tree'];sha=json.loads((D/'sources/pool-head.json').read_text())['sha']
paths=[v['path'] for v in t if v['path'].endswith('projects.yml') or v['path'].startswith('candidates/') and v['type']=='blob']
(D/'outputs/pool-paths.json').write_text(json.dumps(paths,indent=2))
for n,p in enumerate(paths):get('pool-file-'+str(n)+'.txt',f'https://raw.githubusercontent.com/Vilin97/lean-pool/{sha}/{p}')
for n,q in enumerate(['"valid hook" lean','"Seo Yee" lean','"seaweed" lean','"Kaplan" "semigroup" lean','"Hippchen" lean','"Kasami" lean','"Rodney" lean','"2211.08746" lean']):
 if n:time.sleep(8)
 get('github-search-'+str(n)+'.json','https://api.github.com/search/repositories?q='+urllib.parse.quote(q))
 rec=json.loads((D/'sources'/('github-search-'+str(n)+'.json.receipt.json')).read_text())
 if rec.get('status') in [403,429]:break
for a in ['1808.01008','2004.11367','1910.14369','1912.03741','1905.06459','2211.08746']:
 get(a+'-abs.html','https://arxiv.org/abs/'+a)
