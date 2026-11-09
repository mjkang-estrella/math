import pathlib,json,re,sys
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from fetch import get
D=pathlib.Path(__file__).resolve().parents[1]
sha=json.loads((D/'sources/omega-head.json').read_text())['sha'];get('omega-root.json',f'https://api.github.com/repos/the-omega-institute/trureturing/git/trees/{sha}')
root=json.loads((D/'sources/omega-root.json').read_text())
for o in root['tree']:
 if o['path'] in ['D5','Problems']:get('omega-'+o['path']+'.json',o['url']+'?recursive=1')
res={}
for p in (D/'sources').glob('*abs.html'):
 s=p.read_text();res[p.name]=sorted(set(re.findall(r'\[v(\d+)\]',s)),key=int)
(D/'outputs/versions.json').write_text(json.dumps(res,indent=2));print(res)
for p in (D/'sources').glob('github-search-*.json'):
 o=json.loads(p.read_text());print(p.name,[(x['full_name'],x['description']) for x in o.get('items',[])])
for a in ['2004.11367v1','2211.08746v1','1904.04071v1','1807.05181v1','1912.03741v1','1912.03741v2','1912.03741v3','1909.09381v1','1909.09381v2']:
 get(a+'.html','https://arxiv.org/html/'+a)
