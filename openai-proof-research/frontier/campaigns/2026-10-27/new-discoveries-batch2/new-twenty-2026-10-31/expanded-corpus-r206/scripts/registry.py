import pathlib,json,re,sys,hashlib
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent));from net import get,D
head=json.loads((D/'sources/pool-head.json').read_text())['sha'];get('pool-projects.yml',f'https://raw.githubusercontent.com/Vilin97/lean-pool/{head}/LeanPool/projects.yml')
x=json.loads((D/'extracted.json').read_text());patterns=[str(i) for i in x]+[o['source_url'].rsplit('/',1)[-1] for o in x.values()]+['meandric','heterochromatic','Mazzuoccolo','exponential domination','Gadouleau','cross number','fighting fish','Goldschmidt','Saxl','ghost number','nested cartesian']
report={'patterns':patterns,'heads':{},'hits':{},'github_queries':[],'scope_limit':'path and catalogue text screening; no exhaustive proof body or deleted history audit'}
for k in ['pool','omega','openai']:
 report['heads'][k]=json.loads((D/f'sources/{k}-head.json').read_text())['sha']
 files=list((D/'sources').glob('pool-candidates*'))+[D/'sources/pool-projects.yml']+[D/f'sources/{k}-tree.json' for k in ['pool','omega','openai']]
for p in files:
 if p.name.endswith('receipt.json'):continue
 s=p.read_text();report['hits'][p.name]=[pat for pat in patterns if pat.lower() in s.lower()]
for p in sorted((D/'sources').glob('github-search-*.json')):
 if p.name.endswith('receipt.json'):continue
 r=json.loads(p.with_suffix('.json.receipt.json').read_text());b=json.loads(p.read_text());report['github_queries'].append({'receipt':r,'total_count':b.get('total_count'),'items':[{k:o.get(k) for k in ['full_name','description','html_url']} for o in b.get('items',[])]})
(D/'outputs/registry-screen.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
