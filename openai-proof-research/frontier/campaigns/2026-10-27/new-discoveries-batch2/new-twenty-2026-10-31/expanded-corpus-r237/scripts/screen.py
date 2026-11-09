from pathlib import Path
import json,re,runpy,hashlib,subprocess
L=Path(__file__).resolve().parents[1];get=runpy.run_path(str(L/'scripts/http.py'))['get']
for k,repo in [('omega','the-omega-institute/trureturing'),('openai','openai/math')]:
 sha=json.loads((L/f'sources/{k}-head.json').read_text())['sha'];get(k+'-tree.json',f'https://api.github.com/repos/{repo}/git/trees/{sha}?recursive=1')
R=json.loads((L/'reservation.json').read_text());tokens=[str(i) for i in R['ids']]+[r['source_url'].split('/')[-1] for r in R['rows']]+['Carbonero','Ceria','Jurrius','eventown','Hurwitz','cograph','Franke','Muthiah','Praeger','Tong-Viet','trinomial','entailment','hyperconnectivity','gonality','InfiniteHex','Infinite Hex','Ryser','Jaeger','derangement']
out={'utc':'2026-11-05','heads':{k:json.loads((L/f'sources/{k}-head.json').read_text())['sha'] for k in ['omega','openai','lean-pool']},'matches':{},'github_searches':[],'limitations':['Path/catalogue screening does not inspect all proof bodies. Empty repository search is not novelty clearance.']}
for p in list((L/'sources').glob('pool-*'))+[L/f'sources/{k}-tree.json' for k in ['omega','openai']]:
 if p.suffix=='.json' and 'tree' in p.name:
  d=json.loads(p.read_text());text='\n'.join(x['path'] for x in d.get('tree',[]));out[p.name+'_truncated']=d.get('truncated')
 elif p.name.endswith('.receipt.json'):continue
 else:text=p.read_text(errors='replace')
 hits=[]
 for n,line in enumerate(text.splitlines(),1):
  if any(t.lower() in line.lower() for t in tokens):hits.append({'line':n,'text':line[:500]})
 if hits:out['matches'][p.name]=hits
for p in (L/'sources').glob('github-search-?.json'):
 d=json.loads(p.read_text());out['github_searches'].append({'receipt':str(p)+'.receipt.json','total':d.get('total_count'),'hits':[o['full_name'] for o in d.get('items',[])]})
(L/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2)[:14000])
