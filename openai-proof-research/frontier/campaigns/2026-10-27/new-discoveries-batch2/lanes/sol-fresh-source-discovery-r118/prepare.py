import json,gzip,re,hashlib,subprocess
from pathlib import Path
from html.parser import HTMLParser
L=Path(__file__).resolve().parent; B=L.parent
class P(HTMLParser):
 def __init__(self):super().__init__();self.a=[]
 def handle_data(self,s):self.a.append(s)
 def handle_starttag(self,t,a):
  if t in {'p','h1','h2','h3','h4','div','tr'}:self.a.append('\n')
for p in (L/'sources').glob('*.html'):
 x=P();x.feed(p.read_text());p.with_suffix('.txt').write_text(''.join(x.a))
subprocess.run(['pdftotext','-layout',str(L/'sources/melbourne.pdf'),str(L/'sources/melbourne.txt')],check=True)
patterns=re.compile(r'Varentropy|Lyapunov|Melbourne|Palafox|GaussianProduct|Gaussian.Product|WeakSimplex|SimplexConjecture|SimplexCode',re.I)
rows=[]; hashes=[]
for name in ('omega','openai'):
 p=B/'root-edge-irregulator-final-freeze-r1'/(name+'-tree.txt.gz')
 hashes.append({'p':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
 with gzip.open(p,'rt') as f:
  for s in f:
   if patterns.search(s):rows.append({'registry':name,'pathrecord':s.strip()})
(L/'registry-targets.json').write_text(json.dumps(rows,indent=2))
heads={k:json.loads((L/'sources'/f'{k}-head.json').read_text()) for k in ('omega','openai')}
d=json.loads((L/'sources/fresh-delta.json').read_text())
(L/'registry-receipt.json').write_text(json.dumps({'heads':{k:{'sha':v['sha'],'committer':v['commit']['committer']} for k,v in heads.items()},'fresh_delta':{'base':d['base_commit']['sha'],'head':d['commits'][-1]['sha'] if d.get('commits') else d['base_commit']['sha'],'commits':d['total_commits'],'files':len(d['files']),'under_300':len(d['files'])<300},'baseline_tree_hashes':hashes,'status':'HOLD: inherited 0d4-to-5e2 delta capped; no complete-current novelty clearance','limits':'path selection only, not semantic coverage'},indent=2))
print((L/'registry-receipt.json').read_text());print('selected',len(rows))
