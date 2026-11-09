from pathlib import Path
import runpy,sys,re,json
L=Path(__file__).resolve().parent;sys.argv=['work','freeze',str(L/'G-edges.json')];ns=runpy.run_path(str(L/'work.py'));freeze=ns['freeze']
for p in sorted((L/'primary').glob('*.txt')):
 if not re.match(r'\d',p.name):continue
 q=freeze(p);s=q.read_text();lines=s.splitlines();print('\nSOURCE',p.name,'TITLE', '\n'.join(lines[:12]))
 hits=[i for i,x in enumerate(lines) if re.search(r'Conjecture|Open Problem|Question \d|Problem \d|cospectral|Theorem 1\.|Theorem A',x,re.I)]
 for i in hits[:10]:print('\n'.join(f'{j+1}: {lines[j]}' for j in range(max(0,i-2),min(len(lines),i+14))))
R=L.parents[4]/'2026-10-26/new-discoveries/lanes/pi-euler-turan-final-review/fresh/trureturing'
# Resolve directly to avoid ancestor ambiguity.
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-euler-turan-final-review/fresh/trureturing')
terms=r'fullerene|Buchstaber|Spodarev|toric variet|ordered Banach|Cuenin|kernelized.*bandit|anytime.*gradient|Krylov|free curves|semigroup conjugacy|Thamrongthanyalak|Fermat.type|Godsil.McKay'
hits=[]
for p in (R/'Problems').glob('*.md'):
 if re.search(terms,p.read_text(errors='replace'),re.I):
  q=freeze(p);hits.append(dict(original=str(p),frozen=str(q),excerpt=q.read_text()[:22000]));print('CACHE',p.name,q.read_text()[:2500])
(L/'cached-screen.json').write_text(json.dumps(hits,indent=2));print('CACHE TOTAL',len(hits))
