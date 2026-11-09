from pathlib import Path
import json,re,sys,runpy
L=Path(__file__).resolve().parent;sys.argv=['work','freeze',str(L/'broad-cache-hits.json')];ns=runpy.run_path(str(L/'work.py'));freeze=ns['freeze']
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-euler-turan-final-review/fresh/trureturing')
for row in json.loads((L/'broad-cache-hits.json').read_text()):
 p=L/row['copy'];s=p.read_text();print('\nCACHE',p.name,s[:4200])
 for rel in re.findall(r'`([^`]+\.lean)`',s):
  p=R/rel
  if p.exists():
   q=freeze(p);t=q.read_text();print('ACTUAL PROOF',rel,t[-3500:])
