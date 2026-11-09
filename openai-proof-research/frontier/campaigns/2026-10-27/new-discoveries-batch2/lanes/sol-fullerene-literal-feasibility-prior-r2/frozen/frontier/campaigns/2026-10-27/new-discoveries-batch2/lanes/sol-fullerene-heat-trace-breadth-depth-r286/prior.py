from pathlib import Path
import sys,runpy,re,json
L=Path(__file__).resolve().parent
for name,url in [('registry-current.html','https://github.com/the-omega-institute/trureturing'),('openai-current.html','https://github.com/openai/math'),('author-current.html','https://arxiv.org/search/?query=Bille%2C+Artur&searchtype=author&abstracts=show&order=-announced_date_first&size=50')]:
 sys.argv=['work','fetch',name,url];runpy.run_path(str(L/'work.py'))
sys.argv=['work','freeze',str(L/'cached-screen.json')];ns=runpy.run_path(str(L/'work.py'));freeze=ns['freeze']
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-euler-turan-final-review/fresh/trureturing')
for rel in ['D5/S3/FiniteGroups/FiniteOttoCongruence.lean','D5/S3/Quantum/Dynamics/PurificationLowerBoundQutritRefutation.lean']:
 p=R/rel
 if p.exists():
  q=freeze(p);s=q.read_text();print('CACHED PROOF',rel,s[-10000:])
for p in sorted((L/'primary').glob('*current.html')):
 s=freeze(p).read_text()
 print(p.name,'COMMITS',re.findall(r'"currentOid":"([a-f0-9]+)"',s)[:3])
 if 'author' in p.name:
  for b in s.split('<li class="arxiv-result">')[1:]:
   a=re.search(r'arxiv.org/abs/([^"<]+)',b);t=re.search(r'<p class="title is-5 mathjax">(.*?)</p>',b,re.S)
   if a and t:print(a.group(1),re.sub('<[^>]+>','',t.group(1)).strip())
