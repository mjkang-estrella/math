import json,re,gzip,hashlib,datetime
from pathlib import Path
from html.parser import HTMLParser
class Text(HTMLParser):
 def __init__(self):super().__init__();self.parts=[];self.skip=0
 def handle_starttag(self,tag,attrs):
  if tag in ['script','style']:self.skip+=1
 def handle_endtag(self,tag):
  if tag in ['script','style']:self.skip=max(0,self.skip-1)
 def handle_data(self,s):
  if not self.skip:self.parts.append(s)
L=Path(__file__).resolve().parent
for n in ['journal','correction','arxiv-v2','rarity','power-followup']:
 p=L/'sources'/f'{n}.html'
 if p.exists():
  s=Text();s.feed(p.read_text());(L/'sources'/f'{n}.txt').write_text(' '.join(' '.join(s.parts).split()))
for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
 b=(L.parents[1]/n).read_bytes();(L/('context-'+n)).write_bytes(b)
 j=json.loads(b) if n.endswith('json') else None
 print(n, len(b), [(a.get('number'),a.get('title')) for a in j.get('accepted',[])] if isinstance(j,dict) else 'read complete bytes; NEXT mutable')
for n in ['journal','correction','arxiv-v2','rarity']:
 p=L/'sources'/f'{n}.txt'
 if not p.exists():continue
 s=p.read_text();print('\n',n)
 for pat in ['Conjecture 6.1','Theorem 3.4','quasi-polynomial','correction','Correction','Theorem 1','Theorem 2']:
  for m in list(re.finditer(re.escape(pat),s))[:5]:print(s[max(0,m.start()-150):m.start()+1800])
out=[]
for n in ['omega-tree.txt.gz','openai-tree.txt.gz']:
 p=L.parent/'root-edge-irregulator-final-freeze-r1'/n
 s=gzip.decompress(p.read_bytes()).decode()
 matches=[x for x in s.splitlines() if re.search('semigroup|Rosas|09500|infinite.chain|InfiniteChain',x,re.I)]
 out.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),matches=matches))
(L/'registry-path-screen.json').write_text(json.dumps(out,indent=2))
print('registry',json.dumps(out))
