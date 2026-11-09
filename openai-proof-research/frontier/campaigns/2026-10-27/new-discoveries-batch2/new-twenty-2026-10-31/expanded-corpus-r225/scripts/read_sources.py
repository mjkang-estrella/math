import hashlib,pathlib,json,re,html
from html.parser import HTMLParser
D=pathlib.Path(__file__).resolve().parents[1]
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ('script','style'):self.skip+=1
  if t in ('p','div','section','h1','h2','h3','h4','li','figure'):self.out.append('\n')
 def handle_endtag(self,t):
  if t in ('script','style'):self.skip=max(0,self.skip-1)
 def handle_data(self,s):
  if not self.skip:self.out.append(s)
for p in (D/'sources').glob('*.html'):
 s=Parser();s.feed(p.read_text());t=''.join(s.out);t=re.sub(r'[^\S\n]+',' ',t);t=re.sub(r'\n+','\n',t);p.with_suffix('.txt').write_text(t)
 if '-abs' in p.name:
  for l in t.splitlines():
   if re.search(r'\[v\d+\]|Submission history',l):print(p.stem,l)
 else:
  ls=t.splitlines()
  for j,l in enumerate(ls):
   if re.search(r'Conjecture',l):print(p.name,'\n','\n'.join(ls[max(0,j-1):j+5])[:5000])
h=(D/'history-matches.txt').read_text();pat=re.compile(r'(?<![0-9a-f])(?:'+ '|'.join(map(str,json.loads((D/'reservation.json').read_text())['ids']))+r')(?![0-9a-f])')
(D/'history-filtered.txt').write_text('\n'.join(l[:6000] for l in h.splitlines() if pat.search(l))+'\n')
for name in ['ledger.json','../ledger.json','../prior-campaign-context.json']:
 p=D.parent/name;o=json.loads(p.read_text());print(name,list(o)[:20])
 # record hashes and family summaries, do not duplicate whole ledgers
 (D/('context-'+name.replace('../','parent-'))).write_text(json.dumps({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'accepted':o.get('accepted',[]),'excluded':o.get('excluded',[])},indent=2)+'\n')
