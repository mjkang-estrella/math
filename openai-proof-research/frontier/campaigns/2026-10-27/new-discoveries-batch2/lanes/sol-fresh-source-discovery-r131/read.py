import sys,json,hashlib,re
from pathlib import Path
from html.parser import HTMLParser
L=Path(__file__).resolve().parent;B=L.parent.parent
class Reader(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.hide=0
 def handle_starttag(self,t,a):
  if t in ('script','style'):self.hide+=1
  if t in ('p','div','section','h1','h2','h3','h4','h5','h6','li'):self.out.append('\n')
 def handle_endtag(self,t):
  if t in ('script','style'):self.hide-=1
 def handle_data(self,d):
  if not self.hide:self.out.append(d)
if sys.argv[1]=='html':
 p=L/'sources'/sys.argv[2];r=Reader();r.feed(p.read_text());s=''.join(r.out);s=re.sub(r'\n\s*\n','\n',s);p.with_suffix('.txt').write_text(s)
 print('extracted',p.name,len(s))
elif sys.argv[1]=='context':
 rec=[]
 for i,p in enumerate([B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B/'NEXT.md',B/'lanes/root-r128-r129-handback/DECISION.md',B/'lanes/root-r128-r129-handback/R130-DECISION.md']):
  b=p.read_bytes();(L/'sources'/('context-'+p.name)).write_bytes(b);rec.append(dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),mutable=p.name=='NEXT.md'))
  if p.suffix=='.json':
   j=json.loads(b);print(p.name,'keys',list(j));print(json.dumps(j,ensure_ascii=False)[:500] if 'accepted' not in j else [(x.get('number'),x.get('title'),x.get('one_family')) for x in j['accepted']])
  else:
   lines=b.decode().splitlines();(L/'sources'/('context-'+p.stem+'-outline.txt')).write_text('\n'.join(x for x in lines if re.search(r'^(#|Current|Counts|Total|Latest)|r12[5-9]|r130',x)))
 (L/'context-receipts.json').write_text(json.dumps(rec,indent=2))
elif sys.argv[1]=='heads':
 for n in ['omega','openai']:
  j=json.loads((L/'sources'/(n+'-head.json')).read_text());print(n,j['sha'],j['commit']['committer']['date'],j['commit']['message'][:160])
elif sys.argv[1]=='links':
 s=(L/'sources/journal-page.html').read_text();print('\n'.join(sorted(set(re.findall(r'https?[^\s<>"\\]+',s)))[:100]));print([x[:300] for x in re.findall(r'.{0,50}downloadLink.{0,180}',s)])
