import pathlib,json,re
from html.parser import HTMLParser
L=pathlib.Path(__file__).parent
class Text(HTMLParser):
 def __init__(self): super().__init__();self.out=[]
 def handle_starttag(self,t,a):
  if t in ('p','section','h1','h2','h3','h4','div'):self.out.append('\n')
  if t=='math':self.out.append(' '+dict(a).get('alttext','')+' ')
 def handle_data(self,d):self.out.append(d)
for p in (L/'sources').glob('*.html'):
 parser=Text();parser.feed(p.read_text());s=''.join(parser.out);s=re.sub(r'[ \t]+',' ',s);s=re.sub(r'\n\s*\n','\n',s)
 p.with_suffix('.txt').write_text(s)
B=L.parent.parent
with (L/'history/governing-digest.txt').open('w') as out:
 for name in ('ledger.json','prior-campaign-context.json'):
  v=json.loads((B/name).read_text());out.write(name+'\n')
  for k,items in v.items():
   if isinstance(items,list):
    for item in items:
     if isinstance(item,dict):out.write(json.dumps({x:y for x,y in item.items() if x in ('number','title','source_target','reason','scope','status','path','novelty_limit','one_family')},ensure_ascii=False)+'\n')
   else:out.write(k+': '+str(items)+'\n')
