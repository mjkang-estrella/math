from pathlib import Path
from html.parser import HTMLParser
import json,re,shutil
P=Path(__file__).resolve().parent
class Text(HTMLParser):
 def __init__(self):super().__init__();self.t=[];self.links=[]
 def handle_data(self,d):
  if d.strip():self.t.append(d.strip())
 def handle_starttag(self,t,a):
  for k,v in a:
   if k=='href' and v and ('pdf' in v or 'content' in v):self.links.append(v)
p=Text();p.feed((P/'live/publisher-chapter').read_text());(P/'live/publisher-chapter.txt').write_text('\n'.join(p.t));print('publisher PDF links',list(dict.fromkeys(p.links)))
base=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/sources/CONTENTS.md')
if base.exists():
 shutil.copy2(base,P/'context/base-CONTENTS.md')
 old=base.read_text();new=(P/'registry/openai-CONTENTS.md').read_text()
 oldheads=set(re.findall(r'^\*\*\d+\..*',old,re.M));heads=re.findall(r'^\*\*\d+\..*',new,re.M)
 added=[h for h in heads if h not in oldheads];(P/'catalog-delta.txt').write_text('\n'.join(added)+'\n');print('catalog',len(oldheads),len(heads),'changed/new headings',len(added))
for name in ['ledger.json','prior-campaign-context.json']:
 data=json.loads((P/'context'/name).read_text())
 print(name, 'keys',list(data))
 for a in data.get('accepted',[]):print(a.get('number'),a.get('title'),a.get('scope',''))
