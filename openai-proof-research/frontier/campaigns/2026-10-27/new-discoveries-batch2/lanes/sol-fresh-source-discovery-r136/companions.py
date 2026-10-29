import json
from pathlib import Path
from html.parser import HTMLParser
L=Path(__file__).resolve().parent
class Text(HTMLParser):
 def __init__(self):super().__init__();self.out=[]
 def handle_data(self,s):
  if s.strip():self.out.append(s.strip())
p=Text();p.feed((L/'sources/polyserial-pmc.html').read_text());(L/'sources/polyserial-pmc.txt').write_text('\n'.join(p.out))
j=json.loads((L/'sources/frank-code-head.json').read_text());print('Frank code HEAD',j['sha'],j['commit']['committer']['date'])
print('paths',[(x['filename'],x['status']) for x in j['files']])
# Review all historical candidate/exclusion descriptions, not only accepted titles.
for n in ['context-2.json','context-3.json']:
 j=json.loads((L/'sources'/n).read_text())
 for k in ['excluded','candidates','held_candidates']:
  for x in j.get(k,[]):print(k,json.dumps(x,ensure_ascii=False))
