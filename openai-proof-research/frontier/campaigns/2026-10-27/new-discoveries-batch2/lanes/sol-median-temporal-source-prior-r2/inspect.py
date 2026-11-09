from pathlib import Path
from html.parser import HTMLParser
import json,re
L=Path(__file__).resolve().parent
class P(HTMLParser):
 def handle_starttag(self,t,a):
  if t=='a':
   d=dict(a)
   if 'href' in d: print(d['href'])
p=P();p.feed((L/'sources/search.html').read_text())
d=json.loads((L/'sources/crossref.json').read_text())['message']
print('CROSSREF',json.dumps({k:d.get(k) for k in ['link','resource','published','author','relation']}))
for name in ['abb-abs.html','damron-abs.html']:
 s=(L/'sources'/name).read_text()
 print(name,re.findall(r'.{0,80}(?:v[123]\]|Submitted|202[0-9]|Journal reference|doi.org|Authors:).{0,130}',s))
