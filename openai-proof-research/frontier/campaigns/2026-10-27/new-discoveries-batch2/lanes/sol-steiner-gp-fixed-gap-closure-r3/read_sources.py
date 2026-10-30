from work import *
from html.parser import HTMLParser
class Text(HTMLParser):
 def __init__(self):super().__init__();self.s=[]
 def handle_data(self,s):self.s.append(s)
for i in [3,14,17]:
 p=R/f'citations/{i}.html';t=Text();t.feed(p.read_text());s='\n'.join(t.s);(R/f'citations/{i}.txt').write_text(s)
 j=s.find('Abstract');print(i,s[j:j+2500])
for i in [10,19]:
 x=json.loads((L/'citation-abstracts.json').read_text())[i-1]
 b=fetch('https://api.crossref.org/works/'+x['doi'].split('doi.org/')[1],f'citations/{i}-crossref.json')
 if b:print(i,json.loads(b)['message'].get('abstract','NO ABSTRACT'))
for i in [1,5,9,12,13]:
 p=R/f'citations/{i}.txt';lines=p.read_text().splitlines(); hits=[]
 for j,s in enumerate(lines):
  if re.search(r'Steiner|twin|clone|substitut|blow.up|Theorem|Lemma|Proposition',s,re.I):hits.append((j+1,s))
 print(i,hits)
