import pathlib,json
from html.parser import HTMLParser
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.parts=[];self.skip=0
 def handle_starttag(self,tag,attrs):
  if tag in ("script","style"):self.skip+=1
 def handle_endtag(self,tag):
  if tag in ("script","style"):self.skip=max(0,self.skip-1)
 def handle_data(self,data):
  if not self.skip:self.parts.append(data)
D=pathlib.Path(__file__).resolve().parents[1]
for p in (D/'sources').glob('*.html'):
 if False:continue
 s=Parser();s.feed(p.read_text())
 (D/'outputs'/(p.stem+'.txt')).write_text(' '.join(' '.join(s.parts).split()))
for key in ['leanpool','openai','omega']:
 j=json.loads((D/'sources'/f'{key}-head.json').read_text());print(key,j['sha'])
for p in sorted((D/'outputs').glob('*abs.txt')):
 t=p.read_text();a=t.find('Submission history');b=t.find('Access Paper');print(p.name,t[a:b][:1600])
