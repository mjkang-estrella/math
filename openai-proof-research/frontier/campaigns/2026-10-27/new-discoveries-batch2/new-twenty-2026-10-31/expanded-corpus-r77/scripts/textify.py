import pathlib,json,re,subprocess
from html.parser import HTMLParser
class Text(HTMLParser):
 def __init__(self):super().__init__();self.parts=[]
 def handle_data(self,d):self.parts.append(d)
D=pathlib.Path(__file__).resolve().parents[1]
for p in (D/'sources').glob('*.html'):
 t=Text();t.feed(re.sub(r'<(svg|script|style)\b.*?</\1>', '', p.read_text(), flags=re.S));p.with_suffix('.txt').write_text(' '.join(t.parts))
for name in ['openai','omega']:
 a=json.loads((D/f'sources/{name}-head.json').read_text());print(name,a['sha'])
