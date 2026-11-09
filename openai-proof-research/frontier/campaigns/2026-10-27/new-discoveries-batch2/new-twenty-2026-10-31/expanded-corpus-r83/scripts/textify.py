from html.parser import HTMLParser
class Text(HTMLParser):
 def __init__(self):super().__init__();self.out=[]
 def handle_data(self,d):self.out.append(d)
from pathlib import Path
import json
D=Path(__file__).resolve().parents[1]
for p in (D/'sources').glob('*.html'):
 s=Text();s.feed(__import__('re').sub(r'<(script|style)\b[^>]*>.*?</\1>', '', p.read_text(), flags=__import__('re').S));(p.with_suffix('.txt')).write_text(' '.join(' '.join(s.out).split()))
for name in ['openai','omega']:
 o=json.loads((D/f'sources/{name}-head.json').read_text());print(name,o['sha'])
for p in (D/'sources').glob('*.txt'):
 t=p.read_text(); print('\nFILE',p.name, t[:300]);
 for word in ['Conjecture','conjecture','Question']:
  starts=[m.start() for m in __import__('re').finditer(word,t)]
  for k in starts[:10]:print(t[max(0,k-120):k+700])
