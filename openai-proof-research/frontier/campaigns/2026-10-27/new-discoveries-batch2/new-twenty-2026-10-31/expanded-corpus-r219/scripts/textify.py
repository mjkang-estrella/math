from pathlib import Path
from html.parser import HTMLParser
class P(HTMLParser):
 def __init__(self):super().__init__();self.s=[]
 def handle_data(self,d):self.s.append(d)
D=Path(__file__).resolve().parents[1]
for p in (D/'http').glob('*.html'):
 s=P();s.feed(p.read_text());(D/'sources'/(p.stem+'.txt')).write_text(' '.join(' '.join(s.s).split()))
