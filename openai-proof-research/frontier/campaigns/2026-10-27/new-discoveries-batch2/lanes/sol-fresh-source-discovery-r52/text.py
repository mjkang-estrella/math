from html.parser import HTMLParser
from pathlib import Path
class P(HTMLParser):
 def __init__(self):super().__init__();self.s=[]
 def handle_data(self,d):self.s.append(d)
for name in ['source','source-abs']:
 p=P();p.feed(Path('sources/'+name+'.html').read_text());Path('sources/'+name+'.txt').write_text(' '.join(p.s))
