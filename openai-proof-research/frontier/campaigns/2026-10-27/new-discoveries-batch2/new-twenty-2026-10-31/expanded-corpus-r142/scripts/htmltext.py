from html.parser import HTMLParser
from pathlib import Path
class P(HTMLParser):
 def handle_data(self,d): self.out.append(d)
for f in Path('sources').glob('*.html'):
 p=P();p.out=[];p.feed(f.read_text());f.with_suffix('.txt').write_text(' '.join(p.out))
