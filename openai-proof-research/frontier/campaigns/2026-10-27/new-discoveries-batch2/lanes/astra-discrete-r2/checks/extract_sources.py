"""Extract local HTML with MathML alttext intact (no network)."""
from html.parser import HTMLParser
from pathlib import Path
class Extract(HTMLParser):
 def __init__(self):
  super().__init__(); self.out=[]; self.skip=[]; self.math=0
 def handle_starttag(self,tag,attrs):
  if tag in ('script','style'): self.skip.append(tag)
  if self.skip:return
  if tag=='math':
   if not self.math:self.out.append(dict(attrs).get('alttext',''))
   self.math+=1
  elif not self.math and tag in ('p','div','section','h1','h2','h3','h4','h5','h6','li','tr'):self.out.append('\n')
 def handle_endtag(self,tag):
  if self.skip:
   if tag==self.skip[-1]:self.skip.pop()
   return
  if tag=='math':self.math-=1
 def handle_data(self,s):
  if not self.skip and not self.math:self.out.append(s)
for f in (Path(__file__).parent.parent/'sources').glob('*.html'):
 p=Extract();p.feed(f.read_text());f.with_suffix('.txt').write_text(''.join(p.out))
