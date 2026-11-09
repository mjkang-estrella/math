from html.parser import HTMLParser
import pathlib,re
class P(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.math=False;self.skip=False
 def handle_starttag(self,t,a):
  a=dict(a)
  if t=='math':self.out.append(' '+a.get('alttext','')+' ');self.math=True
  if t in ['script','style']:self.skip=True
  if t in ['p','h1','h2','h3','h4','li','figcaption']:self.out.append('\n')
 def handle_endtag(self,t):
  if t=='math':self.math=False
  if t in ['script','style']:self.skip=False
 def handle_data(self,s):
  if not self.math and not self.skip:self.out.append(s)
L=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r174')
for p in (L/'sources').glob('*.html'):
 s=P();s.feed(p.read_text());p.with_suffix('.txt').write_text(re.sub(r'[ \t]+',' ',''.join(s.out)))
