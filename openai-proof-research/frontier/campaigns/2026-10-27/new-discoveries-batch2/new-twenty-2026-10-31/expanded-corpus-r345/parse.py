from html.parser import HTMLParser
import re
class Text(HTMLParser):
 def __init__(self): super().__init__(); self.out=[]; self.math=0; self.skip=0
 def handle_starttag(self,t,a):
  d=dict(a)
  if t in ['script','style']: self.skip+=1
  if t=='math': self.math+=1; self.out.append(' $'+d.get('alttext','')+'$ ')
  if t=='img' and d.get('alt'): self.out.append('[FIGURE '+d['alt']+']')
  if t in ['p','div','section','h1','h2','h3','li']: self.out.append('\n')
 def handle_endtag(self,t):
  if t in ['script','style']: self.skip-=1
  if t=='math': self.math-=1
 def handle_data(self,s):
  if not self.math and not self.skip:self.out.append(s)
def plaintext(b):
 p=Text();p.feed(b.decode());return re.sub(r'\n\s*\n','\n',re.sub(r'[ \t]+',' ',''.join(p.out)))
