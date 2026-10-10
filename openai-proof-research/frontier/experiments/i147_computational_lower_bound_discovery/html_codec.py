"""Pure deterministic normalization; no acquisition or mutation."""
from html.parser import HTMLParser
class Text(HTMLParser):
 def __init__(self):super().__init__();self.parts=[];self.skip=0;self.math=0
 def handle_starttag(self,tag,attrs):
  if tag in ('script','style'):self.skip+=1
  if tag=='math':
   self.math+=1;self.parts.append(dict(attrs).get('alttext','[math]'))
  if tag in ('p','div','section','h1','h2','h3','h4','h5','h6','li','tr','br'):self.parts.append('\n')
 def handle_endtag(self,tag):
  if tag in ('script','style'):self.skip-=1
  if tag=='math':self.math-=1
  if tag in ('p','div','section','li','tr'):self.parts.append('\n')
 def handle_data(self,data):
  if not self.skip and not self.math:self.parts.append(data)
 def text(self):return '\n'.join(x.strip() for x in ''.join(self.parts).splitlines() if x.strip())

