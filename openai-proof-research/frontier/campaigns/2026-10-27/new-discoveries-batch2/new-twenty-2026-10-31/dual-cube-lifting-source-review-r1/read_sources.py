from html.parser import HTMLParser
import re
class Clean(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.article=False;self.skip=0
 def handle_starttag(self,t,attrs):
  if t=='article':self.article=True
  if t=='math':
   if self.article:self.out.append(dict(attrs).get('alttext',''))
   self.skip+=1
  elif t in ['script','style']:self.skip+=1
 def handle_endtag(self,t):
  if t in ['math','script','style']:self.skip=max(0,self.skip-1)
  if t=='article':self.article=False
 def handle_data(self,s):
  if self.article and not self.skip:self.out.append(s)
for name in ['376322','376322-v1','dual-companion']:
 c=Clean();c.feed((a/'sources'/f'{name}.html').read_text());text=re.sub(r'\s+',' ',' '.join(c.out))
 (p/f'{name}-clean.txt').write_text(text)
 print(name,len(text))
 if name=='376322':
  for start,end in [('3 Existence','4 Optimized'),('4.2 Optimization','4.3 Construction'),('5 Concluding','References')]:
   i=text.find(start);j=text.find(end,i+len(start));print(text[i:j])
 elif name=='dual-companion': print(text)
