from html.parser import HTMLParser
class Article(HTMLParser):
 def __init__(self):super().__init__();self.active=False;self.skip=0;self.out=[]
 def handle_starttag(self,t,a):
  if t=='article':self.active=True
  if not self.active:return
  if t=='math':self.out.append(dict(a).get('alttext',''));self.skip+=1
  elif t in ['script','style']:self.skip+=1
 def handle_endtag(self,t):
  if t in ['math','script','style']:self.skip=max(0,self.skip-1)
  if t=='article':self.active=False
 def handle_data(self,d):
  if self.active and not self.skip:self.out.append(d)
