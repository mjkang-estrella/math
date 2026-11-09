from html.parser import HTMLParser
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  d=dict(a)
  if t=="math":self.out.append(" "+d.get("alttext","")+" ");self.skip+=1
  elif t in ["script","style"]:self.skip+=1
  elif t=="img":self.out.append(" [image: "+d.get("alt","")+" src="+(d.get("src","")[:200] if not d.get("src","").startswith("data:") else "embedded")+"] ")
  elif t in ["p","div","section","h1","h2","h3","li","tr"]:self.out.append("\n")
 def handle_endtag(self,t):
  if t in ["math","script","style"]:self.skip=max(0,self.skip-1)
 def handle_data(self,d):
  if not self.skip:self.out.append(d)
def parse(b):
 h=Parser();h.feed(b.decode());return "\n".join(x.strip() for x in "".join(h.out).splitlines() if x.strip())
