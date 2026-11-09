from html.parser import HTMLParser
class Text(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.math=False
 def handle_starttag(self,tag,attrs):
  if tag=='math':self.out.append(' $'+dict(attrs).get('alttext','')+'$ ');self.math=True
 def handle_endtag(self,tag):
  if tag=='math':self.math=False
  if tag in ['p','div','section','h1','h2','h3','h4','li']:self.out.append('\n')
 def handle_data(self,data):
  if not self.math:self.out.append(data)
