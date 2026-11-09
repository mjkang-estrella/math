from html.parser import HTMLParser
from pathlib import Path
import hashlib,json,re
L=Path(__file__).resolve().parent
class P(HTMLParser):
 def __init__(self):super().__init__();self.a=[]
 def handle_data(self,d):self.a.append(d)
p=L/'primary/2019-publisher.html';r=json.loads((L/'publisher-access.json').read_text());assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
x=P();x.feed(p.read_text());s=' '.join(x.a);s=re.sub(r'\s+',' ',s)
(L/'primary/2019-publisher-extracted.txt').write_text(s)
for word in ['fragment flipped','Conjecture 1','in general such','trace','character']:
 start=0
 for k in range(4):
  i=s.lower().find(word.lower(),start)
  if i<0:break
  print(word,':',s[max(0,i-300):i+1300]);start=i+len(word)
assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
