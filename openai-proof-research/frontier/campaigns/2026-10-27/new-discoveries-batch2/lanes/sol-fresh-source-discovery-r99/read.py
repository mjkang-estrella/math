from pathlib import Path
from html.parser import HTMLParser
class Extract(HTMLParser):
 def __init__(self):super().__init__();self.bits=[]
 def handle_data(self,d):self.bits.append(d)
def plain(s):
 e=Extract();e.feed(s);return " ".join(e.bits)
P=Path(__file__).resolve().parent
for n in ['finite','coalition']:
 f=P/('sources/'+n+'.html')
 if f.exists():
  s=plain(f.read_text());(P/('sources/'+n+'.txt')).write_text(s)
  for t in ['Conjecture','Problem','Super domatic']:
   i=0
   while (i:=s.find(t,i))>=0:print(n,s[max(0,i-150):i+2200]);i+=len(t)
