import pathlib,json,re
from html.parser import HTMLParser
L=pathlib.Path(__file__).resolve().parent
class P(HTMLParser):
 def __init__(self):super().__init__();self.a=[]
 def handle_data(self,d):self.a.append(d)
for f in sorted((L/'sources').glob('*.html')):
 p=P();p.feed(f.read_text());s=re.sub(r'\s+',' ',' '.join(p.a));(f.with_suffix('.txt')).write_text(s)
 print('\nFILE',f.stem,'HEAD',s[:170])
 patterns=['Conjecture','conjecture','disproved','refuted']
 matches=list(re.finditer('|'.join(patterns),s))
 for m in matches[:8]:print(s[max(0,m.start()-150):m.start()+1000])
