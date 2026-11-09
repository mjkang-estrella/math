from pathlib import Path
from html.parser import HTMLParser
import os,re,json
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
D=Path(__file__).resolve().parents[1]
class Parser(HTMLParser):
 def __init__(self): super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ('script','style'):self.skip+=1
  if t=='math':self.out.append(dict(a).get('alttext',''))
 def handle_endtag(self,t):
  if t in ('script','style'):self.skip-=1
 def handle_data(self,s):
  if not self.skip:self.out.append(s)
for n in ['survey','dirichlet','composition','integrability']:
 p=Parser();p.feed((D/'downloads'/(n+'.html')).read_text());t=' '.join(p.out);(D/'downloads'/(n+'.txt')).write_text(t)
 print('BODY',n,'TITLE',t[:800])
 for key in ['Theorem','Conjecture','graph','2410.10695','2506.12624','contact order']:
  ms=list(re.finditer(re.escape(key),t,re.I));print('KEY',key,'count',len(ms))
  for m in (ms[:4] if key in ['Theorem','Conjecture'] else ms[:2]):print(t[max(0,m.start()-150):m.start()+1800])
