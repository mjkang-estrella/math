import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import runpy,sys
sys.argv=['research.py','read']; d=runpy.run_path('research.py');globals().update({k:d[k] for k in ['L','write','dump','receipt','json','re']})
from html.parser import HTMLParser
class P(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  if t == 'math':self.out.append(dict(a).get('alttext',''))
  if t in ['script','style','math']:self.skip+=1
  if t in ['p','div','section','h1','h2','h3','h4','li']:self.out.append('\n')
 def handle_endtag(self,t):
  if t in ['script','style','math']:self.skip=max(0,self.skip-1)
 def handle_data(self,s):
  if not self.skip:self.out.append(s)
for path in sorted((L/'sources').glob('*.html')):
 p=P();p.feed(path.read_text());txt=re.sub(r'[ \t]+',' ',''.join(p.out)); txt=re.sub(r'\n\s*\n','\n',txt);write('text/'+path.stem+'.txt',txt)

receipt('parse-math')
