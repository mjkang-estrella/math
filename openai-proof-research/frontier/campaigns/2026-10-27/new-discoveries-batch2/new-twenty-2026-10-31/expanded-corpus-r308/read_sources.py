import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
import json,re,sys
from html.parser import HTMLParser
class Text(HTMLParser):
 def __init__(self,s):super().__init__();self.parts=[];self.feed(s)
 def handle_data(self,d):self.parts.append(d)
 def get_text(self,*args,**kwargs):return ' '.join(' '.join(self.parts).split())
 def __str__(self):return ' '.join(self.parts)
def BeautifulSoup(s,*args):return Text(s)
P=Path(__file__).resolve().parent
if sys.argv[1]=='plan':
 jobs=[]; meta={}
 for r in json.loads((P/'reservation.json').read_text())['rows']:
  k=str(r['mathdb_id']);s=BeautifulSoup((P/'sources'/f'{k}-abs.html').read_text(),'html.parser');text=s.get_text(' ',strip=True)
  history=text[text.find('Submission history'):text.find('Submission history')+1300]; print(k,history)
  versions=sorted(set(re.findall(r'/abs/(\d+\.\d+v\d+)',(P/'sources'/f'{k}-abs.html').read_text())),key=lambda x:int(x.split('v')[-1]))
  latest=versions[-1] if versions else r['source_url'].split('/')[-1]+'v1'
  meta[k]={'versions':versions,'submission_history':history,'latest':latest}
  jobs.append([k+'-body.html','https://arxiv.org/html/'+latest])
 (P/'version-metadata.json').write_text(json.dumps(meta,indent=2));(P/'body-jobs.json').write_text(json.dumps(jobs))
else:
 for name in sys.argv[1:]:
  f=P/'sources'/name
  if not f.exists():continue
  s=BeautifulSoup(f.read_text(),'html.parser')
  t=s.get_text(' ',strip=True);(P/'sources'/(name+'.txt')).write_text(t)
  if 'body' in name:
   chunks=re.split(r'(?=Conjecture|conjecture|Assumption|Problem|Definition)',t)
   print(name,'BYTES',len(t));print('\n'.join(c[:2100] for c in chunks if re.match('Conjecture|Assumption|Problem',c))[:8500])
  else:
   for pat in ['recovery','paired coalition','polar space','subtraction','Hibi','inversion','binary scalar','Grassmann','QUP','toric','forbidden out','Koszul']:
    hits=list(re.finditer(pat,t,re.I));print(name,pat,len(hits))
    for m in hits[:3]:print(t[max(0,m.start()-100):m.start()+550])
