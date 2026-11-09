import pathlib,json,re,runpy,subprocess
D=pathlib.Path(__file__).resolve().parents[1]
for name in ['math','trureturing']:
 o=json.loads((D/'sources'/f'{name}-tree.json').read_text());print(name,'truncated',o.get('truncated'))
 hits=[x['path'] for x in o.get('tree',[]) if re.search('golomb|lee.code|layered|quasi.kernel|saxton|supermagic|perfect.basis|zero.sum|cordial|gatex|inversion',x['path'],re.I)];print('\n'.join(hits[:40]))
 (D/'outputs'/f'{name}-path-hits.json').write_text(json.dumps(hits,indent=2))
m=runpy.run_path(str(D/'scripts/fetch.py'))
for aid in ['2210.03336v1','2212.03026']:
 p=D/'sources'/f'{aid}.pdf'
 if m['fetch']('https://arxiv.org/pdf/'+aid,p):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))])
(D/'outputs/version-receipts.json').write_text(json.dumps(m['receipts'],indent=2))
from html.parser import HTMLParser
class P(HTMLParser):
 def __init__(self):super().__init__();self.hide=0;self.parts=[]
 def handle_starttag(self,tag,attrs):
  if tag in ['script','style']:self.hide+=1
 def handle_endtag(self,tag):
  if tag in ['script','style']:self.hide=max(0,self.hide-1)
  if tag in ['p','div']:self.parts.append('\n')
 def handle_data(self,d):
  if not self.hide:self.parts.append(d)
p=P();p.feed((D/'sources/super-proof.html').read_text());(D/'sources/super-proof.txt').write_text(''.join(p.parts))
