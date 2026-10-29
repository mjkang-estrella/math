import json,re,hashlib,subprocess
from pathlib import Path
from html.parser import HTMLParser
P=Path(__file__).resolve().parent; B=P.parent.parent; R=B.parents[1]
patterns=r'2507[.]07243|celano|maximum.displacement|displacement.{0,35}unimodal|interval.parking|2609[.]39917|Mohammadi'
r=subprocess.run(['rg','-l','-i',patterns,str(R),'-g','*.md','-g','*.json'],capture_output=True,text=True)
files=r.stdout.splitlines(); (P/'duplicate-filenames.txt').write_text(r.stdout)
hits=[]
for f in files:
 if str(P) in f:continue
 t=Path(f).read_text(errors='replace')
 for m in list(re.finditer(patterns,t,re.I))[:5]:
  hits.append({'file':f,'offset':m.start(),'excerpt':t[max(0,m.start()-140):m.end()+210]})
(P/'duplicate-sections.json').write_text(json.dumps(hits,indent=2))
context={}
for name in ['ledger.json','prior-campaign-context.json']:
 t=(B/name).read_bytes();d=json.loads(t)
 context[name]={'sha256':hashlib.sha256(t).hexdigest(),'accepted':[{'number':x['number'],'title':x['title'],'scope':x.get('scope')} for x in d['accepted']], 'excluded':d.get('excluded',[]),'candidates':d.get('candidates',[])}
(P/'context-reading.json').write_text(json.dumps(context,indent=2))
class Text(HTMLParser):
 def __init__(self):super().__init__();self.s=[]
 def handle_data(self,s):
  if s.strip():self.s.append(s.strip())
for n in ['source-v2','followup','author-publications']:
 p=Text();p.feed((P/(n+'.html')).read_text());t='\n'.join(p.s);(P/(n+'.txt')).write_text(t)
head=(P/'omega-head.html').read_text()
print('HEAD fields',re.findall(r'currentOid.{0,85}',head)[:3])
t=(P/'followup.txt').read_text()
for pat in ['Conjecture','unimodal','maximum displacement','standardiz']:
 print('FOLLOWUP',pat)
 for m in list(re.finditer(pat,t,re.I))[:6]:print(t[max(0,m.start()-100):m.end()+400])
print('duplicate files',len(files),'bounded sections',len(hits))
