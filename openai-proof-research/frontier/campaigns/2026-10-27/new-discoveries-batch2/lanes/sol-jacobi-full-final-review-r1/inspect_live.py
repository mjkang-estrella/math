from pathlib import Path
import json,re,urllib.request,hashlib,datetime
from html.parser import HTMLParser
p=Path('evidence');old=Path('../root-jacobi-final-prior-r1/evidence')
class Read(HTMLParser):
 def __init__(self):super().__init__();self.t=[]
 def handle_starttag(self,t,a):
  a=dict(a)
  if t=='math' and 'alttext'in a:self.t.append(' MATH '+a['alttext']+' ')
  if t in ('p','div','section','h1','h2','h3','h4'):self.t.append('\n')
 def handle_data(self,d):self.t.append(d)
for n in ['primary','companion','primary-abs','companion-abs']:
 x=Read();x.feed((p/(n+'.html')).read_text());(p/(n+'.txt')).write_text(''.join(x.t))
delta={};hits={};fetch=[]
for dn in ['Problems','D5','Blueprint']:
 n='omega-'+dn+'-tree.json';new=json.loads((p/n).read_text());prev=json.loads((old/n).read_text());a={i['path']:i['sha']for i in prev['tree']if i['type']=='blob'}
 delta[dn]=[i for i in new['tree']if i['type']=='blob'and a.get(i['path'])!=i['sha']]
 hits[dn]=[i for i in new['tree']if re.search('jacobi|riccati|dikii|dyadic|phaselaw',i['path'],re.I)]
 for i in delta[dn]:print('CHANGED',dn,i['path'])
 for i in hits[dn]:
  if re.search('CompositionalSquareDyadic|PhaseLawDyadic',i['path'])and i['path'].endswith(('.md','.lean')):fetch.append(dn+'/'+i['path'])
# Fetch all changed problem bodies, plus exact potentially confusing theorem bodies.
fetch += ['Problems/'+i['path']for i in delta['Problems']if i['path'].endswith(('.md','.json'))]
head=json.loads((p/'omega-head.json').read_text())['sha'];rec=[]
for k,path in enumerate(dict.fromkeys(fetch)):
 u=f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{head}/{path}'
 try:
  with urllib.request.urlopen(u,timeout=30) as r:d=r.read()
  n=f'body-{k}.txt';(p/n).write_bytes(d);rec.append(dict(path=path,url=u,file=n,sha256=hashlib.sha256(d).hexdigest()))
 except Exception as e:rec.append(dict(path=path,error=str(e)))
(p/'delta.json').write_text(json.dumps(delta,indent=2));(p/'hits.json').write_text(json.dumps(hits,indent=2));(p/'bodies.json').write_text(json.dumps(rec,indent=2))
print('bodies',rec)
