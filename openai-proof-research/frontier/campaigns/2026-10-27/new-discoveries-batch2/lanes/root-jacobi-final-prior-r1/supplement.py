from pathlib import Path
import json,urllib.request,datetime,hashlib
from html.parser import HTMLParser
p=Path('evidence');rows=[]
class Text(HTMLParser):
 def __init__(self):super().__init__();self.parts=[]
 def handle_data(self,s):self.parts.append(s)
for n in ['primary-abs','companion-abs','primary','companion']:
 t=Text();t.feed((p/(n+'.html')).read_text());s=' '.join(' '.join(t.parts).split());(p/(n+'-readable.txt')).write_text(s)
 if n.endswith('abs'):
  i=s.find('Submission history');print(n,s[i:i+800])
head=json.loads((p/'omega-head.json').read_text())['sha']
paths=['Problems/'+x for x in json.loads((p/'delta-screen.json').read_text())['omega-Problems-tree.json']['changed']]
paths+=['Blueprint/D5/S3/Analytic/Asymptotics/PhaseLawDyadicCoercivity.md']
for i,path in enumerate(paths):
 url=f'https://raw.githubusercontent.com/the-omega-institute/trureturing/{head}/{path}'
 row={'url':url,'path':path,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as r:raw=r.read();row['status']=r.status
  name=f'body-{i}.txt';(p/name).write_bytes(raw);row.update(file=name,sha256=hashlib.sha256(raw).hexdigest());print(path,raw.decode()[:16000])
 except Exception as e:row['error']=str(e)
 rows.append(row)
(p/'supplement-retrieval.json').write_text(json.dumps(rows,indent=2)+'\n')
