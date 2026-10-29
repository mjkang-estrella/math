from pathlib import Path
from html.parser import HTMLParser
import json,urllib.request,datetime,hashlib
P=Path(__file__).resolve().parent
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
  if t in ['p','section','h1','h2','h3','h4','h5','h6','li']:self.out.append('\n')
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip-=1
 def handle_data(self,d):
  if not self.skip:self.out.append(d)
for n in ['arvind','lin']:
 parser=Parser();parser.feed((P/'sources'/(n+'.html')).read_text());(P/'sources'/(n+'.txt')).write_text(''.join(parser.out))
for n in ['openai','omega']:
 j=json.loads((P/'sources'/(n+'-head.json')).read_text());print(n,j['sha'],j['commit']['committer']['date'])
log=json.loads((P/'http.json').read_text())
for name,url in [('distance-prior.html','https://arxiv.org/html/2604.26385v1'),('hansen-closest.html','https://link.springer.com/article/10.1007/s00010-026-01314-5')]:
 row={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as r:data=r.read(15000000);row.update(status=r.status,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));(P/'sources'/name).write_bytes(data)
  parser=Parser();parser.feed(data.decode());(P/'sources'/name.replace('.html','.txt')).write_text(''.join(parser.out))
 except Exception as e:row['error']=str(e)
 log.append(row)
(P/'http.json').write_text(json.dumps(log,indent=2))
# streaming filename gate, then selected bounded passages
import subprocess
pat=r'Zagreb|Sarkhel|isoclin|2305[.]07301|2501[.]18656|2604[.]26385'
a=subprocess.run(['rg','-l','-i',pat,'openai-proof-research/frontier/campaigns','-g','*.md','-g','*.json','-g','*.txt'],capture_output=True,text=True)
P.joinpath('final-duplicate-filenames.txt').write_text(a.stdout)
for f in a.stdout.splitlines():
 if '/sol-fresh-source-discovery-r83/' in f:continue
 if any(x in Path(f).name.lower() for x in ['finding','discovery','summary','provenance','progress']):
  z=subprocess.run(['rg','-n','-i','-m','4',pat,f],capture_output=True,text=True);print(f,z.stdout[:3000])
