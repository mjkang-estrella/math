from review_tools import *
import urllib.request,urllib.error,re
from html.parser import HTMLParser
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.a=[]
 def handle_data(self,d):
  if d.strip():self.a.append(d.strip())
def get(url,name):
 utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical source review'}),timeout=30) as f:raw=f.read(8000000);status=f.status
  (R/name).write_bytes(raw);rec=dict(url=url,utc=utc,status=status,path=name,sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw))
 except urllib.error.HTTPError as e:rec=dict(url=url,utc=utc,status=e.code,error=str(e));raw=None
 with (R/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(json.dumps(rec))
 if rec['status'] in [403,429]:sys.exit(0)
 return raw
head=json.loads((R/'omega-head.json').read_text())[0]['sha']
d=json.loads(get('https://api.github.com/repos/the-omega-institute/trureturing/compare/0a10157da355f1825f38212dd4c2869925ae6785...'+head,'omega-new-delta.json'))
pattern=re.compile(r'supertoken|366438|2412.?20558|metric.?dimension|johnson|separating|multiset.?resolv',re.I)
matches=[{'path':f['filename'],'patch':f.get('patch','')[:3000]} for f in d.get('files',[]) if pattern.search(f['filename'])]
print('new delta',d.get('total_commits'),len(d.get('files',[])),matches)
# Stream original tree lines; retain only exact target metadata, excluding frozen/generated echoes.
hits=[]
for label in ['omega','openai']:
 p=B/'lanes/root-edge-irregulator-final-freeze-r1'/(label+'-tree.txt')
 with p.open() as f:
  for line in f:
   if pattern.search(line) and not re.search(r'Golden/|Frozen/|inventory|cache|duplicate',line,re.I):hits.append({'registry':label,'line':line.strip()})
(R/'registry-target-matches.json').write_text(json.dumps({'baseline_matches':hits,'new_delta_commits':d.get('total_commits'),'new_delta_files':len(d.get('files',[])),'new_matches':matches},indent=2)+'\n');print('baseline matches',hits[:25], 'count',len(hits))
# Read full cached successor body in a legible extraction; retain only source text.
p=Parser();p.feed((R/'copy/sources/metric-successor.html').read_text());text=' '.join(p.a)
(R/'successor-body.txt').write_text(text)
print('SUCCESSOR BODY',text[:28000])
get('https://arxiv.org/abs/2604.06164','successor-abs.html')
get('https://arxiv.org/html/2507.11686v1','multiset-body.html')
