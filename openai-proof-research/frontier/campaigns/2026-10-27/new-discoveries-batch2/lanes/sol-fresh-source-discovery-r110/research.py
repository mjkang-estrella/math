from pathlib import Path
import json,re,hashlib,urllib.request,datetime,sys
from html.parser import HTMLParser
P=Path(__file__).resolve().parent;R=next(x for x in P.parents if x.name=='openai-proof-research');B=P.parent.parent
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(f):
 h=hashlib.sha256()
 with f.open('rb') as s:
  for b in iter(lambda:s.read(65536),b''):h.update(b)
 return h.hexdigest()
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
  if t in ['p','h1','h2','h3','h4','section','li','div']:self.out.append('\n')
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip-=1
 def handle_data(self,d):
  if not self.skip:self.out.append(d)
def get(n,u):
 row={'file':n,'url':u,'utc':now()}
 try:
  with urllib.request.urlopen(u,timeout=25) as r:
   row.update(status=r.status,headers=dict(r.headers));f=P/'sources'/n
   with f.open('wb') as s:
    for b in iter(lambda:r.read(65536),b''):s.write(b)
  row.update(sha256=sha(f),bytes=f.stat().st_size)
  if n.endswith('.html'):
   p=Parser();p.feed(f.read_text());f.with_suffix('.txt').write_text('\n'.join(' '.join(l.split()) for l in ''.join(p.out).splitlines() if l.strip()))
 except Exception as e:row['error']=str(e)
 rows=json.loads((P/'http.json').read_text()) if (P/'http.json').exists() else [];rows.append(row);(P/'http.json').write_text(json.dumps(rows,indent=2));print(json.dumps(row),flush=True)
if sys.argv[1]=='audit':
 pat=re.compile(r'Kudra|(?<!\d)374626(?!\d)|2605[.]07628|quasi.stable idealizer|2608[.]12531|Marashdeh|quotient.submodule equidistribution|quotient.closed subcategories|2607[.]14270|Pojar',re.I)
 assert all(pat.search(s) for s in ['2605.07628','2608.12531','2607.14270']);assert all(not pat.search(s) for s in ['2605x07628','2608x12531','2607x14270'])
 count=0;hits=[];stream=(P/'duplicate-corpus.jsonl').open('w')
 for f in R.rglob('*'):
  if not f.is_file() or P in f.parents or f.suffix.lower() not in ['.md','.json','.txt','.py','.sh','.js','.ts','.html','.tex','.lean','.yaml','.yml']:continue
  # all-date reports plus every textual note/helper in embedded tool/script/agent/openproblem/review trees
  name=f.name.lower();parts=str(f.relative_to(R)).lower()
  if not (any(t in name for t in ['summary','discovery','findings','proof','review','ledger','screened-out','openproblem','agent','next','context']) or any(t in parts for t in ['/tools/','/scripts/','/agent/','/agents/','review','openproblem'])):continue
  row={'path':str(f.relative_to(R)),'bytes':f.stat().st_size,'sha256':sha(f)};stream.write(json.dumps(row)+'\n');count+=1;matches=[]
  with f.open(errors='replace') as s:
   for i,l in enumerate(s,1):
    for match in pat.finditer(l):matches.append({'line':i,'text':l[max(0,match.start()-150):match.end()+250].strip()})
  if matches:hits.append({'path':row['path'],'hits':matches})
 stream.close();(P/'duplicate-audit.json').write_text(json.dumps({'utc':now(),'pattern':pat.pattern,'regex_controls':'PASS literal dot positive/negative','files':count,'hits':hits,'scope':'All-date streaming lexical; no semantic absence certificate'},indent=2));print(json.dumps(hits,indent=2)[:24000]);print('files',count)
 ctx=[]
 for f in [R/'AGENTS.md',B/'AGENTS.md',B/'ledger.json',B/'NEXT.md',B/'prior-campaign-context.json',R/'sources/upstream.json',R/'sources/CONTENTS.md']:
  obj=json.loads(f.read_text()) if f.suffix=='.json' else f.read_text();ctx.append({'path':str(f),'bytes':f.stat().st_size,'sha256':sha(f)})
 (P/'context-read.json').write_text(json.dumps(ctx,indent=2))
elif sys.argv[1]=='fetch':
 for n,u in [('kudra-abs.html','https://arxiv.org/abs/2605.07628'),('kudra.html','https://arxiv.org/html/2605.07628v1'),('type-abs.html','https://arxiv.org/abs/2608.12531'),('type.html','https://arxiv.org/html/2608.12531v1')]:get(n,u)
elif sys.argv[1]=='get':get(sys.argv[2],sys.argv[3])
