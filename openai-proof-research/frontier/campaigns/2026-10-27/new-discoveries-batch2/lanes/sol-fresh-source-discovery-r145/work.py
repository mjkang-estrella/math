import sys,json,hashlib,urllib.request,datetime,gzip,re,subprocess
from pathlib import Path
L=Path(__file__).resolve().parent;B=L.parents[1];R=B.parents[3]
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,x): (L/n).write_text(json.dumps(x,indent=2)+'\n')
if sys.argv[1]=='registry':
 import sqlite3
 old=L.parent/'sol-fresh-source-discovery-r133'
 db=sqlite3.connect('file:'+str(old/'history.sqlite')+'?mode=ro',uri=True)
 pat=re.compile(rb'Nordhaus|14060|12008|Laplacian.{0,70}(product|kth)|(?:product|kth).{0,70}Laplacian',re.I)
 out=dict(bodies_read=0,hits=[],missing=[],oversize=[],semantic_clearance=False,fixed_omega='a19a578cd06b57a4ea4d287cb0df92f9085117ae',fixed_openai='7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a',latest_delta_capped=True,head_refresh=False)
 for h,p in db.execute('select h,path from bodies'):
  if not re.search(r'(?:omega|openai|trureturing).*(?:tree|paths)|(?:tree|paths).*(?:omega|openai|trureturing)',p,re.I):continue
  q=R/p
  try:
   if q.stat().st_size>12000000:out['oversize'].append(p);continue
   b=q.read_bytes();out['bodies_read']+=1
   if pat.search(b):out['hits'].append(dict(path=p,sha256=sha(b),matches=[b[max(0,m.start()-150):m.end()+250].decode(errors='replace') for m in pat.finditer(b)]))
  except OSError as e:out['missing'].append([p,str(e)])
 for n in [135,137,139]:
  q=L.parent/('sol-fresh-source-discovery-r'+str(n))
  for name in ['registry-delta-receipt.json','registry-delta.json']:
   f=q/name
   if f.exists():out.setdefault('inherited_receipts',[]).append(dict(path=str(f),sha256=sha(f.read_bytes())))
 save('registry-retained.json',out);print({k:v for k,v in out.items() if k!='hits'})
 for x in out['hits']:
  print(x['path'])
  for s in x['matches']:print(s)
elif sys.argv[1]=='view':
 j=json.loads((L/('history-'+sys.argv[2]+'.json')).read_text())
 for h in j['hits']:
  print(h['path'])
  for m in re.finditer(j['pattern'],h['body'],re.I):print(repr(h['body'][max(0,m.start()-90):m.end()+160]))
elif sys.argv[1]=='parse':
 from html.parser import HTMLParser
 class Parser(HTMLParser):
  def __init__(self):super().__init__();self.parts=[];self.math=0
  def handle_starttag(self,t,a):
   if t=='math':self.math+=1;self.parts.append(dict(a).get('alttext',''))
   if t in ['p','div','section','h1','h2','h3','li']:self.parts.append('\n')
  def handle_endtag(self,t):
   if t=='math':self.math-=1
  def handle_data(self,s):
   if not self.math:self.parts.append(s)
 for n in ['mesh.html','mesh-abs.html']:
  s=Parser();s.feed((L/'sources'/n).read_text())
  (L/'sources'/n.replace('.html','.txt')).write_text(''.join(s.parts))
 for n in ['initial','exact']:
  j=json.loads((L/('history-'+n+'.json')).read_text())
  for h in j['hits']:
   matches=list(re.finditer(j['pattern'],h['body'],re.I))
   print(h['path'],[(m.group(),h['body'][max(0,m.start()-100):m.end()+220]) for m in matches])
elif sys.argv[1]=='context':
 out=[]
 for p in [R/'AGENTS.md',B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B/'NEXT.md']:
  b=p.read_bytes();out.append(dict(path=str(p),sha256=sha(b),bytes=len(b)))
  if p.suffix=='.json':
   j=json.loads(b)
   for k,v in j.items():
    print(k,json.dumps(v,ensure_ascii=False) if not isinstance(v,(list,dict)) else str(len(v))+' entries')
   if p.name=='ledger.json': print([(x.get('number'),x.get('title')) for x in j['accepted']])
 save('context-receipts.json',out)
elif sys.argv[1]=='scan':
 pattern=sys.argv[2];patt=re.compile(pattern.encode(),re.I)
 old=L.parent/'sol-fresh-source-discovery-r133/history-aliases.jsonl.gz'
 roles=re.compile(r'(?:^|/)(?:SUMMARY|discovery|PROOF|review|DECISION)[^/]*\.(?:md|txt)$',re.I)
 echoes=re.compile(r'/(?:extracted[^/]*|rebuild[^/]*|replay[^/]*|packet|inputs|evidence|history|review-core|core|source-copy|verification)/',re.I)
 paths={};rows=0
 with gzip.open(old,'rt') as f:
  for line in f:
   h,p=json.loads(line);rows+=1
   if roles.search(p) and not echoes.search(p):paths[p]=h
 inherited=len(paths)
 names=subprocess.check_output(['rg','--files',str(R),'-g','*.md','-g','*.txt'],text=True)
 for n in names.splitlines():
  p=str(Path(n).relative_to(R))
  if roles.search(p) and not echoes.search(p) and not str(L.relative_to(R)) in p:paths.setdefault(p,None)
 out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),pattern=pattern,index=str(old),index_sha256=sha(old.read_bytes()),alias_rows=rows,inherited=inherited,paths=len(paths),unchanged=0,changed=0,missing=[],oversize=[],hits=[],retained_r111_r113=[],global_cutoff=None,complete_bodies=True,role_regex=roles.pattern,echo_exclusion=echoes.pattern)
 seen=set()
 for p,h in sorted(paths.items()):
  try:
   f=R/p
   if f.stat().st_size>12000000:out['oversize'].append(p);continue
   b=f.read_bytes();hh=sha(b);out['unchanged' if hh==h else 'changed']+=1
   if re.search('r11[123]/',p):out['retained_r111_r113'].append([p,hh])
   if hh in seen:continue
   seen.add(hh)
   if patt.search(b):out['hits'].append(dict(path=p,sha256=hh,body=b.decode(errors='replace')))
  except OSError as e:out['missing'].append([p,str(e)])
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
  b=(B/n).read_bytes()
  if patt.search(b):out['hits'].append(dict(path=str(B/n),sha256=sha(b),body=b.decode()))
 out['unique_bodies']=len(seen)
 tag=sys.argv[3];save('history-'+tag+'.json',out)
 print({k:v for k,v in out.items() if k not in ['hits','retained_r111_r113']})
 for h in out['hits']:print(h['path'])
elif sys.argv[1]=='fetch':
 for arg in sys.argv[2:]:
  n,url=arg.split('=',1);r=dict(name=n,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
  try:
   with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source audit'}),timeout=35) as f:
    b=f.read(16000001);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=sha(b),capped=len(b)>16000000);(L/'sources'/n).write_bytes(b)
  except Exception as e:r['error']=str(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
  print(r)
