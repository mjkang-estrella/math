import sys,json,hashlib,re,gzip,datetime,urllib.request,subprocess
from pathlib import Path
L=Path(__file__).resolve().parent; B=L.parents[1]; R=B.parents[3]
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
if sys.argv[1]=='context':
 out={}
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md','AGENTS.md']:
  b=(B/n).read_bytes();(L/('context-'+n)).write_bytes(b);out[n]={'sha256':sha(b),'bytes':len(b)}
 save('context-receipt.json',out);print(out)
elif sys.argv[1]=='scan':
 pat=re.compile(sys.argv[2],re.I); roles=re.compile(r'(?:^|/)(?:SUMMARY|discovery|PROOF|review|DECISION)[^/]*\.(?:md|txt)$',re.I)
 echoes=re.compile(r'/(?:extracted[^/]*|rebuild[^/]*|replay[^/]*|packet|inputs|evidence|history|review-core|core|source-copy|verification)/',re.I)
 old=L.parent/'sol-fresh-source-discovery-r133/history-aliases.jsonl.gz'; known={}
 with gzip.open(old,'rt') as f:
  for line in f:
   h,p=json.loads(line)
   if roles.search(p) and not echoes.search(p):known[p]=h
 retained=L.parent/'sol-fresh-source-discovery-r146/history-initial.json'
 for h,ps in json.loads(retained.read_bytes())['aliases'].items():
  for p in ps:
   if roles.search(p) and not echoes.search(p):known[p]=h
 for d in (B/'lanes').iterdir():
  if not d.is_dir() or d==L or d.name in ['sol-fresh-source-discovery-r147','sol-fresh-source-discovery-r148']:continue
  for f in d.iterdir():
   if f.is_file() and roles.search(f.name):known.setdefault(str(f.relative_to(R)),None)
 out=dict(pattern=pat.pattern,retained=[str(old),str(retained)],aliases={},hits=[],missing=[],changed=[],unchanged=0,r111_r113=[],full_bodies=True,cutoff=None,limits='Retained qualified role indexes; immediate new batch originals refreshed; active r147/r148 excluded. Lexical screen only.')
 seen=set()
 for p,h in sorted(known.items()):
  f=R/p
  if not f.is_file():out['missing'].append(p);continue
  b=f.read_bytes();hh=sha(b);out['aliases'].setdefault(hh,[]).append(p)
  if hh!=h:out['changed'].append(p)
  else:out['unchanged']+=1
  if re.search(r'r11[123]/',p):out['r111_r113'].append([p,hh])
  if hh in seen:continue
  seen.add(hh)
  if pat.search(b.decode(errors='replace')):
   dest=L/'reopened'/sys.argv[3]/str(len(out['hits']));dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
   out['hits'].append(dict(path=p,sha256=hh,copy=str(dest.relative_to(L))))
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
  b=(L/('context-'+n)).read_bytes()
  if pat.search(b.decode()):out['hits'].append(dict(path='context-'+n,sha256=sha(b)))
 save('history-'+sys.argv[3]+'.json',out);print(len(seen),'bodies',len(out['changed']),'changed',len(out['hits']),'hits');print(out['hits'] if len(out['hits'])<20 else 'All hits retained in JSON')
elif sys.argv[1]=='fetch':
 (L/'sources').mkdir(exist_ok=True)
 for arg in sys.argv[2:]:
  n,url=arg.split('=',1);r=dict(name=n,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
  try:
   with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source audit'}),timeout=30) as f:
    b=f.read(12000001)
    if len(b)>12000000:raise ValueError('12MB cap')
    (L/'sources'/n).write_bytes(b);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=sha(b))
  except Exception as e:r['error']=str(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
  print(r)
elif sys.argv[1]=='text':
 for n in sys.argv[2:]:
  q=subprocess.run(['pdftotext','-layout',str(L/'sources'/n),str(L/'sources'/n.replace('.pdf','.txt'))],capture_output=True);print(n,q.returncode,q.stderr.decode())
elif sys.argv[1]=='registry':
 pat=re.compile(r'Kaneko|leaf.?distance|leaf.?degree|Erbes|Mousley',re.I);out=[]
 for name in ['omega-tree.txt.gz','openai-tree.txt.gz']:
  p=L.parent/'root-edge-irregulator-final-freeze-r1'/name;h=hashlib.sha256();hits=[];count=0
  with gzip.open(p,'rb') as f:
   for line in f:
    h.update(line);count+=1
    if pat.search(line.decode(errors='replace')):hits.append(line.decode().strip())
  out.append(dict(path=str(p),uncompressed_sha256=h.hexdigest(),lines=count,hits=hits))
 for lane,n in [('sol-fresh-source-discovery-r145','registry-screen.json'),('sol-fresh-source-discovery-r146','registry-delta-receipt.json')]:
  p=L.parent/lane/n;out.append(dict(path=str(p),sha256=sha(p.read_bytes()),receipt=json.loads(p.read_bytes())))
 save('registry-screen.json',out);print(json.dumps(out[:2],indent=2))
elif sys.argv[1]=='deltas':
 pat=re.compile(r'Kaneko|leaf.?distance|leaf.?degree|Erbes|Mousley',re.I);out=[]
 for lane,n in [('sol-fresh-source-discovery-r138','sources/omega-compare.json'),('sol-fresh-source-discovery-r141','sources/omega-fixed-delta.json')]:
  p=L.parent/lane/n;j=json.loads(p.read_bytes());out.append(dict(path=str(p),sha256=sha(p.read_bytes()),base=j['base_commit']['sha'],merge_base=j['merge_base_commit']['sha'],total_commits=j['total_commits'],commits=len(j['commits']),files=len(j['files']),capped=len(j['files'])==300,hits=[x['filename'] for x in j['files'] if pat.search(json.dumps(x))]))
 save('registry-deltas.json',dict(omega='490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c',openai='7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a',intervals=out,semantic_clearance=False));print(out)
