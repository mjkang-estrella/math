import sys,json,re,hashlib,datetime,urllib.request,urllib.parse,urllib.error,subprocess,os,xml.etree.ElementTree as ET
from pathlib import Path
L=Path(__file__).resolve().parent; R=L.parents[5]; B=L.parents[1]
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
mode=sys.argv[1]
if mode=='init':
 known={};bases=[]
 for k in [185,186,187,188]:
  p=L.parent/f'sol-fresh-source-discovery-r{k}/history-receipt.json'; b=p.read_bytes(); bases.append([str(p),sha(b)]);known.update({r[0]:r[1:] for r in json.loads(b)['records']})
 paths=set(known)
 # Refresh actual campaign decision records, pruning generated/frozen copies.
 prune={'inputs','originals','frozen','private','packet','source','sources','verification','verification-fresh','verification-final','extracted','node_modules','.git','.lake','fresh-replay','replay','evidence','consulted'}
 names={'summary.md','discovery.md','proof.md','review.md','decision.md'}
 for root,ds,fs in os.walk(R/'frontier/campaigns'):
  ds[:]=[d for d in ds if d not in prune and not d.startswith(('verification-','extracted-'))]
  if Path(root)==L:ds[:]=[];continue
  for n in fs:
   if n.lower() in names:paths.add(str((Path(root)/n).relative_to(R)))
 rows=[];changed=[];copies=[]
 (L/'originals').mkdir(exist_ok=True)
 for p in sorted(paths):
  f=R/p
  if not f.is_file():continue
  b=f.read_bytes(); h=sha(b); row=[p,h,len(b)]; rows.append(row)
  if known.get(p)!=row[1:]:changed.append(row)
  c='originals/'+sha(p.encode())[:16]+'-'+f.name;(L/c).write_bytes(b)
  assert sha(f.read_bytes())==sha((L/c).read_bytes())==h
  copies.append([p,c,h,len(b)])
 for k in [185,186,187]:
  p=L.parent/f'sol-fresh-source-discovery-r{k}/history-receipt.json';c=f'history-r{k}.json';b=p.read_bytes();(L/c).write_bytes(b);copies.append([str(p.relative_to(R)),c,sha(b),len(b)])
 for n in ['NEXT.md','ledger.json','prior-campaign-context.json','AGENTS.md']:(L/('context-'+n)).write_bytes((B/n).read_bytes())
 (L/'context-ancestor-AGENTS.md').write_bytes((R/'AGENTS.md').read_bytes())
 save('history-receipt.json',dict(utc=now(),bases=bases,records=rows,changed=changed,missing=sorted(paths-set(r[0] for r in rows)),policy='Inherited qualified originals plus all-campaign original decision refresh; prune generated copies on new discovery only.'))
 save('original-copy-provenance.json',copies)
 save('initial-verification.json',dict(utc=now(),pairs=len(copies),pass_all=True,retained_r111_113={str(k):sum(f'r{k}/' in r[0] for r in rows) for k in [111,112,113]}))
 print('records',len(rows),'changed',len(changed)); print('\n'.join(p for p,h,z in changed))
elif mode=='screen':
 pat=re.compile(sys.argv[2],re.I); hits=[]
 for p,c,h,z in json.loads((L/'original-copy-provenance.json').read_text()):
  if not p.lower().endswith('.md'):continue
  s=(L/c).read_text(errors='replace');ms=list(pat.finditer(s))
  if ms:hits.append(dict(path=p,sha256=h,excerpts=[s[max(0,m.start()-100):m.end()+200] for m in ms[:4]]))
 save(sys.argv[3],dict(utc=now(),pattern=pat.pattern,hits=hits)); print(json.dumps(hits)[:20000])
elif mode in ['fetch','search']:
 (L/'sources').mkdir(exist_ok=True)
 for arg in sys.argv[2:]:
  if mode=='fetch':n,u=arg.split('=',1)
  else:n='search-'+sha(arg.encode())[:12]+'.xml';u='https://www.bing.com/search?format=rss&q='+urllib.parse.quote(arg)
  rec=dict(utc=now(),url=u,name=n,query=arg if mode=='search' else None)
  try:
   assert not any(s in u.lower() for s in ['github','codeload','sciencedirect','google.'])
   with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Mathematical-source-research/1.0'}),timeout=25) as f:
    b=f.read(12000001);assert len(b)<=12000000;(L/'sources'/n).write_bytes(b);rec.update(status=f.status,final_url=f.url,sha256=sha(b),bytes=len(b))
   if mode=='search':rec['results']=[dict(title=x.findtext('title'),url=x.findtext('link'),description=x.findtext('description')) for x in ET.fromstring(b).findall('.//item')]
  except Exception as e:
   rec['error']=str(e)
   if isinstance(e,urllib.error.HTTPError):
    b=e.read(1000000);(L/'sources'/(n+'.error')).write_bytes(b);rec['error_body_sha256']=sha(b)
  with (L/('http.jsonl' if mode=='fetch' else 'search.jsonl')).open('a') as f:f.write(json.dumps(rec)+'\n')
  print(json.dumps(rec))
elif mode=='text':
 for n in sys.argv[2:]:subprocess.run(['pdftotext','-layout',str(L/'sources'/n),str(L/'sources'/(n+'.txt'))],check=True)
