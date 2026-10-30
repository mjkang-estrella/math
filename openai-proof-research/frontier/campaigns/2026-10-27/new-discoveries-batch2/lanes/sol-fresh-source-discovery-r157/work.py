import sys,json,hashlib,datetime,re,urllib.request,subprocess,gzip
from pathlib import Path
L=Path(__file__).resolve().parent; B=L.parents[1]; R=L.parents[5]
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
mode=sys.argv[1]
if mode=='init':
 (L/'sources').mkdir(exist_ok=True)
 base=L.parent/'sol-fresh-source-discovery-r151/history-receipt.json'; j=json.loads(base.read_bytes()); known={p:h for p,h,z in j['records']}; paths=set(known)
 for lane in (B/'lanes').iterdir():
  if lane==L or not lane.is_dir():continue
  for p in lane.iterdir():
   if p.is_file() and p.name.lower() in {'summary.md','discovery.md','proof.md','review.md','decision.md'}:paths.add(str(p.relative_to(R)))
 records=[]; changed=[];missing=[]
 for p in sorted(paths):
  f=R/p
  if not f.is_file():missing.append(p);continue
  b=f.read_bytes();h=sha(b);records.append([p,h,len(b)])
  if known.get(p)!=h:changed.append([p,h,len(b)])
 save('history-receipt.json',dict(utc=now(),base=str(base.relative_to(R)),base_sha256=sha(base.read_bytes()),records=records,changed=changed,missing=missing,role_policy='Reuse qualified r151/r148 indexes; add immediate original scientific roles only; preserve original r111-r113. No lane-wide exclusion.'))
 print('original records',len(records),'changed',len(changed),'missing',len(missing))
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
  b=(B/n).read_bytes();(L/('context-'+n)).write_bytes(b)
  if n.endswith('.json'):
   j=json.loads(b); print(n, list(j)); print(json.dumps(j if n=='ledger.json' else {k:v for k,v in j.items() if k not in ['accepted','published_papers']},ensure_ascii=False))
  else:
   # Read the entire context, emit paragraphs individually in context-reading.txt for bounded subsequent reading.
   (L/'context-reading.txt').write_text(b.decode())
elif mode=='alias':
 j=json.loads((L/'history-receipt.json').read_bytes());pat=re.compile(sys.argv[2],re.I);hits=[]
 for p,h,z in j['records']:
  b=(R/p).read_bytes()
  if sha(b)!=h:raise RuntimeError('changed original '+p)
  if pat.search(b.decode(errors='replace')):
   (L/'reopened').mkdir(exist_ok=True);n='reopened/'+sha(b)+'.txt';(L/n).write_bytes(b);hits.append(dict(path=p,copy=n,sha256=h))
 out=dict(utc=now(),pattern=pat.pattern,full_original_bodies=len(j['records']),hits=hits)
 with (L/'alias-queries.jsonl').open('a') as f:f.write(json.dumps(out)+'\n')
 print(json.dumps(out,indent=2))
elif mode=='fetch':
 for arg in sys.argv[2:]:
  name,url=arg.split('=',1);r=dict(utc=now(),name=name,url=url)
  try:
   with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'mathematical-source-research/1.0'}),timeout=30) as f:
    b=f.read(12000001);assert len(b)<=12000000;(L/'sources'/name).write_bytes(b);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=sha(b))
  except Exception as e:r['error']=str(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
  print(r)
elif mode=='text':
 for n in sys.argv[2:]:
  p=subprocess.run(['pdftotext','-layout',str(L/'sources'/n),str(L/'sources'/n.replace('.pdf','.txt'))],capture_output=True);print(n,p.returncode,p.stderr.decode())
elif mode=='delta':
 for n in ['omega-delta.json','openai-delta.json']:
  j=json.loads((L/'sources'/n).read_bytes());files=j.get('files',[])
  print(n,j.get('status'),'ahead',j.get('ahead_by'),'commits',len(j.get('commits',[])),'files',len(files),'CAPPED',len(files)>=300)
  print('\n'.join(x['filename'] for x in files if re.search('black|curvature|schwarz|monotonic|entropy|measure',x['filename'],re.I)))
