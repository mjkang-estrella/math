import os,sys,json,hashlib,re,datetime,urllib.request
from pathlib import Path
L=Path(__file__).resolve().parent; R=L.parents[5]; B=L.parents[1]
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,x):(L/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
(L/'sources').mkdir(exist_ok=True)
if sys.argv[1]=='history':
 base=L.parent/'sol-fresh-source-discovery-r157/history-receipt.json'
 known={p:h for p,h,z in json.loads(base.read_bytes())['records']}
 for lane in ['r158','r161']:
  p=L.parent/('sol-fresh-source-discovery-'+lane)/'history-delta.json'
  for f,h,z in json.loads(p.read_bytes())['changed_or_new']:known[f]=h
 p=L.parent/'sol-fresh-source-discovery-r159/history-receipt.json'
 j=json.loads(p.read_bytes())
 if 'records' in j:
  for f,h,z in j['records']:known[f]=h
 skip={'.git','.lake','node_modules','__pycache__','extracted','copy','fresh','replay','history','inputs','evidence','build','vendor','dist','.venv','payload','private','context','core','reopened','sources','output','replays','frozen'}
 paths=set(known)
 for root,ds,fs in os.walk(R):
  ds[:]=[d for d in ds if d not in skip and Path(root)/d!=L and not d.startswith(('extracted-replay','extracted-attempt','frozen-copy'))]
  for n in fs:
   if n.lower() in {'summary.md','discovery.md','proof.md','review.md','decision.md'}:paths.add(str((Path(root)/n).relative_to(R)))
 records=[];changed=[];hits=[];pat=re.compile(sys.argv[2],re.I)
 for p in sorted(paths):
  if any(x in skip or x.startswith(('extracted-replay','extracted-attempt','frozen-copy')) for x in p.split('/')):continue
  f=R/p
  if not f.exists():continue
  b=f.read_bytes();h=sha(b);records.append([p,h,len(b)])
  if known.get(p)!=h:changed.append([p,h,len(b)])
  s=re.sub(r'\b[0-9a-f]{40,64}\b','',b.decode(errors='replace'))
  if pat.search(s):
   hits.append(dict(path=p,sha256=h,bytes=len(b)));(L/'sources'/('history-'+h+'.txt')).write_bytes(b)
 save('history-delta.json',dict(utc=now(),changed_or_new=changed,baseline_sha256=sha(base.read_bytes()),cutoff=None))
 save('history-receipt.json',dict(utc=now(),records=records,pattern=pat.pattern,hits=hits,full_body_count=len(records),qualification='Full original roles inherited from qualified r157/r158/r159/r161; generated copies excluded by role; no global semantic clearance'))
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
  b=(B/n).read_bytes();(L/('context-'+n)).write_bytes(b)
  if n.endswith('.json'):
   j=json.loads(b); print(n,'top keys',list(j),'bytes',len(b))
 print('body_count',len(records),'changed',len(changed),'hits',hits)
elif sys.argv[1]=='audit':
 j=json.loads((L/'history-receipt.json').read_bytes());pat=re.compile(r'2402[.]14163|\b[ŠS]irola\b|Širola|Dumas.Eisenstein|2511[.]21427|\bGarg\b|A generalized Dumas irreducibility criterion|2502[.]06032|\bGatzweiler\b|\bKrattenthaler\b',re.I);hits=[]
 for p,h,z in j['records']:
  b=(R/p).read_bytes();s=re.sub(r'\b[0-9a-f]{40,64}\b','',b.decode(errors='replace'))
  if pat.search(s):
   hits.append(dict(path=p,sha256=sha(b),bytes=len(b)));(L/'sources'/('history-'+sha(b)+'.txt')).write_bytes(b)
 save('alias-audit.json',dict(utc=now(),pattern=pat.pattern,hits=hits,body_count=len(j['records'])))
 print('alias hits',[(x['path'],x['bytes']) for x in hits])
 for n in ['ledger.json','prior-campaign-context.json']:
  j=json.loads((L/('context-'+n)).read_bytes());print(n, {k:j[k] for k in ['accepted_count','total_accepted_count','next_global_outcome_number'] if k in j})
  for k in ['accepted','excluded','candidates','held_candidates']:
   a=j.get(k,[]);print(k,len(a),[(x.get('number',x.get('id')),x.get('title',x.get('proposed_result',''))[:100]) for x in a] if k=='accepted' else 'all parsed; exact target search below')
  print('exact source aliases present?',bool(pat.search(re.sub(r'\b[0-9a-f]{40,64}\b','',json.dumps(j,ensure_ascii=False)))))
 j=json.loads((L/'sources/omega-delta.json').read_bytes());fs=j.get('files',[])
 save('registry-delta-audit.json',dict(utc=now(),files=len(fs),capped=len(fs)>=300,total_commits=j.get('total_commits'),changed_paths=[x['filename'] for x in fs],target_hits=[x['filename'] for x in fs if pat.search(x['filename'])],gaps=['two older300-path caps remain']))
 print('current delta',len(fs),'files',j.get('total_commits'),'commits','target hits',[x['filename'] for x in fs if pat.search(x['filename'])])
elif sys.argv[1]=='registry':
 import gzip
 pat=re.compile(r'Dumas|Eisenstein|Sirola|Širola|14163',re.I);records=[]
 for rel in ['root-edge-irregulator-final-freeze-r1/omega-tree.txt.gz','root-edge-irregulator-final-freeze-r1/openai-tree.txt.gz','sol-fresh-source-discovery-r148/sources/omega-problems-fixed.json','sol-fresh-source-discovery-r138/sources/omega-compare.json','sol-fresh-source-discovery-r141/registry-delta.json','sol-fresh-source-discovery-r157/sources/omega-delta.json','sol-fresh-source-discovery-r157/sources/openai-delta.json']:
  p=L.parent/rel;b=p.read_bytes();s=gzip.decompress(b).decode() if p.suffix=='.gz' else b.decode()
  if p.suffix=='.gz':paths=[x.split('\t')[-1] for x in s.splitlines()]
  else:
   j=json.loads(s);paths=[x.get('path',x.get('filename','')) for x in j.get('tree',j.get('files',[]))] if isinstance(j,dict) else []
  records.append(dict(path=str(p),sha256=sha(b),hits=[x for x in paths if pat.search(re.sub(r'\b[0-9a-f]{40,64}\b','',x))]))
 for n in ['omega','openai']:
  j=json.loads((L/'sources'/f'{n}-head.json').read_bytes());records.append(dict(name=n,head=j['sha']))
 save('registry-screen.json',dict(utc=now(),records=records,gaps=['aa026->a19a capped300','a19a->490f capped300','Lexical coverage only, no worldwide absence. Current head comparison against r157/r159/r161 required.']))
 print([(r.get('name',r.get('path')),len(r.get('hits',[])),r.get('head')) for r in records])
elif sys.argv[1]=='fetch':
 for arg in sys.argv[2:]:
  n,u=arg.split('=',1);rec=dict(utc=now(),url=u,name=n)
  try:
   with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'research-source-audit/1.0'}),timeout=30) as f:
    b=f.read(12000001)
    if len(b)>12000000:raise ValueError('12MB cap')
    (L/'sources'/n).write_bytes(b);rec.update(status=f.status,final_url=f.url,bytes=len(b),sha256=sha(b))
  except Exception as e:rec['error']=str(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
  print(rec)
