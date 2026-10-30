import sys,json,hashlib,datetime,urllib.request,re,os
from pathlib import Path
L=Path(__file__).resolve().parent;B=L.parents[1];R=L.parents[5]
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
(L/'sources').mkdir(exist_ok=True)
mode=sys.argv[1]
if mode=='history':
 old=L.parent/'sol-fresh-source-discovery-r147/history-receipt.json';j=json.loads(old.read_bytes());known={p:h for p,h,z in j['records']};paths=set(known)
 roles={'summary.md','discovery.md','proof.md','review.md','decision.md'}
 skip={'.git','.lake','node_modules','__pycache__','extracted','copy','fresh','replay','history','inputs','evidence','build','vendor','dist','.venv','payload','private','context'}
 for root,ds,fs in os.walk(R):
  ds[:]=[d for d in ds if d not in skip and Path(root)/d!=L]
  for n in fs:
   if n.lower() in roles:paths.add(str((Path(root)/n).relative_to(R)))
 omitted=[p for p in paths if any(x in p for x in ['/build/','/replays/','output/release/','output/submissions/'])]
 paths.difference_update(omitted)
 records=[];changed=[]
 for p in sorted(paths):
  f=R/p
  if not f.exists():continue
  b=f.read_bytes();h=sha(b);records.append([p,h,len(b)])
  if known.get(p)!=h:changed.append(p)
 save('history-receipt.json',dict(utc=now(),baseline=str(old),baseline_sha256=sha(old.read_bytes()),records=records,changed=changed,omitted_echo_roles=sorted(omitted),cutoff=None,scope='retained qualified original roles, refresh new/changed; original r111-r113 retained; not a whole inventory rebuild'))
 print('records',len(records),'changed',changed)
elif mode=='alias':
 j=json.loads((L/'history-receipt.json').read_bytes());pat=re.compile(sys.argv[2],re.I);hits=[]
 for p,h,z in j['records']:
  b=(R/p).read_bytes()
  if pat.search(b.decode(errors='replace')):
   hits.append(p);(L/'sources'/('history-'+sha(b)+'.txt')).write_bytes(b)
 rec=dict(utc=now(),pattern=pat.pattern,hits=hits,bodies=len(j['records']),cutoff=None)
 with (L/'alias-queries.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(rec)
elif mode=='fetch':
 for arg in sys.argv[2:]:
  name,url=arg.split('=',1);rec=dict(utc=now(),name=name,url=url)
  try:
   with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-audit/1.0'}),timeout=30) as f:
    b=f.read(12000001)
    if len(b)>12000000:raise ValueError('12MB cap')
    (L/'sources'/name).write_bytes(b);rec.update(status=f.status,final_url=f.url,sha256=sha(b),bytes=len(b))
  except Exception as e:rec['error']=str(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
  print(rec)
elif mode=='context':
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
  b=(B/n).read_bytes();(L/('context-'+n)).write_bytes(b)
  if n.endswith('.json'):
   j=json.loads(b);print(n,[(a.get('number'),a.get('title')) for a in j.get('accepted',[])])
  else: print(b.decode()[:24000])
