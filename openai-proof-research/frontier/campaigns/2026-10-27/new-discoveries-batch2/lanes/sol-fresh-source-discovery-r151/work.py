import sys,json,hashlib,datetime,urllib.request,re,os,subprocess
from pathlib import Path
L=Path(__file__).resolve().parent; B=L.parents[1]; R=L.parents[5]
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
mode=sys.argv[1]
if mode=='history':
 known={}
 for lane,name in [('r147','history-receipt.json'),('r145','history-exact.json'),('r148','history-initial.json')]:
  p=L.parent/('sol-fresh-source-discovery-'+lane)/name;j=json.loads(p.read_bytes())
  if 'records' in j:known.update({p:h for p,h,z in j['records']})
  elif 'aliases' in j:known.update({p:h for h,ps in j['aliases'].items() for p in ps})
  else:known.update({p:h for p,h in j.get('retained_r111_r113',[])})
 paths=set(known)
 for lane in (B/'lanes').iterdir():
  if lane==L or not lane.is_dir():continue
  for p in lane.iterdir():
   if p.is_file() and p.name.lower() in {'summary.md','discovery.md','proof.md','review.md','decision.md'}:paths.add(str(p.relative_to(R)))
 records=[];changed=[];missing=[]
 for p in sorted(paths):
  f=R/p
  if not f.is_file():missing.append(p);continue
  b=f.read_bytes();h=sha(b);records.append([p,h,len(b)])
  if known.get(p)!=h:changed.append(p)
 save('history-receipt.json',dict(utc=now(),records=records,changed=changed,missing=missing,cutoff=None,scope='Union qualified r147/r145/r148 original body indexes plus immediate new batch original roles; no generated echo discovery; no global completeness claim'))
 print('records',len(records),'changed',changed,'missing',missing)
elif mode=='alias':
 j=json.loads((L/'history-receipt.json').read_bytes());pat=re.compile(sys.argv[2],re.I);hits=[]
 for p,h,z in j['records']:
  b=(R/p).read_bytes();assert sha(b)==h,(p,'changed since refresh')
  if pat.search(b.decode(errors='replace')):
   dst='reopened/'+sha(b)+'.txt';(L/'reopened').mkdir(exist_ok=True);(L/dst).write_bytes(b);hits.append(dict(path=p,sha256=h,copy=dst))
 rec=dict(utc=now(),pattern=pat.pattern,hits=hits,bodies=len(j['records']),full_bodies=True)
 with (L/'alias-queries.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(json.dumps(rec))
elif mode=='fetch':
 for arg in sys.argv[2:]:
  name,url=arg.split('=',1);r=dict(utc=now(),name=name,url=url)
  try:
   with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'mathematical-source-research/1.0'}),timeout=25) as f:
    b=f.read(12000001);assert len(b)<=12000000
    (L/'sources'/name).write_bytes(b);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=sha(b))
  except Exception as e:r['error']=str(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
  print(r)
elif mode=='text':
 for n in sys.argv[2:]:
  p=subprocess.run(['pdftotext','-layout',str(L/'sources'/n),str(L/'sources'/n.replace('.pdf','.txt'))],capture_output=True);print(n,p.returncode,p.stderr.decode())
elif mode=='registry':
 pat=re.compile('curvature|schuhmacher|wannerer|viakhirev|stieltjes|single.peak',re.I);out=[]
 for n in ['omega-library-tree.json','omega-problems-tree.json','omega-docs-tree.json']:
  p=L.parent/'sol-fresh-source-discovery-r143/sources'/n;j=json.loads(p.read_bytes())
  out.append(dict(path=str(p),sha256=sha(p.read_bytes()),truncated=j.get('truncated'),hits=[x for x in j['tree'] if pat.search(x['path'])]))
 save('registry-path-screen.json',out);print(json.dumps(out,indent=2))
elif mode=='baseline':
 import gzip
 out=[];pat=re.compile(rb'curvature|schuhmacher|wannerer|viakhirev|stieltjes|single.peak',re.I)
 for n in ['omega-tree.txt.gz','openai-tree.txt.gz']:
  p=L.parent/'root-edge-irregulator-final-freeze-r1'/n;hh=hashlib.sha256();hits=[]
  with gzip.open(p,'rb') as f:
   for b in f:
    hh.update(b)
    if pat.search(b):hits.append(b.decode().strip())
  out.append(dict(path=str(p),uncompressed_sha256=hh.hexdigest(),hits=hits))
 save('baseline-target-paths.json',out);print(json.dumps(out,indent=2))
elif mode=='context':
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
  b=(B/n).read_bytes();(L/('context-'+n)).write_bytes(b)
  if n.endswith('.json'):
   j=json.loads(b);print(n,list(j),[(a.get('number'),a.get('title')) for a in j.get('accepted',[])])
  else:print(b.decode())
