import sys,json,hashlib,datetime,urllib.request,re,subprocess
from pathlib import Path
L=Path(__file__).resolve().parent; B=L.parents[1]; R=L.parents[5]
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
mode=sys.argv[1]
if mode=='init':
 (L/'sources').mkdir(exist_ok=True)
 base=L.parent/'sol-fresh-source-discovery-r151/history-receipt.json';j=json.loads(base.read_bytes());known={p:h for p,h,z in j['records']};paths=set(known)
 for lane in (B/'lanes').iterdir():
  if lane==L or not lane.is_dir():continue
  for p in lane.iterdir():
   if p.is_file() and p.name.lower() in {'summary.md','discovery.md','proof.md','review.md','decision.md'}:paths.add(str(p.relative_to(R)))
 changed=[];missing=[]
 for p in sorted(paths):
  f=R/p
  if not f.is_file():missing.append(p);continue
  b=f.read_bytes();h=sha(b)
  if known.get(p)!=h:changed.append([p,h,len(b)])
 save('history-delta.json',dict(utc=now(),base=str(base.relative_to(R)),base_sha256=sha(base.read_bytes()),changed=changed,missing=missing,scope='Qualified r151 union of r148/r147/r145 plus new immediate original batch roles. No generated echoes added. Original r111-r113 retained. No global cutoff.'))
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
  b=(B/n).read_bytes();(L/('context-'+n)).write_bytes(b)
  if n.endswith('.json'):
   j=json.loads(b);print(n,list(j));print([(a.get('number'),a.get('title')) for a in j.get('accepted',[])])
  else: print(b.decode()[:14000])
 print('delta',changed,'missing',missing)
elif mode=='alias':
 d=json.loads((L/'history-delta.json').read_bytes());base=R/d['base'];assert sha(base.read_bytes())==d['base_sha256'];rec={p:h for p,h,z in json.loads(base.read_bytes())['records']};rec.update({p:h for p,h,z in d['changed']});pat=re.compile(sys.argv[2],re.I);hits=[]
 for p,h in rec.items():
  if p in d['missing']:continue
  b=(R/p).read_bytes()
  if sha(b)!=h:raise RuntimeError('original changed: '+p)
  if pat.search(b.decode(errors='replace')):
   (L/'reopened').mkdir(exist_ok=True);name='reopened/'+sha(b)+'.txt';(L/name).write_bytes(b);hits.append(dict(path=p,sha256=h,copy=name))
 out=dict(utc=now(),pattern=pat.pattern,full_original_bodies=len(rec),hits=hits)
 with (L/'alias-queries.jsonl').open('a') as f:f.write(json.dumps(out)+'\n')
 print(json.dumps(out,indent=2))
elif mode=='fetch':
 for arg in sys.argv[2:]:
  name,url=arg.split('=',1);r=dict(utc=now(),name=name,url=url)
  try:
   with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'mathematical-source-research/1.0'}),timeout=25) as f:
    b=f.read(12000001);assert len(b)<=12000000;(L/'sources'/name).write_bytes(b);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=sha(b))
  except Exception as e:r['error']=str(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
  print(r)
elif mode=='text':
 for n in sys.argv[2:]:
  p=subprocess.run(['pdftotext','-layout',str(L/'sources'/n),str(L/'sources'/n.replace('.pdf','.txt'))],capture_output=True);print(n,p.returncode,p.stderr.decode())
elif mode=='registry':
 import gzip
 pat=re.compile(rb'bernoulli|milojev|sudakov|samuels|manickam|leakage|first.proof|small.deviation',re.I);out=[]
 for n in ['omega-tree.txt.gz','openai-tree.txt.gz']:
  p=L.parent/'root-edge-irregulator-final-freeze-r1'/n;hh=hashlib.sha256();hits=[]
  with gzip.open(p,'rb') as f:
   for b in f:
    hh.update(b)
    if pat.search(b):hits.append(b.decode().strip())
  out.append(dict(path=str(p.relative_to(R)),compressed_sha256=sha(p.read_bytes()),uncompressed_sha256=hh.hexdigest(),hits=hits))
 save('registry-paths.json',out);print(json.dumps(out,indent=2))
elif mode=='links':
 p=subprocess.run(['pdftohtml','-stdout','-i',str(L/'sources/report.pdf')],capture_output=True);assert p.returncode==0,p.stderr
 (L/'sources/report-links.html').write_bytes(p.stdout)
 print('\n'.join(x for x in p.stdout.decode().splitlines() if '3A' in x or 'href=' in x and 'submission-3' in x))
elif mode=='scoped':
 pat=re.compile('bernoulli|milojev|sudakov|samuels|manickam|exceeds|first.proof|nonnegative.*sum',re.I);out=[]
 root=json.loads((L/'sources/omega-root.json').read_bytes())
 for n,prefix in [('omega-library-tree.json','Library'),('omega-problems-tree.json','Problems'),('omega-docs-tree.json','docs')]:
  p=L.parent/'sol-fresh-source-discovery-r143/sources'/n;j=json.loads(p.read_bytes());treeid=next(x['sha'] for x in root['tree'] if x['path']==prefix);assert treeid==j['sha'];assert not j.get('truncated')
  out.append(dict(path=str(p.relative_to(R)),sha256=sha(p.read_bytes()),tree=treeid,scope=prefix,hits=[x for x in j['tree'] if pat.search(x['path'])]))
 save('registry-scoped.json',out);print(json.dumps(out,indent=2))
elif mode=='firstproof':
 j=json.loads((L/'sources/firstproof-head.json').read_bytes());t=json.loads((L/'sources/firstproof-tree.json').read_bytes());assert t['sha']==j['sha'];assert not t['truncated'];print(j['sha'],j['commit']['committer']['date']);print('\n'.join(x['path'] for x in t['tree'] if ('problem-03' in x['path'] and x['path'].endswith(('.pdf','.md','.tex'))) or 'submission-3A' in x['path']))
