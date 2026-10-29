import sys,json,hashlib,datetime,urllib.request,re,os
from pathlib import Path
L=Path(__file__).resolve().parent
R=L.parents[5]
def sha(b): return hashlib.sha256(b).hexdigest()
def save(n,o): (L/n).write_text(json.dumps(o,indent=2)+'\n')
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
mode=sys.argv[1]
if mode=='history':
 old=L.parent/'sol-fresh-source-discovery-r137/history-receipt.json'
 j=json.loads(old.read_bytes()); paths={p for ps in j['aliases'].values() for p in ps}
 roles={'summary.md','discovery.md','proof.md','review.md','decision.md'}
 skip={'.git','.lake','node_modules','__pycache__','extracted','copy','fresh','replay','history','inputs','evidence','build','vendor','dist','.venv'}
 for root,ds,fs in os.walk(R):
  ds[:]=[d for d in ds if d not in skip and Path(root)/d!=L]
  for n in fs:
   if n.lower() in roles: paths.add(str((Path(root)/n).relative_to(R)))
 patterns={
 'partition':r'Heffernan|0093[.]39[.]41|genesis of a conjecture|partition.{0,60}factorial|p\(n\).{0,30}divides',
 'CN':r'CN-spectrum|CN.energy|CN-hyperenergetic',
 'transversal':r'common transversal probability|jgth-2024-0030',
 }
 records=[];hits={k:[] for k in patterns}; missing=[];changed=[]
 known={p:h for h,ps in j['aliases'].items() for p in ps}
 for p in sorted(paths):
  f=R/p
  if not f.exists(): missing.append(p);continue
  b=f.read_bytes();h=sha(b);records.append([p,h,len(b)])
  if known.get(p)!=h:changed.append(p)
  for k,v in patterns.items():
   ms=list(re.finditer(v.encode(),b,re.I))
   if ms:
    hits[k].append({'path':p,'sha256':h,'matches':[m.group().decode(errors='replace') for m in ms]})
    # Lossless matched originals, not snippets, available for reopening.
    (L/'sources'/('history-'+h+'.txt')).write_bytes(b)
 save('history-receipt.json',dict(utc=now(),baseline=str(old),baseline_sha256=sha(old.read_bytes()),records=records,changed=changed,missing=missing,patterns=patterns,hits=hits,full_bodies=True,cutoff=None,limits='Named original report roles, retained r137 aliases plus refreshed originals; not arbitrary source/code coverage.'))
 print({k:[x['path'] for x in v] for k,v in hits.items()});print('bodies',len(records),'changed',len(changed))
elif mode=='fetch':
 for arg in sys.argv[2:]:
  name,url=arg.split('=',1);rec=dict(name=name,url=url,utc=now())
  try:
   with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-audit/1.0'}),timeout=35) as f:
    b=f.read(12000001)
    if len(b)>12000000: raise ValueError('body exceeds fixed 12MB cap')
    rec.update(status=f.status,final_url=f.url,sha256=sha(b),bytes=len(b));(L/'sources'/name).write_bytes(b)
  except Exception as e:rec['error']=str(e)
  with (L/'http.jsonl').open('a') as out:out.write(json.dumps(rec)+'\n')
  print(rec)
elif mode=='context':
 out=[]
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
  p=L.parents[1]/n;b=p.read_bytes();out.append(dict(path=str(p),sha256=sha(b),bytes=len(b),mutable=n=='NEXT.md'))
  if n.endswith('.json'):
   j=json.loads(b); print(n,[(a.get('number'),a.get('title')) for a in j['accepted']])
   save('context-'+n,j)
  else:
   (L/'context-NEXT.md').write_bytes(b)
   print('NEXT fully retained, lines',len(b.splitlines()))
 save('context-receipts.json',out)
elif mode=='supplement':
 j=json.loads((L/'history-receipt.json').read_bytes());p=re.compile(rb'A046668|A192885|Heffernan|0093[.]39[.]41|genesis of a conjecture|Cilleruelo|CLPofpofnAA|multiplicative properties of the partition function|BF02837831',re.I);hits=[]
 for name,h,size in j['records']:
  b=(R/name).read_bytes()
  if p.search(b):hits.append(dict(path=name,sha256=sha(b)))
 save('exact-alias-receipt.json',dict(utc=now(),pattern=p.pattern.decode(),bodies=len(j['records']),hits=hits,full_bodies=True,cutoff=None))
 print('exact aliases',hits)
 for n in ['omega-head.json','openai-head.json']:
  x=json.loads((L/'sources'/n).read_bytes());print(n,x['sha'],x['commit']['committer']['date'])
elif mode=='delta':
 j=json.loads((L/'sources/omega-compare.json').read_bytes());base='aa026efa802f4361758b827d6b68231ac353948f';head='a19a578cd06b57a4ea4d287cb0df92f9085117ae'
 r=dict(utc=now(),base=base,head=head,status=j['status'],total_commits=j['total_commits'],returned_commits=len(j['commits']),files=len(j['files']),merge_base=j['merge_base_commit']['sha'],paths=[x['filename'] for x in j['files']],semantic_clearance=False)
 r['caps_ok']=r['total_commits']==r['returned_commits'] and r['files']<300 and r['returned_commits']<250
 r['ancestry_ok']=r['merge_base']==base and j['behind_by']==0
 save('registry-delta-receipt.json',r);print(json.dumps(r,indent=2))
