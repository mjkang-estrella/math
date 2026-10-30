import sys,json,re,hashlib,datetime,urllib.request,subprocess,gzip
from pathlib import Path
L=Path(__file__).resolve().parent; R=L.parents[5]; B=L.parents[1]
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
mode=sys.argv[1]
if mode=='init':
 known={};bases=[]
 for k in [170,172,173,174]:
  p=L.parent/f'sol-fresh-source-discovery-r{k}/history-receipt.json';b=p.read_bytes();bases.append([str(p),sha(b)]);known.update({r[0]:r[1:] for r in json.loads(b)['records']})
 paths=set(known)
 for d in L.parent.iterdir():
  if d.is_dir() and d!=L:
   for n in ['SUMMARY.md','discovery.md','PROOF.md','review.md','REVIEW.md','DECISION.md']:
    if (d/n).is_file():paths.add(str((d/n).relative_to(R)))
 rows=[];changed=[];missing=[]
 for p in sorted(paths):
  f=R/p
  if not f.is_file():missing.append(p);continue
  b=f.read_bytes();row=[p,sha(b),len(b)];rows.append(row)
  if known.get(p)!=row[1:]:changed.append(row)
 save('history-receipt.json',dict(utc=now(),bases=bases,records=rows,changed=changed,missing=missing,policy='Union qualified original indexes; retain all older science, refresh immediate original documents; no new echo exclusions. Bounded coverage.'))
 for n in ['NEXT.md','ledger.json','prior-campaign-context.json','AGENTS.md']:(L/('context-'+n)).write_bytes((B/n).read_bytes())
 (L/'context-ancestor-AGENTS.md').write_bytes((R/'AGENTS.md').read_bytes())
 (L/'inherited-history-qualification.json').write_bytes((L.parent/'sol-fresh-source-discovery-r174/inherited-history-qualification.json').read_bytes())
 print('records',len(rows),'changed',len(changed),'missing',len(missing),'r111-113',[(k,sum(f'r{k}/' in r[0] for r in rows)) for k in [111,112,113]])
elif mode=='screen':
 pat=re.compile(sys.argv[2],re.I);hits=[]
 for p,h,z in json.loads((L/'history-receipt.json').read_text())['records']:
  s=(R/p).read_text(errors='replace');ms=list(pat.finditer(s))
  if ms:hits.append(dict(path=p,sha256=h,excerpts=[s[max(0,m.start()-100):m.end()+230] for m in ms[:8]]))
 save(sys.argv[3],dict(utc=now(),pattern=pat.pattern,hits=hits));print(json.dumps(hits)[:23000])
elif mode=='fetch':
 (L/'sources').mkdir(exist_ok=True)
 for arg in sys.argv[2:]:
  n,u=arg.split('=',1);rec=dict(utc=now(),url=u,name=n)
  try:
   assert not any(s in u.lower() for s in ['github','codeload','sciencedirect','google.','ieeexplore'])
   with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Mathematical-source-research/1.0'}),timeout=25) as f:
    b=f.read(12000001);assert len(b)<=12000000;(L/'sources'/n).write_bytes(b);rec.update(status=f.status,final_url=f.url,sha256=sha(b),bytes=len(b))
  except Exception as e:rec['error']=str(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
  print(rec)
elif mode=='text':
 for n in sys.argv[2:]:subprocess.run(['pdftotext','-layout',str(L/'sources'/n),str(L/'sources'/(n+'.txt'))],check=True)
elif mode=='registry':
 pat=re.compile('irregularis|irregulariz|2506[.-]21254|115773|Bourneuf|Colinot|Humeau|Martinod',re.I);rows=[]
 for rec in json.loads((L.parent/'sol-fresh-source-discovery-r172/registry-screen.json').read_text())['records']:
  p=Path(rec['path']);b=p.read_bytes();s=gzip.decompress(b).decode() if p.suffix=='.gz' else b.decode()
  try:j=json.loads(s);hits=[x for x in j.get('tree',[]) if pat.search(x.get('path',''))]
  except json.JSONDecodeError:hits=[line for line in s.splitlines() if pat.search(line)]
  rows.append(dict(path=str(p),sha256=sha(b),bytes=len(b),hits=hits))
 for p in [R/'sources/CONTENTS.md',R/'sources/preprints-tree.json']:
  b=p.read_bytes();s=b.decode();hits=[s[max(0,m.start()-90):m.end()+180] for m in pat.finditer(s)];rows.append(dict(path=str(p),sha256=sha(b),bytes=len(b),hits=hits))
 save('registry-screen.json',dict(utc=now(),pattern=pat.pattern,records=rows,limits='Cached pinned paths/catalogues only; current GitHub routes denied in earlier work, not retried. Missing merge trees and capped intervals PARKED. No worldwide/current exhaustive clearance.'));print([(r['path'],len(r['hits'])) for r in rows])
