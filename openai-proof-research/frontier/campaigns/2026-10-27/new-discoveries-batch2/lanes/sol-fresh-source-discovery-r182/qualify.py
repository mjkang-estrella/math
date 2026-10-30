import json,hashlib,re,datetime,gzip
from pathlib import Path
L=Path(__file__).resolve().parent;R=L.parents[5]
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
rec=[];(L/'originals').mkdir(exist_ok=True)
for p,h,z in json.loads((L/'history-receipt.json').read_text())['records']:
 if any('/sol-fresh-source-discovery-r'+str(k)+'/' in p for k in [111,112,113,23,38,41,67]):
  b=(R/p).read_bytes();assert sha(b)==h
  name=sha(p.encode())[:12]+'-'+Path(p).name;(L/'originals'/name).write_bytes(b)
  rec.append(dict(original=p,copy='originals/'+name,sha256=h,bytes=z))
save('original-copy-provenance.json',rec)
base=L.parent/'sol-fresh-source-discovery-r172/registry-path-screen.json'
pat=re.compile(r'Fernando|Kousik|2606[.-]01037|PowerSum|Diagonal|Permutation|Trace|FiniteField',re.I);out=[]
for r in json.loads(base.read_bytes())['records']:
 p=Path(r['path']);b=p.read_bytes();s=gzip.decompress(b).decode() if p.suffix=='.gz' else b.decode()
 try:
  j=json.loads(s);items=j.get('tree',[]) if isinstance(j,dict) else [];hits=[x for x in items if pat.search(x.get('path',''))]
 except json.JSONDecodeError:
  items=s.splitlines();hits=[x for x in items if pat.search(x.split('\t')[-1])]
 out.append(dict(path=str(p),sha256=sha(b),entries=len(items),hits=hits))
save('registry-screen.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),input=str(base),sha256=sha(base.read_bytes()),records=out,limits='Actual cached input trees screened, names only; no body absence or current HEAD clearance. GitHub denied routes not retried. Inherited missing merge trees and capped intervals PARKED. Current public search receipt separate. No acceptance/investment clearance.'))
print('copied originals',len(rec),'cached registry inputs',len(out),'entries',sum(r['entries'] for r in out),'hits',sum(len(r['hits']) for r in out))
