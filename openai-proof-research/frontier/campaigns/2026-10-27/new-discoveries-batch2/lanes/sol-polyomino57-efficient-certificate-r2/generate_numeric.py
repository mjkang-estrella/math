import os,resource,signal,json,hashlib
from pathlib import Path
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(30,35));signal.alarm(40)
L=Path(__file__).resolve().parent
src=L.parent/'sol-fresh-finite-optimization-r26/embedding-certificate.jsonl'
rows=[]
with src.open() as f:
 for i,line in enumerate(f):
  if i>=135268:raise RuntimeError('input exceeds explicit bound')
  P,t=json.loads(line);assert len(P)==11 and len(t)==2
  rows.append((P,t))
def row(r):
 P,t=r
 return '(['+','.join('(%d,%d)'%tuple(p) for p in P)+'],(%d,%d))'%tuple(t)
def emit(name,rs):
 text='import Efficient\nset_option autoImplicit false\nset_option maxRecDepth 65536\nset_option maxHeartbeats 10000000\nnamespace Polyomino57\ndef '+name+' : List (List GridPoint × GridPoint) := [\n'+',\n'.join(map(row,rs))+']\ntheorem '+name+'_checked : numericBatch '+name+' = true := by decide\ntheorem '+name+'_sound : ∀ r ∈ '+name+', translate r.2 r.1.toFinset ⊆ witness := numericBatch_sound _ '+name+'_checked\nend Polyomino57\n'
 (L/'formal'/(name+'.lean')).write_text(text)
emit('NumericPilot',rows[:1024])
(L/'numeric-input.json').write_text(json.dumps({'source':str(src),'sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'rows':len(rows),'kernel_claim':False},indent=2))
