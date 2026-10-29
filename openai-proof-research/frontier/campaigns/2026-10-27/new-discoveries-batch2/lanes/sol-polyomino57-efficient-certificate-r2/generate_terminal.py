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
  if i>=135268:raise RuntimeError('bounded input exceeded')
  P,t=json.loads(line);assert len(P)==11
  rows.append('(['+','.join('(%d,%d)'%tuple(p) for p in P)+'],(%d,%d))'%tuple(t))
mods=[]
for part in range((len(rows)+1023)//1024):
 name='Terminal%03d'%part;mods.append(name)
 s=['import PlacementTree','set_option autoImplicit false','set_option maxRecDepth 8192','namespace Polyomino57']
 chunks=[]
 block=rows[part*1024:(part+1)*1024]
 for j in range((len(block)+31)//32):
  nm=name+'c'+str(j);chunks.append(nm)
  s.extend(['def '+nm+' : List (List GridPoint × GridPoint) := ['+','.join(block[j*32:(j+1)*32])+']',
   'theorem '+nm+'_checked : numericBatch '+nm+' = true := by decide'])
 def tree(ns):
  if len(ns)==1:return '(.leaf '+ns[0]+')'
  m=len(ns)//2;return '(.branch '+tree(ns[:m])+' '+tree(ns[m:])+')'
 s.append('def '+name+' : PlacementTree := '+tree(chunks))
 s.append('theorem '+name+'_checked : treeCheck '+name+' = true := by\n  simp only ['+name+',treeCheck,'+','.join(x+'_checked' for x in chunks)+',Bool.and_self]')
 s.append('theorem '+name+'_sound : ∀ row, TreeMember row '+name+' → translate row.2 row.1.toFinset ⊆ witness := treeCheck_sound _ '+name+'_checked')
 s.append('end Polyomino57')
 (L/'formal'/(name+'.lean')).write_text('\n'.join(s)+'\n')
(L/'terminal-modules.json').write_text(json.dumps(mods))
