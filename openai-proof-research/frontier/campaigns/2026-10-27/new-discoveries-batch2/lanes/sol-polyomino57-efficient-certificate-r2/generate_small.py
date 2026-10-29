import os,resource,signal,json
from pathlib import Path
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(15,20));signal.alarm(25)
L=Path(__file__).resolve().parent
src=L.parent/'sol-fresh-finite-optimization-r26/embedding-certificate.jsonl'
def pt(p):return '(%d,%d)'%tuple(p)
def cells(P):return '['+','.join(map(pt,P))+']'
rows=[]
with src.open() as f:
 for _ in range(32):
  P,t=json.loads(next(f));rows.append('('+cells(P)+','+pt(t)+')')
(L/'formal/NumericPilot.lean').write_text('import Efficient\nset_option autoImplicit false\nset_option maxRecDepth 8192\nnamespace Polyomino57\ndef numericPilot : List (List GridPoint × GridPoint) := ['+','.join(rows)+']\ntheorem numericPilot_checked : numericBatch numericPilot = true := by decide\ntheorem numericPilot_sound : ∀ r ∈ numericPilot, translate r.2 r.1.toFinset ⊆ witness := numericBatch_sound _ numericPilot_checked\nend Polyomino57\n')
def norm(P):
 x=min(x for x,y in P);y=min(y for x,y in P)
 return tuple(sorted((a-x,b-y) for a,b in P)),(-x,-y)
def nbr(P):return {(x+dx,y+dy) for x,y in P for dx,dy in [(1,0),(-1,0),(0,1),(0,-1)]}-set(P)
layers=[ [((0,0),)] ];maps=[]
for k in range(4):
 nxt=sorted({norm(set(P)|{b})[0] for P in layers[-1] for b in nbr(P)})
 lookup={P:i for i,P in enumerate(nxt)};cs=[]
 for P in layers[-1]:
  edges=[]
  for b in sorted(nbr(P)):
   Q,t=norm(set(P)|{b});edges.append('('+pt(b)+',('+str(lookup[Q])+','+pt(t)+'))')
  cs.append((P,'fun b => ((['+','.join(edges)+'] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))'))
 maps.append(cs);layers.append(nxt)
s=['import Assembly','set_option autoImplicit false','set_option maxRecDepth 65536','set_option maxHeartbeats 10000000','namespace Polyomino57']
for k,layer in enumerate(layers):
 s.append('def smallLayer%d : Array (List GridPoint) := #['%k+','.join(map(cells,layer))+']')
for k,cs in enumerate(maps):
 cases='\n'.join('  if row = '+cells(P)+' then '+expr+' else' for P,expr in cs)
 s.append('def smallChoices%d (row : List GridPoint) : GridPoint → ℕ × GridPoint :=\n'%k+cases+'\n  fun _ => (0,(0,0))')
 s.append('theorem smallClosure%d : arrayClosureCheck smallLayer%d smallLayer%d smallChoices%d = true := by decide'%(k,k,k+1,k))
s.append('end Polyomino57')
(L/'formal/SmallClosure.lean').write_text('\n'.join(s)+'\n')
(L/'small-data.json').write_text(json.dumps({'layer_lengths_external_only':list(map(len,layers)),'no_full_endpoint':True},indent=2))
