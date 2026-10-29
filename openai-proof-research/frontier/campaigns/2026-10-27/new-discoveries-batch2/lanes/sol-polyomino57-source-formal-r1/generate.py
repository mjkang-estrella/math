import os,resource,signal,json
from pathlib import Path
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']: os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(20,25));signal.alarm(30)
L=Path(__file__).resolve().parent
pt=lambda p:f'({p[0]},{p[1]})'
lst=lambda s:'['+','.join(map(pt,s))+']'
C={(x,y) for x in range(-5,6) for y in range(-5,6) if abs(x)+abs(y)<=5 and (abs(x),abs(y))!=(2,2)}
order=[(0,0)];rem=C-set(order)
while rem:
 b=next(p for p in sorted(rem) if any(abs(p[0]-a[0])+abs(p[1]-a[1])==1 for a in order))
 order.append(b);rem.remove(b)
s='''import Growth
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Polyomino57
'''
s+='def witnessOrder : List GridPoint := '+lst(order)+'\n'
s+='def witness : Finset GridPoint := witnessOrder.toFinset\n'
s+='theorem witness_card : witness.card = 57 := by decide\n'
s+='theorem witness_connected : EdgeConnected witness := by\n  have h : attachCheck {(0,0)} '+lst(order[1:])+' = true := by decide\n  have hC := attachCheck_sound {(0,0)} '+lst(order[1:])+' (connected_singleton (0,0)) h\n  convert hC using 1; decide\n'
# Independently literal bounded-grid description, exact finite equality.
s+='def square : Finset GridPoint := ((List.range 11).flatMap (fun x => (List.range 11).map (fun y => ((x : ℤ)-5,(y : ℤ)-5)))).toFinset\n'
s+='def diamondMinusFour : Finset GridPoint := square.filter (fun p => p.1.natAbs + p.2.natAbs ≤ 5 ∧ ¬ (p.1.natAbs = 2 ∧ p.2.natAbs = 2))\n'
s+='theorem witness_literal : witness = diamondMinusFour := by decide\n'
s+='end Polyomino57\n'
(L/'formal/Witness.lean').write_text(s)
rows=[]
with (L/'input/lanes/sol-fresh-finite-optimization-r26/embedding-certificate.jsonl').open() as f:
 for i,line in enumerate(f):
  if i==64:break
  P,t=json.loads(line);rows.append((P,t))
s='''import Witness
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace Polyomino57
'''
for i,(P,t) in enumerate(rows):
 s+=f'def pilotPiece{i} : List GridPoint := '+lst(P)+'\n'
 s+=f'theorem pilotPlacement{i} : translate {pt(t)} pilotPiece{i}.toFinset ⊆ witness :=\n  placementCheck_sound witness pilotPiece{i} {pt(t)} (by decide)\n'
s+='end Polyomino57\n'
(L/'formal/Pilot.lean').write_text(s)
