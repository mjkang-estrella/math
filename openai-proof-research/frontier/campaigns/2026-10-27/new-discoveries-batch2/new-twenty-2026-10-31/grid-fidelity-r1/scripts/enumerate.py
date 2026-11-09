import itertools as it,json
from pathlib import Path
root=Path(__file__).resolve().parent.parent
def rgs(n):
 if n==0:
  yield ();return
 def go(a,k):
  if len(a)==n: yield tuple(a);return
  for x in range(k+1): yield from go(a+[x],max(k,x+1))
 yield from go([0],1)
def canon(a):
 d={};return tuple(d.setdefault(x,len(d)) for x in a)
rows=[]; lean=['module','public import GridFinal6','public import GridRegression','@[expose] public section','open Grid343536','namespace FidelitySanity','set_option maxRecDepth 100000','set_option maxHeartbeats 4000000']
for m,n in [(1,k) for k in range(1,7)]+[(2,2),(2,3),(3,3),(3,4)]:
 N=m*n
 adj=[{j for j in range(N) if abs(i//n-j//n)+abs(i%n-j%n)==1} for i in range(N)]
 degs={}
 for v in range(N): degs.setdefault(len(adj[v]),[]).append(v)
 groups=list(degs.values());eq=set();candidates=0
 for pieces in it.product(*(list(rgs(len(g))) for g in groups)):
  labels=[None]*N
  for t,(g,p) in enumerate(zip(groups,pieces)):
   for v,c in zip(g,p):labels[v]=(t,c)
  a=canon(labels); candidates+=1
  sig=[tuple(sum(a[w]==c for w in adj[v]) for c in range(max(a)+1)) for v in range(N)]
  if all(a[u]!=a[v] or sig[u]==sig[v] for u in range(N) for v in range(u)):
   eq.add(a)
 # full automorphism search, preserving degrees and every adjacency/nonadjacency
 autos=[]
 def bt(p,used):
  k=len(p)
  if k==N: autos.append(tuple(p));return
  for x in range(N):
   if x not in used and len(adj[k])==len(adj[x]) and all((j in adj[k])==(p[j] in adj[x]) for j in range(k)):
    bt(p+[x],used|{x})
 bt([],set())
 identity=tuple(range(N)); idx={p:i for i,p in enumerate(autos)}
 mul=[[idx[tuple(p[q[v]] for v in range(N))] for q in autos] for p in autos]
 subs=[]
 for mask in range(1<<len(autos)):
  H={i for i in range(len(autos)) if mask>>i&1}
  if idx[identity] in H and all(mul[a][b] in H for a in H for b in H): subs.append(H)
 def orb(H):
  return canon([min(autos[g][v] for g in H) for v in range(N)])
 orbits={orb(H) for H in subs}
 free=any(sum(p[v]==v for p in autos)==1 for v in range(N))
 assert eq==orbits
 assert free == (not (2<=m==n<=3))
 assert (len(eq)==len(subs))==free
 item=dict(m=m,n=n,degree_compatible_partitions=candidates,equitable=len(eq),automorphisms=len(autos),subgroups=len(subs),distinct_orbits=len(orbits),free_vertex=free,partitions=[list(p) for p in sorted(eq)])
 rows.append(item);print(json.dumps(item),flush=True)
 name=f'labels_{m}_{n}'; val=str(item['partitions'])
 lean += [f'def {name} : List (List ℕ) := {val}',
 f'example : {name}.Nodup := by decide',
 f'example : {name}.length = {len(eq)} := by decide',
 f'example : {name}.all (fun lab => decide (labelEquitable {m} {n} lab)) = true := by decide',
 f'example (lab : List ℕ) (h : labelEquitable {m} {n} lab) :',
 f'    ∃ H : Subgroup (G {m} {n} ≃g G {m} {n}), labelSetoid {m} {n} lab = orbitSetoid (G {m} {n}) H :=',
 f'  ((GridFinal6.mathdb_343536 {m} {n} (by decide) (by decide)).1 _).mp ((labelEquitable_iff _ _ _).mpr h)']
 lean += [f'example : {"HasFreeVertex" if free else "¬ HasFreeVertex"} (G {m} {n}) := by',
 f'  {"apply" if free else "intro h; have hbad : ¬ (2 ≤ "+str(m)+" ∧ "+str(m)+" = "+str(n)+" ∧ "+str(n)+" ≤ 3) :="} '+(f'(free_classification {m} {n} (by decide) (by decide)).mpr' if free else f'(free_classification {m} {n} (by decide) (by decide)).mp h'),
 '  decide' if free else '  exact hbad (by decide)']
lean += ['example : ¬ Nonempty (EqPart (G 2 2) ≃o Subgroup (G 2 2 ≃g G 2 2)) := exceptional_no_iso 2 (by decide) (by decide)',
'example : ¬ Nonempty (EqPart (G 3 3) ≃o Subgroup (G 3 3 ≃g G 3 3)) := exceptional_no_iso 3 (by decide) (by decide)',
'example : HasFreeVertex (G 4 4) := (free_classification 4 4 (by decide) (by decide)).mpr (by decide)',
'example : ¬ IsEquitable (G 3 4) (labelSetoid 3 4 [0,0,0,0,0,0,0,0,0,0,0,0]) := by',
'  rw [labelEquitable_iff]; decide',
'example : (⊥ : Setoid (Fin 3 × Fin 4)) ≤ ⊤ := bot_le',
'example (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) : NaturalLatticeIso m n ↔ HasFreeVertex (G m n) :=',
'  natural_iso_iff main_orbit_proved free_classification exceptional_no_iso m n hm hn',
'#print axioms GridFinal6.mathdb_343536']
exec((root/'scripts/witness-fragment.txt').read_text())
lean += ['end FidelitySanity']
(root/'Sanity.lean').write_text('\n'.join(lean)+'\n')
(root/'enumeration.json').write_text(json.dumps(rows,indent=2)+'\n')
