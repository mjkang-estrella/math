from pathlib import Path
import gzip,json,resource,signal
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(200,200));signal.alarm(220)
L=Path(__file__).resolve().parent

def tree(v,x):
 if len(v)==1:return str(v[0])
 mid=len(v)//2
 return f'(if {x} < {mid} then {tree(v[:mid],x)} else {tree(v[mid:],f"({x}-{mid})")})'
def fs(ps):return '{'+','.join(f'({x},{y})' for x,y in ps)+'}'
def generate(a,b,e):
 cells=sorted([(x,y) for x in range(-10,12) for y in range(-10,12) if 0<=x+y<=a and e<=x-y<=e+b],key=lambda p:(sum(p),p[0]-p[1]));n=len(cells)
 centers=[(x,y) for x in range(-10,12) for y in range(-10,12) if a-5<=x+y<=5 and e+b-5<=x-y<=e+5];holes={(2,2),(2,-2),(-2,2),(-2,-2)}
 groups={sum(1<<i for i,(x,y) in enumerate(cells) if (x-cx,y-cy) in holes) for cx,cy in centers}
 groups.update(sum(1<<i for i,(x,y) in enumerate(cells) if f(x,y)==bound) for f,bound in [(lambda x,y:x+y,0),(lambda x,y:x+y,a),(lambda x,y:x-y,e),(lambda x,y:x-y,e+b)])
 gs=[g for g in groups if not any(h!=g and h&g==h for h in groups)];gs.sort(key=lambda g:[i for i in range(n) if g>>i&1]);k=len(gs);N=1<<k
 raw=gzip.decompress((L/f'frozen/frozen/inputs/compression/steiner-{a}-{b}-{e}.bin.gz').read_bytes());assert len(raw)==N*n
 rows=[sum(v*64**i for i,v in enumerate(raw[m*n:(m+1)*n])) for m in range(N)]
 fullrows=rows
 best=min((m for m in range(1,N) if all(raw[m*n+i]>=12 for i in range(n))),key=lambda m:(m.bit_count(),m))
 positions=[i for i in range(k) if best>>i&1]
 gs=[gs[i] for i in positions];k=len(gs);N=1<<k
 rows=[fullrows[sum((1<<positions[i]) for i in range(k) if m>>i&1)] for m in range(N)]
 ns=f'R{a}_{b}_{e}';pre='set_option autoImplicit false\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace '+ns+'\nopen Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed\n'
 def write(mod,imports,body):
  s=''.join('import '+i+'\n' for i in imports)+pre+body+'\nend '+ns+'\n'
  for d in ['dev','formal']:(L/d/(mod+'.lean')).write_text(s)
 dataImports=['PackedHalf'];tableExpr=tree(rows,'m')
 if N>256:
  dataImports=[]
  for start in range(0,N,64):
   bn=ns+f'Rows{start//64}';dataImports.append(bn)
   write(bn,['PackedHalf'],f'def rows{start//64} (m : ℕ) : ℕ := '+tree(rows[start:start+64],'m'))
  tableExpr=tree([f'(rows{start//64} (m-{start}))' for start in range(0,N,64)],'(m/64)')
 write(ns+'Data',dataImports,f'def point (i : Fin {n}) : GridPoint := '+tree([f'({x},{y})' for x,y in cells],'i.val')+'\n'+f'def group (i : ℕ) : Finset GridPoint := '+tree([fs([p for i,p in enumerate(cells) if g>>i&1]) for g in gs],'i')+'\n'+'def table (m : ℕ) : ℕ := '+tableExpr+f'\ndef value (A : Finset ℕ) (v : Fin {n}) : ℕ := digit (rowOf {k} table A) v.val\n')
 write(ns+'Geometry',[ns+'Data'],f'''theorem domain_eq : domain {a} {b} {e} = (Finset.univ : Finset (Fin {n})).image point := by decide
 theorem point_injective : Function.Injective point := by
  have h : ∀ i j : Fin {n}, point i = point j → i = j := by decide
  exact h
 theorem groups_mem : ∀ i ∈ Finset.range {k}, group i ∈ groups {a} {b} {e} := by decide''')
 write(ns+'Bounds',[ns+'Data'],f'theorem bounds_check : ∀ m : Fin {N}, boundCheck {n} (table m.val) = true := by decide')
 write(ns+'Base',[ns+'Data'],f'''theorem base_check : ∀ m : Fin {N}, m.val ≠ 0 → ∀ v : Fin {n},
  (∀ i ∈ decode {k} m.val, point v ∈ group i) → digit (table m.val) v.val ≤ 1 := by decide''')
 edges=[(i,j) for i,(x,y) in enumerate(cells) for j,(z,t) in enumerate(cells) if abs(x-z)+abs(y-t)==1]
 write(ns+'Edges',[ns+'Data'],f"def edges : List (Fin {n} × Fin {n}) := ["+','.join(f'({i},{j})' for i,j in edges)+f"]\ntheorem edge_mem : ∀ v w : Fin {n}, Adj (point v) (point w) → (v,w) ∈ edges := by decide")
 write(ns+'Edge',[ns+'Edges'],f'''theorem edge_check : ∀ m : Fin {N}, m.val ≠ 0 → ∀ vw ∈ edges,
  digit (table m.val) vw.1.val ≤ digit (table m.val) vw.2.val + 1 := by decide''')
 write(ns+'Merge',[ns+'Data'],f'theorem merge_check : ∀ u : Fin {N}, halfCheck {k} {n} table u.val = true := by decide')
 write(ns+'Full',[ns+'Data'],f'theorem full_check : ∀ v : Fin {n}, 12 ≤ value (Finset.range {k}) v := by decide')
 write(ns+'Case',[ns+x for x in ['Geometry','Bounds','Base','Edge','Merge','Full']],f'''theorem certificate : GraphPotential.Certificate (fun i j => Adj (point i) (point j))
    Finset.univ (Finset.range {k}) (fun i j => point j ∈ group i) value := by
  apply bits_certificate {n} (fun v : Fin {n} => v.val) Finset.univ (Finset.range {k})
    (fun i j => Adj (point i) (point j)) (fun i j => point j ∈ group i) (rowOf {k} table)
  · intro v _; exact v.isLt
  · intro A _ _
    exact row_bounds (fun m hm => bounds_check ⟨m,hm⟩) A
  · intro A hA hn v _ hh
    have hb := base_check ⟨encode {k} A,encode_lt _ _⟩ (encode_nonzero hA hn) v
    rw [decode_encode _ _ hA] at hb
    exact hb hh
  · intro A hA hn v _ w _ he
    exact edge_check ⟨encode {k} A,encode_lt _ _⟩ (encode_nonzero hA hn) (v,w) (edge_mem v w he)
  · intro A B hA hB hnA hnB hd
    exact halfCheck_sound (fun u hu => merge_check ⟨u,hu⟩) A B hA hB hnA hnB hd
 theorem case_{a}_{b}_{e} : ∀ Q : Finset GridPoint, Q ⊆ domain {a} {b} {e} → EdgeConnected Q →
    Q.card = 11 → ¬ HitsAll Q (groups {a} {b} {e}) :=
  excludes {a} {b} {e} point point_injective Finset.univ (Finset.range {k}) group value
    domain_eq groups_mem certificate (by decide) (fun v _ => full_check v)''')
 mods=[]
 if N>256:mods+=dataImports
 mods += [ns+'Data',ns+'Geometry']
 for stage,var,chunk in [('Bounds','m',64),('Base','m',16),('Edges',None,0),('Edge','m',8),('Merge','u',4),('Full',None,0)]:
  mod=ns+stage
  if var is None or N<=64:mods.append(mod);continue
  path=L/'formal'/(mod+'.lean');src=path.read_text();beg=src.index('theorem ');head=src[:beg];decl=src[beg:src.index(' := by decide',beg)]
  name=decl.split()[1];batches=[]
  for bi,start in enumerate(range(0,N,chunk)):
   count=min(chunk,N-start);bm=mod+str(bi);batches.append(bm)
   text=decl.replace('theorem '+name+' :','theorem '+name+str(bi)+' :').replace(f'{var} : Fin {N}',f'{var} : Fin {count}').replace(var+'.val',f'({var}.val+{start})')
   for d in ['formal','dev']:(L/d/(bm+'.lean')).write_text(head+text+' := by decide\nend '+ns+'\n')
  # Use balanced dispatch below instead of nested sequential splits.
  def dispatch(lo,hi,indent):
   if hi-lo==1:
    start=lo*chunk;end=min(start+chunk,N);bi=lo
    return indent+f'have hb : {var}.val-{start} < {end-start} := by omega\n'+indent+f'have he : {var}.val-{start}+{start} = {var}.val := by omega\n'+indent+f'have hp := {name}{bi} ⟨{var}.val-{start},hb⟩\n'+indent+'simpa only [he] using hp\n'
   mid=(lo+hi)//2
   return indent+f'by_cases h{mid} : {var}.val < {mid*chunk}\n'+indent+'·\n'+dispatch(lo,mid,indent+'  ')+indent+'·\n'+dispatch(mid,hi,indent+'  ')
  body=decl+' := by\n  intro '+var+'\n'+dispatch(0,len(batches),'  ')
  write(mod,batches,body);mods+=batches+[mod]
 mods += [ns+'Case']
 return mods
if __name__=='__main__':
 import sys
 mods=generate(*map(int,sys.argv[1:4]));print(json.dumps(mods))
