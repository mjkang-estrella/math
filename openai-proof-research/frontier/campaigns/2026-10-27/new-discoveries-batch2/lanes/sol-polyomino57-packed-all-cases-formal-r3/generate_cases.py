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
 ns=f'C{a}_{b}_{e}';pre='set_option autoImplicit false\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace '+ns+'\nopen Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed\n'
 def write(mod,imports,body):
  s=''.join('import '+i+'\n' for i in imports)+pre+body+'\nend '+ns+'\n'
  for d in ['dev','formal']:(L/d/(mod+'.lean')).write_text(s)
 write(ns+'Data',['MaskBridge'],f'def point (i : Fin {n}) : GridPoint := '+tree([f'({x},{y})' for x,y in cells],'i.val')+'\n'+f'def group (i : ℕ) : Finset GridPoint := '+tree([fs([p for i,p in enumerate(cells) if g>>i&1]) for g in gs],'i')+'\n'+'def table (m : ℕ) : ℕ := '+tree(rows,'m')+f'\ndef value (A : Finset ℕ) (v : Fin {n}) : ℕ := digit (rowOf {k} table A) v.val\n')
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
 write(ns+'Merge',[ns+'Data'],f'theorem merge_check : ∀ u : Fin {N}, unionCheck {k} {n} table u.val = true := by decide')
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
    exact unionCheck_sound (fun u hu => merge_check ⟨u,hu⟩) A B hA hB hnA hnB hd
 theorem case_{a}_{b}_{e} : ∀ Q : Finset GridPoint, Q ⊆ domain {a} {b} {e} → EdgeConnected Q →
    Q.card = 11 → ¬ HitsAll Q (groups {a} {b} {e}) :=
  excludes {a} {b} {e} point point_injective Finset.univ (Finset.range {k}) group value
    domain_eq groups_mem certificate (by decide) (fun v _ => full_check v)''')
 return [ns+x for x in ['Data','Geometry','Bounds','Base','Edges','Edge','Merge','Full','Case']]
if __name__=='__main__':
 import sys
 mods=generate(*map(int,sys.argv[1:4]));print(json.dumps(mods))
