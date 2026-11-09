import json, pathlib, itertools, math
root=pathlib.Path(__file__).resolve().parent.parent
N=20
X={0:[[1]]}; I={0:[[0]]}
def B(m): return min(m,N+1-m)
def get(T,m,r,s):
    if m not in T or not 0<=r<len(T[m]) or not 0<=s<len(T[m][r]): return 0
    return T[m][r][s]
for m in range(1,N+1):
    b=B(m); X[m]=[[0]*(b+1) for _ in range(b+1)];I[m]=[[0]*(b+1) for _ in range(b+1)]
    for r in range(1,b+1):
      for s in range(1,b+1):
        ki=sum((2 if t==1 else 1)*(2 if u==1 else 1)*get(X,m-1,r-1+t,s-1+u) for t in range(3) for u in range(3))
        c1=c2=0
        for k in range(1,m):
          v=sum(get(X,m-k,r-a,s-c)*get(I,k,a,c) for a in range(1,r) for c in range(1,s))
          c1+=math.comb(m-1,k-1)*v;c2+=math.comb(m,k)*v
        assert ki>=c1
        I[m][r][s]=ki-c1;X[m][r][s]=ki-c1+c2
cached=json.load(open(root.parent/'expanded-corpus-r133/outputs/stack_pairs_P_1_82.json'))
assert all(X[m][1][1]==int(cached[str(m)]) for m in range(1,N+1))
# Independent literal diagnostic (not proof).
def sort(w):
    if not w:return ()
    m=max(w);j=w.index(m)
    return sort(w[:j])+sort(w[j+1:])+(m,)
for n in range(1,9):
    h={}
    for w in itertools.permutations(range(n)):
        y=sort(w);h[y]=h.get(y,0)+1
    assert sum(v*v for v in h.values())==X[n][1][1]
print('All top-max seeds 1..20 match cached data; literal enumeration agrees through 8.')
s='import StackSortSeeds2Recursion\nnamespace StackSort.Seeds2\n'
for m in range(21):
    vals=[f'({X[m][r][t]}, {I[m][r][t]})' for r in range(len(X[m])) for t in range(len(X[m]))]
    s+=f'def row{m} : List (ℕ × ℕ) := ['+', '.join(vals)+']\n'
s+='def rawRow : ℕ → List (ℕ × ℕ)\n'
for m in range(21):s+=f'  | {m} => row{m}\n'
s+='  | _ => []\ndef table (M r s : ℕ) : ℕ × ℕ :=\n  if M = 0 then (if r = 0 ∧ s = 0 then 1 else 0, 0) else if 1 ≤ r ∧ r ≤ bound M ∧ 1 ≤ s ∧ s ≤ bound M then ((rawRow M)[r*(bound M+1)+s]?).getD (0,0) else (0,0)\ndef tableX : Counts := fun M r s => (table M r s).1\ndef tableI : Counts := fun M r s => (table M r s).2\n'
s+='theorem table_seeds : ∀ n : Fin 20, tableX (n+1) 1 1 = seed20[(n : ℕ)+1]! := by decide\nend StackSort.Seeds2\n'
(root/'StackSortSeeds2Data.lean').write_text(s)
for m in range(1,21):
    s=f'import StackSortSeeds2Data\nnamespace StackSort.Seeds2\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\ntheorem row_valid_{m} : ∀ r s : Fin {B(m)+1},\n  (tableX {m} r s, tableI {m} r s) = topStep tableX tableI {m} r s := by decide\nend StackSort.Seeds2\n'
    (root/f'StackSortSeeds2Row{m:02}.lean').write_text(s)
json.dump({'X':X,'I':I},open(root/'numeric.json','w'))
