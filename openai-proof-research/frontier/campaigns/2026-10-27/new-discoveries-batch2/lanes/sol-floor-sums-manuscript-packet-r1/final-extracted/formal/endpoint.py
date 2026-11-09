from pathlib import Path
import json,re
L=Path(__file__).resolve().parent
N=[d.get('atom',tuple(d.get('args',[]))) for d in map(json.loads,(L/'frozen/sol-floor-sums-certificate-r2/dag.jsonl').open())]
defs={int(m[1]):m[2] for g in L.glob('Sem[0-9]*.lean') for m in re.finditer(r'^def e(\d+) .*? := (.*)$',g.read_text(),re.M)}
def head(i):return N[i] if isinstance(N[i],str) else head(N[i][0])
def full(i):
 if isinstance(N[i],str):
  if N[i].lstrip('-').isdigit():return f'({N[i]} : ℤ)'
  return {'m':'(m : ℤ)','H':'(H : ℤ)','t':'((m/3 : ℕ) : ℤ)','a':'(a 0 : ℤ)','b':'(a 1 : ℤ)','c':'(a 2 : ℤ)','d':'(a 3 : ℤ)'}[N[i]]
 return re.sub(r'\(e(\d+) _v\)',lambda m:full(int(m[1])),defs[i])
ids=[137,234,242,254,292,327,458,3126,4012,4510,4942,4947,155,166,177,392]
lines=['import SourceBridge','import Dag276','set_option autoImplicit false','set_option warningAsError true','set_option maxRecDepth 20000','namespace Assembly',
'theorem query_of_neg_bound (m H : ℕ) (hm : 0 < m) (hH : 1 ≤ H) (hHm : H ≤ m)',
'    (a : Fin 4 → ℕ) (ha : ∀ i, a i < m) (hs : Monotone a)',
'    (hneg : FloorSums.clampedSum m H a < -3 * ((m/3 : ℕ) : ℤ)) : Query (sourceEnv m H a) := by',
'  have h0 := ha 0','  have h1 := ha 1','  have h2 := ha 2','  have h3 := ha 3',
'  have s01 := hs (show (0 : Fin 4) ≤ 1 by decide)','  have s12 := hs (show (1 : Fin 4) ≤ 2 by decide)','  have s23 := hs (show (2 : Fin 4) ≤ 3 by decide)',
'  have hr := Nat.mod_lt m (show 0 < 3 by decide)','  have hd := Nat.mod_add_div m 3',
'  refine ⟨'+', '.join('?_ ' for _ in range(17))+'⟩']
for i in ids:lines += ['  · change '+full(i),'    omega']
lines += ['  · change e11660 (sourceEnv m H a) < -3 * ((m/3 : ℕ) : ℤ)','    rw [sum_match]','    exact hneg',
'theorem sorted_clamped_bound : FloorSums.SortedClampedBound := by',
'  intro m H hm hH hHm a ha hs','  by_contra hb',
'  have hneg : FloorSums.clampedSum m H a < -3 * ((m/3 : ℕ) : ℤ) := lt_of_not_ge hb',
'  exact n22671 (sourceEnv m H a) (query_of_neg_bound m H hm hH hHm a ha hs hneg)',
'theorem literal_endpoint : FloorSums.LiteralEndpoint := FloorSums.endpoint_of_sorted_clamped_bound sorted_clamped_bound',
'end Assembly']
(L/'Endpoint.lean').write_text('\n'.join(lines)+'\n')
print('exact source endpoint attempt generated')
