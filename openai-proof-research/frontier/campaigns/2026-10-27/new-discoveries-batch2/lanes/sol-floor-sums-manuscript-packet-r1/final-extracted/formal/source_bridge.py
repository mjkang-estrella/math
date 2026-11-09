from pathlib import Path
import json
L=Path(__file__).resolve().parent
N=[d.get('atom',tuple(d.get('args',[]))) for d in map(json.loads,(L/'frozen/sol-floor-sums-certificate-r2/dag.jsonl').open())]
C=json.loads((L/'clip-inventory.json').read_text());clips={r[0] for r in C};done=set()
def visit(i):
 if i in done or i in clips:return
 done.add(i)
 if isinstance(N[i],tuple):
  for j in N[i][1:]:visit(j)
visit(11660)
arith=set()
def expand(i):
 if i in arith:return
 arith.add(i)
 if isinstance(N[i],tuple):
  for j in N[i][1:]:expand(j)
for _,z,*_ in C:expand(z)
assert all(not isinstance(N[i],str) or not N[i].startswith('z3name!') for i in arith)
exprs=sorted(done|arith)
lines=['import ClipBridge','import Expansion','import Symmetry','import Mathlib.Tactic.Abel','set_option autoImplicit false','set_option warningAsError true','set_option maxRecDepth 20000','set_option maxHeartbeats 1500000','namespace Assembly',
'def sourceEnv (m H : ℕ) (a : Fin 4 → ℕ) : Vars := ⟨m, H, m/3, a 0, a 1, a 2, a 3⟩',
'theorem sum_match (m H : ℕ) (a : Fin 4 → ℕ) : e11660 (sourceEnv m H a) = FloorSums.clampedSum m H a := by',
'  unfold FloorSums.clampedSum', '  rw [FloorSums.explicit_sixteen]',
'  norm_num only [Finset.sum_empty, Finset.sum_singleton, Finset.sum_insert,',
'    Finset.mem_insert, Finset.mem_singleton, Finset.not_mem_empty,',
'    Fin.reduceFinMk, Nat.cast_add, Nat.cast_zero, Nat.cast_one,',
'    not_false_eq_true, Fin.isValue, Fin.mk.injEq, OfNat.ofNat_ne_zero,',
'    reduceCtorEq, or_self, or_false, false_or]',
'  simp only ['+', '.join('e'+str(i) for i in sorted(done))+']']
for i,*_ in C:lines.append(f'  rw [clip_{i} _ H rfl]')
lines += ['  simp only ['+', '.join('e'+str(i) for i in sorted(arith))+', sourceEnv]',
'  simp only [neg_mul, one_mul, neg_one_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]',
'  abel','end Assembly']
(L/'SourceBridge.lean').write_text('\n'.join(lines)+'\n')
print('source sum matching generated',len(done),len(arith))
