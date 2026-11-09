import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];r=json.loads((D/'tour-certificate.json').read_text());p=r['permutations_1based']
vec=lambda x:'!['+', '.join(map(str,x))+']'
s='''import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Basic

namespace MathDB356266

def Permutation (n : Nat) (p : Fin n → Fin n) : Prop := Function.Injective p

def Overlaps {n : Nat} (p q : Fin (n+1) → Fin (n+1)) : Prop :=
  ∀ a b : Fin n, (p a.succ < p b.succ ↔ q a.castSucc < q b.castSucc)

def next {N : Nat} (i : Fin (N+1)) : Fin (N+1) :=
  ⟨(i.val + 1) % (N+1), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩

def EulerOrdering {n N : Nat} (t : Fin (N+1) → Fin (n+1) → Fin (n+1)) : Prop :=
  (∀ i, Permutation (n+1) (t i)) ∧ Function.Injective t ∧
  (∀ p, Permutation (n+1) p → ∃ i, t i = p) ∧
  (∀ i, Overlaps (t i) (t (next i)))

def position {N n : Nat} (i : Fin (N+1)) (a : Fin (n+1)) : Fin (N+1) :=
  ⟨(i.val + a.val) % (N+1), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩

def Realizes {n N : Nat} {A : Type} [LT A]
    (t : Fin (N+1) → Fin (n+1) → Fin (n+1)) (w : Fin (N+1) → A) : Prop :=
  ∀ i a b, t i a < t i b ↔ w (position i a) < w (position i b)

def tour : Fin 24 → Fin 4 → Fin 4 :=
'''+vec([vec([x-1 for x in row]) for row in p])+'''

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem tour_euler : EulerOrdering tour := by decide

theorem tour_not_realizable {A : Type} [LinearOrder A] (w : Fin 24 → A) :
    ¬ Realizes tour w := by
  intro h
'''
for k,e in enumerate(r['cycle_edges']):
 a,b=e['local_offsets'];s+=f'  have h{k} : w {e["from"]} < w {e["to"]} := (h {e["window"]} {a} {b}).mp (by decide)\n'
expr='h0'
for k in range(1,len(r['cycle_edges'])):expr=f'lt_trans ({expr}) h{k}'
s+=f'  exact (lt_irrefl (w 2)) ({expr})\n'
s+='''
/-- Literal counterexample: the edges form an Euler ordering of the clustered
    overlap graph, but no cyclic word realizes their order types. -/
theorem counterexample : ∃ t : Fin 24 → Fin 4 → Fin 4,
    EulerOrdering t ∧ ∀ (A : Type) [LinearOrder A] (w : Fin 24 → A), ¬ Realizes t w :=
  ⟨tour, tour_euler, fun _ _ w => tour_not_realizable w⟩

#print axioms tour_euler
#print axioms tour_not_realizable
#print axioms counterexample
end MathDB356266
'''
(D/'lean/Hurlbert.lean').write_text(s)
