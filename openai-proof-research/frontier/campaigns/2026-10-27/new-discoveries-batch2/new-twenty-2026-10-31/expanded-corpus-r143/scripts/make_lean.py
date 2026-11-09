import json
r=json.load(open('outputs/pmd-certificate.json')); layers=r['layers'];mat=[[0]*12 for _ in range(12)]
for i,es in enumerate(layers):
 for u,v in es:mat[u][v]=mat[v][u]=i
vec=lambda xs:'!['+', '.join(map(str,xs))+']'
s='''import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Exact

namespace TorusPMD
-- Vertices of the ordinary Cartesian product of two cycles.
abbrev V (m n : ℕ) := Fin m × Fin n
def cycleAdj {n : ℕ} (u v : Fin n) : Prop :=
  u ≠ v ∧ ((u.val + 1) % n = v.val ∨ (v.val + 1) % n = u.val)
def torus (m n : ℕ) (u v : V m n) : Prop :=
  (u.1 = v.1 ∧ cycleAdj u.2 v.2) ∨ (u.2 = v.2 ∧ cycleAdj u.1 v.1)
instance (m n : ℕ) (u v : V m n) : Decidable (torus m n u v) := by
  unfold torus cycleAdj; infer_instance
-- An edge coloring specifies an ordered partition; on the residual edges
-- (colors at least i), exactly the edges of color i have positive weight.
def Decomposition {α : Type} (G : α → α → Prop) (k : ℕ) : Prop :=
  ∃ c : α → α → Fin k, ∃ w : Fin k → α → ℝ,
    (∀ u v, c u v = c v u) ∧
    (∀ i, ∃ u v, G u v ∧ c u v = i) ∧
    (∀ u v z, G u v → G u z → c u v = c u z → v = z) ∧
    (∀ i u v, G u v → i.val ≤ (c u v).val →
      (0 < w i u + w i v ↔ c u v = i))
noncomputable def pmd {α : Type} (G : α → α → Prop) : ℕ :=
  sInf {k | Decomposition G k}
def idx (u : V 3 4) : Fin 12 := ⟨u.1.val * 4 + u.2.val, by omega⟩
'''
s+='def colors : Fin 12 → Fin 12 → Fin 5 := '+vec([vec(row) for row in mat])+'\n'
s+='def weights : Fin 5 → Fin 12 → ℤ := '+vec([vec(row) for row in r['weights']])+'\n'
s+='''def c (u v : V 3 4) : Fin 5 := colors (idx u) (idx v)
def w (i : Fin 5) (u : V 3 4) : ℤ := weights i (idx u)
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
 theorem certificate :
    (∀ u v, c u v = c v u) ∧
    (∀ i, ∃ u v, torus 3 4 u v ∧ c u v = i) ∧
    (∀ u v z, torus 3 4 u v → torus 3 4 u z → c u v = c u z → v = z) ∧
    (∀ i u v, torus 3 4 u v → i.val ≤ (c u v).val →
      (0 < w i u + w i v ↔ c u v = i)) := by decide
 theorem five_part_decomposition : Decomposition (torus 3 4) 5 := by
  refine ⟨c, fun i u => (w i u : ℝ), certificate.1,
    certificate.2.1, certificate.2.2.1, ?_⟩
  intro i u v hG hi
  have h := certificate.2.2.2 i u v hG hi
  constructor
  · intro hp
    apply h.mp
    exact_mod_cast hp
  · intro hc
    have hp := h.mpr hc
    exact_mod_cast hp
 theorem pmd_le_five : pmd (torus 3 4) ≤ 5 := by
  exact Nat.sInf_le five_part_decomposition
 theorem refutes_conjecture_4_7 :
    ¬ (∀ m n : ℕ, 3 ≤ m → 3 ≤ n →
       (Even (m+n) ∨ (m,n) = (3,4) ∨ (m,n) = (3,6) ∨ (m,n) = (5,6)) →
       pmd (torus m n) = 6) := by
  intro h
  have he := h 3 4 (by decide) (by decide) (Or.inr (Or.inl rfl))
  have hl := pmd_le_five
  omega
#print axioms certificate
#print axioms five_part_decomposition
#print axioms pmd_le_five
#print axioms refutes_conjecture_4_7
end TorusPMD
'''
# ExactModCast is provided by NormNum dependencies in mathlib; use explicit import.
s=s.replace('import Mathlib.Tactic.Exact\n','import Mathlib.Tactic.NormNum.OfScientific\n')
open('TorusPMD.lean','w').write(s)
