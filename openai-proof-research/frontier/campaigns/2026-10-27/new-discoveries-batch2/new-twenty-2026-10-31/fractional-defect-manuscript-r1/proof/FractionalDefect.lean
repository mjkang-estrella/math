import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

noncomputable section
namespace FractionalDefect
open scoped BigOperators
abbrev Vertex (m a : ℕ) := Fin (m+1) × Fin (a+1)
abbrev Coloring (m a k : ℕ) := Vertex m a → Fin (k+1) → ℝ

def Valid {m a k : ℕ} (f : Coloring m a k) : Prop :=
 (∀ v c, 0 ≤ f v c) ∧ ∀ v, ∑ c, f v c = 1

def Adj {m a : ℕ} (v w : Vertex m a) : Prop := v.1 ≠ w.1
instance {m a : ℕ} (v w : Vertex m a) : Decidable (Adj v w) := inferInstanceAs (Decidable (v.1 ≠ w.1))

def defect {m a k : ℕ} (f : Coloring m a k) (v : Vertex m a) : ℝ :=
 ∑ w, if Adj v w then ∑ c, min (f v c) (f w c) else 0

def graphDefect {m a k : ℕ} (f : Coloring m a k) : ℝ :=
 Finset.univ.sup' Finset.univ_nonempty (defect f)

def MinimumDefect (m a k : ℕ) (d : ℝ) : Prop :=
 IsLeast {x : ℝ | ∃ f : Coloring m a k, Valid f ∧ graphDefect f = x} d

-- Indices m,a,k encode the strictly positive source parameters m+1,a+1,k+1.
def predicted (m a k : ℕ) : ℝ :=
 (((m + 1 + k) / (k + 1) : ℕ) - 1 : ℝ) * (a + 1)

def SourceConjecture : Prop := ∀ m a k : ℕ,
 MinimumDefect m a k (predicted m a k)

def witness : Coloring 3 1 2 := fun v c =>
 if v.1.val = 0 then (if c.val = 2 then 1 else 0)
 else if v.1.val = 1 then (if c.val = 1 then 2/3 else if c.val = 2 then 1/3 else 0)
 else if v.1.val = 2 then
   (if v.2.val = 0 then (if c.val = 1 then 1 else 0) else (if c.val = 0 then 1 else 0))
 else if v.2.val = 0 then (if c.val = 0 then 2/3 else if c.val = 1 then 1/3 else 0)
 else (if c.val = 0 then 1 else 0)

theorem witness_valid : Valid witness := by
 constructor
 · intro v c
   rcases v with ⟨i,j⟩
   fin_cases i <;> fin_cases j <;> fin_cases c <;> norm_num [witness]
 · intro v
   rcases v with ⟨i,j⟩
   fin_cases i <;> fin_cases j <;> simp only [Fin.sum_univ_succ] <;> norm_num [witness]

theorem witness_defects (v : Vertex 3 1) : defect witness v ≤ 5/3 := by
 rcases v with ⟨i,j⟩
 fin_cases i <;> fin_cases j <;>
   norm_num [defect, Adj, Fintype.sum_prod_type, Fin.sum_univ_succ, witness]

theorem graphDefect_witness_le : graphDefect witness ≤ 5/3 := by
 apply Finset.sup'_le
 intro v _
 exact witness_defects v

-- The numerical invariant is the infimum of precisely the source objective values.
def D (m a k : ℕ) : ℝ :=
 sInf {x : ℝ | ∃ f : Coloring m a k, Valid f ∧ graphDefect f = x}

theorem D_eq_of_minimum {m a k : ℕ} {d : ℝ} (h : MinimumDefect m a k d) :
 D m a k = d := h.csInf_eq

theorem defect_nonneg {m a k : ℕ} {f : Coloring m a k} (hf : Valid f)
 (v : Vertex m a) : 0 ≤ defect f v := by
 apply Finset.sum_nonneg
 intro w _
 split_ifs
 · exact Finset.sum_nonneg (fun c _ => le_min (hf.1 v c) (hf.1 w c))
 · exact le_refl 0

theorem graphDefect_nonneg {m a k : ℕ} {f : Coloring m a k} (hf : Valid f) :
 0 ≤ graphDefect f := by
 have hv : (0 : ℝ) ≤ defect f (0,0) := defect_nonneg hf (0,0)
 exact hv.trans (Finset.le_sup' (f := defect f) (Finset.mem_univ (0,0)))

theorem D_witness_le : D 3 1 2 ≤ 5/3 := by
 have hb : BddBelow {x : ℝ | ∃ f : Coloring 3 1 2, Valid f ∧ graphDefect f = x} := by
  refine ⟨0, ?_⟩
  rintro x ⟨f,hf,rfl⟩
  exact graphDefect_nonneg hf
 exact (csInf_le hb ⟨witness,witness_valid,rfl⟩).trans graphDefect_witness_le

theorem D_strict_counterexample : D 3 1 2 < predicted 3 1 2 := by
 have h := D_witness_le
 norm_num [predicted]
 linarith

theorem literal_minimum_refuted : ¬ MinimumDefect 3 1 2 2 := by
 intro h
 have hle : (2:ℝ) ≤ graphDefect witness := h.2 ⟨witness, witness_valid, rfl⟩
 have hbound := graphDefect_witness_le
 norm_num at *
 linarith

theorem source_conjecture_false : ¬ SourceConjecture := by
 intro h
 have hx := h 3 1 2
 norm_num [predicted] at hx
 exact literal_minimum_refuted hx

def NumericalSourceConjecture : Prop := ∀ m a k : ℕ, D m a k = predicted m a k

theorem numerical_source_conjecture_false : ¬ NumericalSourceConjecture := by
 intro h
 exact (ne_of_lt D_strict_counterexample) (h 3 1 2)

#print axioms witness_valid
#print axioms witness_defects
#print axioms graphDefect_witness_le
#print axioms D_eq_of_minimum
#print axioms defect_nonneg
#print axioms graphDefect_nonneg
#print axioms D_witness_le
#print axioms D_strict_counterexample
#print axioms literal_minimum_refuted
#print axioms source_conjecture_false
#print axioms numerical_source_conjecture_false
end FractionalDefect
