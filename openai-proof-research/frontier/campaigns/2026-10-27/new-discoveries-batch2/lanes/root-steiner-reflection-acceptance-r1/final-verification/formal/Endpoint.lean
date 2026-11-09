import Contraction
import SourceMinimum
import Algebra
set_option autoImplicit false
namespace SteinerReflection
open scoped BigOperators
noncomputable section
/-- Source tensor, defined from a genuine connected-subgraph minimum. -/
def sourceM (i j k h : V) : ℝ := sourceDistance ![i,j,k,h]
def sourceC (i j k l : V) : ℝ := ∑ h, sourceM i j k h * A h l
def sourceH (v : V → ℝ) (i : V) : ℝ :=
  ∑ j, ∑ k, ∑ l, sourceC i j k l*v j*v k*v l
lemma sourceH_eq (v : V → ℝ) (i : V) : sourceH v i = H v i := by
  simp only [sourceH,sourceC,sourceM,sourceDistance_eq,H,C,M]
lemma A_literal (h l : V) : A h l = 2/(30:ℝ)-(if h = l then 1 else 0) := by
  classical
  simp only [A,delta,eq_comm]
  norm_num
/-- Concrete negative H-eigenpair of the literal first-free-index, last-slot-reflected tensor.
There are no graph, contraction, or root-existence hypotheses. -/
theorem concrete_negative_H_pair : ∃ s lam : ℝ,
    5 < s ∧ s < 8 ∧ x s ≠ 0 ∧ lam < 0 ∧
    ∀ i : V, sourceH (x s) i = lam*(x s i)^3 := by
  obtain ⟨s,lam,h5,h8,hn,hc,hl⟩ := algebraic_witness
  refine ⟨s,lam,h5,h8,?_,hn,?_⟩
  · intro he
    have hh := congrFun he (1:V)
    norm_num [x] at hh
  · intro i
    rw [sourceH_eq,orbit_contraction]
    obtain ⟨hd,he⟩ := cubic_identities s
    by_cases hi : i = 0
    · simp only [hi,ite_true,x]
      rw [hd]; exact hc
    · simp only [hi,ite_false,x]
      rw [he]; exact hl
/-- Refutation of positivity for this genuine source tree, hence sufficient to refute
any universal all-tree order-four positivity assertion. -/
def StarHPositivity : Prop := ∀ (v : V → ℝ) (lam : ℝ), v ≠ 0 →
  (∀ i, sourceH v i = lam*(v i)^3) → 0 < lam
theorem source_refutation : (SimpleGraph.starGraph (0:V)).IsTree ∧ ¬StarHPositivity := by
  refine ⟨star_tree,?_⟩
  intro hp
  obtain ⟨s,lam,_,_,hx,hn,he⟩ := concrete_negative_H_pair
  exact (not_lt_of_ge hn.le) (hp (x s) lam hx he)
end
end SteinerReflection
