import Closure
import Endpoint
namespace Percolation
set_option autoImplicit false

def active5 (a : Infection 5) : Infection 5 := fun l => decide (5 ≤ countOn PG5 a l)
def spread5 (a i : Infection 5) : Infection 5 := fun p =>
  a p || (List.finRange 31).any (fun l => PG5.inc p l && i l)

theorem spread_active5 (a : Infection 5) : spread5 a (active5 a) = step PG5 5 a := rfl

-- All quantifiers here range over finite Boolean arrays or the 31 points.
-- No unbounded-time or proper-subset predicate occurs in this system.
def FiniteModel5 (a x i j : Infection 5) (b : Points 5 → Infection 5) : Prop :=
  i = active5 a ∧ x = spread5 a i ∧ j = active5 x ∧
  Full (spread5 x j) ∧ ¬ Full x ∧
  ∀ v, a v = true →
    (∀ p, p ≠ v → a p = true → b v p = true) ∧
    step PG5 5 (b v) = b v ∧ b v v = false

def FiniteSystemUnsat5 : Prop :=
  ¬ ∃ a x i j b, FiniteModel5 a x i j b

theorem witness_to_finite5 (a : Infection 5)
    (hm : Minimal PG5 5 a) (ht : TimeIs PG5 5 a 2) :
    FiniteModel5 a (step PG5 5 a) (active5 a) (active5 (step PG5 5 a))
      (fun v => rounds PG5 5 (erase a v) 31) := by
  refine ⟨rfl, rfl, rfl, ht.1, ht.2 1 (by decide), ?_⟩
  intro v hv
  exact minimal_deletion_separator PG5 5 a hm v hv

theorem finite5_to_witness (a x i j : Infection 5) (b : Points 5 → Infection 5)
    (h : FiniteModel5 a x i j b) : Minimal PG5 5 a ∧ TimeIs PG5 5 a 2 := by
  obtain ⟨hi, hx, hj, hfull, hnot, hb⟩ := h
  subst i
  subst j
  rw [spread_active5] at hx hfull
  subst x
  have hp : Percolates PG5 5 a := ⟨2, hfull⟩
  refine ⟨minimal_from_separators PG5 5 a hp (fun v hv => ⟨b v, hb v hv⟩), hfull, ?_⟩
  intro k hk hf
  have hk' : k = 0 ∨ k = 1 := by omega
  rcases hk' with rfl | rfl
  · exact hnot (fun p => step_inflation PG5 5 a p (hf p))
  · exact hnot hf

theorem finite5_iff_target :
    (∃ a x i j b, FiniteModel5 a x i j b) ↔
    ∃ a, Minimal PG5 5 a ∧ TimeIs PG5 5 a 2 := by
  constructor
  · rintro ⟨a, x, i, j, b, h⟩
    exact ⟨a, finite5_to_witness a x i j b h⟩
  · rintro ⟨a, hm, ht⟩
    exact ⟨a, _, _, _, _, witness_to_finite5 a hm ht⟩

theorem finite_unsat_iff_no_minimal : FiniteSystemUnsat5 ↔ NoMinimalTwoRound5 := by
  exact not_congr finite5_iff_target

theorem not_conjecture20_finite (h : FiniteSystemUnsat5) : ¬ Conjecture20 :=
  not_conjecture20 (finite_unsat_iff_no_minimal.mp h)

#print axioms closure_stable
#print axioms minimal_deletion_separator
#print axioms finite5_iff_target
#print axioms not_conjecture20_finite
end Percolation
