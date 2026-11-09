import ASEPArcs
import Mathlib.GroupTheory.Perm.Fin

/-!
# Reviewer's own restatement of Conjecture 1 (arXiv:2506.10671v1, p. 14) and its refutation

Written independently from the source, formulas (2)-(4), (6), Definition 3 and Conjecture 1:
* coordinates are indexed by the arcs `A = {(i,j) : i ≠ j}` of `K_n` (`m = n(n-1)`), as in (6);
* every constraint sum is written as a sum over ALL arcs with an indicator weight (not a filtered sum);
* the cut range `2 ≤ |S| ≤ n - 2` is written without natural subtraction (`|S| + 2 ≤ n`);
* a face is a textbook (Ziegler) face: the intersection of `P` with the hyperplane of a valid inequality;
  two vertices are adjacent iff they are distinct and the segment joining them is such a face;
* a tour is the arc set of a cyclic listing `f 0 → f 1 → ⋯ → f (n-1) → f 0` of the nodes.
The conjecture quantifies over every `n ≥ 4`.  Only the author's `ASEP.arc_segment_not_face` and
`ASEP.xa_extreme` are used.
-/

namespace RV

open Finset

abbrev Arc (n : ℕ) := {p : Fin n × Fin n // p.1 ≠ p.2}

/-- `P_ASEP^n` (6) with (2), (3), (4) and `x ≥ 0`. -/
def P (n : ℕ) : Set (Arc n → ℝ) :=
  {x | (∀ a, 0 ≤ x a) ∧
       (∀ j : Fin n, ∑ a : Arc n, (if a.1.2 = j then x a else 0) = 1) ∧
       (∀ i : Fin n, ∑ a : Arc n, (if a.1.1 = i then x a else 0) = 1) ∧
       (∀ S : Finset (Fin n), 2 ≤ S.card ∧ S.card + 2 ≤ n →
          1 ≤ ∑ a : Arc n, (if a.1.1 ∈ S ∧ a.1.2 ∉ S then x a else 0))}

/-- Linear functional `c · x`. -/
def dot {n : ℕ} (c x : Arc n → ℝ) : ℝ := ∑ a : Arc n, c a * x a

/-- `F` is a face of `K` in the textbook sense: cut out by a valid inequality `c · y ≤ c₀`. -/
def IsFace {n : ℕ} (K F : Set (Arc n → ℝ)) : Prop :=
  ∃ c : Arc n → ℝ, ∃ c₀ : ℝ, (∀ y ∈ K, dot c y ≤ c₀) ∧ F = {y | y ∈ K ∧ dot c y = c₀}

def Vertex (n : ℕ) (x : Arc n → ℝ) : Prop := x ∈ Set.extremePoints ℝ (P n)

/-- Definition 3: `y ∈ N(x)` iff `x, y` are distinct vertices joined by an edge (a face equal to `[x, y]`). -/
def Adj (n : ℕ) (x y : Arc n → ℝ) : Prop :=
  Vertex n x ∧ Vertex n y ∧ x ≠ y ∧ IsFace (P n) (segment ℝ x y)

/-- A tour: the incidence vector of the directed Hamiltonian cycle listing the nodes as
`f 0, f 1, …, f (n-1)` (successor of `f k` is `f (k+1 mod n)`). -/
def Tour (n : ℕ) (t : Arc n → ℝ) : Prop :=
  ∃ f : Equiv.Perm (Fin n), t = fun a => if a.1.2 = f (finRotate n (f.symm a.1.1)) then 1 else 0

/-- Conjecture 1: for each vertex `x`, `N(x)` contains at least one tour (every `n ≥ 4`). -/
def Conjecture1 : Prop := ∀ n : ℕ, 4 ≤ n → ∀ x, Vertex n x → ∃ t, Tour n t ∧ Adj n x t

/-! ## Bridges to the author's definitions -/

lemma P_eq (n : ℕ) : P n = ASEP.arcPolytope n := by
  ext x
  simp only [P, ASEP.arcPolytope, Set.mem_ofPred_eq, ← Finset.sum_filter]
  constructor
  · rintro ⟨h0, h1, h2, h3⟩; exact ⟨h0, h1, h2, fun S a b => h3 S ⟨a, by omega⟩⟩
  · rintro ⟨h0, h1, h2, h3⟩; exact ⟨h0, h1, h2, fun S ⟨a, b⟩ => h3 S a (by omega)⟩

lemma dot_comb {n : ℕ} (c p q : Arc n → ℝ) (a b : ℝ) : dot c (a • p + b • q) = a * dot c p + b * dot c q := by
  simp only [dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl (fun _ _ => by ring)

/-- Textbook faces are extreme subsets. -/
lemma IsFace.isExtreme {n : ℕ} {K F : Set (Arc n → ℝ)} (h : IsFace K F) : IsExtreme ℝ K F := by
  obtain ⟨c, c₀, hv, rfl⟩ := h
  refine ⟨fun y hy => hy.1, fun p hp q hq z hz hzo => ?_⟩
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hzo
  have e := hz.2; rw [dot_comb] at e
  have h1 := hv p hp; have h2 := hv q hq
  have k1 := mul_nonneg ha.le (sub_nonneg.2 h1)
  have k2 := mul_nonneg hb.le (sub_nonneg.2 h2)
  have s0 : a * (c₀ - dot c p) + b * (c₀ - dot c q) = 0 := by linear_combination c₀ * hab - e
  have s1 : a * (c₀ - dot c p) = 0 := by linarith
  have s2 : b * (c₀ - dot c q) = 0 := by linarith
  have hp' : dot c p = c₀ := by
    rcases mul_eq_zero.1 s1 with h | h
    · exact absurd h ha.ne'
    · linarith
  have hq' : dot c q = c₀ := by
    rcases mul_eq_zero.1 s2 with h | h
    · exact absurd h hb.ne'
    · linarith
  exact ⟨hp, hp'⟩

/-- Every reviewer-tour is an author-tour (so the author's tour set is not too small). -/
lemma tour_to_arcTour (t : Arc 8 → ℝ) (ht : Tour 8 t) : ASEP.IsArcTour 8 t := by
  obtain ⟨f, rfl⟩ := ht
  refine ⟨f * finRotate 8 * f⁻¹, (isCycle_finRotate (n := 6)).conj, ?_, ?_⟩
  · rw [Equiv.Perm.support_conj, support_finRotate (n := 6), Finset.map_univ_equiv]
  · funext a
    have e : (f * finRotate 8 * f⁻¹) a.1.1 = f (finRotate 8 (f.symm a.1.1)) := rfl
    by_cases h : a.1.2 = f (finRotate 8 (f.symm a.1.1))
    · simp only [ASEP.arcTour, e, h]
    · simp only [ASEP.arcTour, e, h, Ne.symm h, ↓reduceIte]

/-- Tours exist (non-vacuity of the tour predicate on both sides). -/
lemma tour_exists : ∃ t, Tour 8 t ∧ ASEP.IsArcTour 8 t :=
  ⟨_, ⟨1, rfl⟩, tour_to_arcTour _ ⟨1, rfl⟩⟩

/-- The reviewer's restatement is refuted by the author's arc-space vertex `xa`. -/
theorem conjecture1_false : ¬ Conjecture1 := by
  intro h
  have hx : Vertex 8 ASEP.xa := by rw [Vertex, P_eq]; exact ASEP.xa_extreme
  obtain ⟨t, ht, -, -, -, hF⟩ := h 8 (by norm_num) ASEP.xa hx
  have hE : IsExtreme ℝ (ASEP.arcPolytope 8) (segment ℝ ASEP.xa t) := by
    rw [← P_eq]; exact hF.isExtreme
  exact ASEP.arc_segment_not_face t (tour_to_arcTour t ht) hE

/-- Stronger form actually delivered: `xa` is a vertex of the reviewer's `P 8` and no tour of
the reviewer's kind is joined to it by an extreme subset (Mathlib face) or a textbook face. -/
theorem counterexample :
    Vertex 8 ASEP.xa ∧ ∀ t, Tour 8 t →
      ¬ IsExtreme ℝ (P 8) (segment ℝ ASEP.xa t) ∧ ¬ IsFace (P 8) (segment ℝ ASEP.xa t) := by
  refine ⟨by rw [Vertex, P_eq]; exact ASEP.xa_extreme, fun t ht => ⟨?_, fun hF => ?_⟩⟩
  · rw [P_eq]; exact ASEP.arc_segment_not_face t (tour_to_arcTour t ht)
  · have := hF.isExtreme; rw [P_eq] at this
    exact ASEP.arc_segment_not_face t (tour_to_arcTour t ht) this

end RV

#print axioms RV.conjecture1_false
#print axioms RV.counterexample
