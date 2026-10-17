/- Copyright 2026 Myeongjin Kang. MIT.
Scoped finite, relational, linear and integer support for AGM063.
No Fano classification, virtual cycle or quotient-existence axiom is introduced.
-/
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic

open scoped BigOperators
namespace AGM063

section Degree
variable {ι : Type*}

/-- Exact conversion of the two finite degree budgets, with actual cardinality. -/
theorem sum_excess_identity (s : Finset ι) (d : ι → ℤ) (i : ℤ) :
    ∑ a ∈ s, (d a - i) = (∑ a ∈ s, (d a - 1)) - (s.card : ℤ) * (i - 1) := by
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

theorem sum_excess_le_one (s : Finset ι) (d : ι → ℤ) (i : ℤ)
    (h : ∑ a ∈ s, (d a - 1) ≤ (s.card : ℤ) * (i - 1) + 1) :
    ∑ a ∈ s, (d a - i) ≤ 1 := by
  rw [sum_excess_identity]
  linarith

/-- Nonnegativity of every excess prevents one degree consuming more than the budget. -/
theorem degree_le_successor (s : Finset ι) (d : ι → ℤ) (i : ℤ)
    (hmin : ∀ a ∈ s, i ≤ d a) (hbudget : ∑ a ∈ s, (d a - i) ≤ 1)
    (a : ι) (ha : a ∈ s) : d a ≤ i + 1 := by
  have hsingle : d a - i ≤ ∑ b ∈ s, (d b - i) :=
    Finset.single_le_sum (fun b hb => sub_nonneg.mpr (hmin b hb)) ha
  linarith

theorem degree_strict_cutoff (s : Finset ι) (d : ι → ℤ) (i : ℤ)
    (hi : 2 ≤ i) (hmin : ∀ a ∈ s, i ≤ d a)
    (hbudget : ∑ a ∈ s, (d a - 1) ≤ (s.card : ℤ) * (i - 1) + 1)
    (a : ι) (ha : a ∈ s) : d a < 2 * i := by
  have h := degree_le_successor s d i hmin (sum_excess_le_one s d i hbudget) a ha
  omega

/-- The Fintype instance uses its true finite cardinality, with no independent r parameter. -/
theorem all_degrees_strict_cutoff [Fintype ι] (d : ι → ℤ) (i : ℤ)
    (hi : 2 ≤ i) (hmin : ∀ a, i ≤ d a)
    (hbudget : ∑ a, (d a - 1) ≤ (Fintype.card ι : ℤ) * (i - 1) + 1) :
    ∀ a, d a < 2 * i := by
  classical
  intro a
  exact degree_strict_cutoff Finset.univ d i hi (by simpa using hmin)
    (by simpa using hbudget) a (Finset.mem_univ a)

/-- The numerical part of excluding two nonconstant components. -/
theorem strict_sum_card_le_one (s : Finset ι) (d : ι → ℤ) (i : ℤ)
    (hi : 0 < i) (hmin : ∀ a ∈ s, i ≤ d a)
    (hdegree : ∑ a ∈ s, d a < 2 * i) : s.card ≤ 1 := by
  have hsum : (s.card : ℤ) * i ≤ ∑ a ∈ s, d a := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hmin
  by_contra h
  have hc : (2 : ℤ) ≤ s.card := by exact_mod_cast (by omega : 2 ≤ s.card)
  nlinarith

theorem strict_sum_card_eq_one (s : Finset ι) (d : ι → ℤ) (i : ℤ)
    (hne : s.Nonempty) (hi : 0 < i) (hmin : ∀ a ∈ s, i ≤ d a)
    (hdegree : ∑ a ∈ s, d a < 2 * i) : s.card = 1 := by
  have := strict_sum_card_le_one s d i hi hmin hdegree
  have := Finset.card_pos.mpr hne
  omega

/-- The numerical part of excluding a multiple cover. -/
theorem strict_multiple_eq_one (i d k : ℤ) (hi : 0 < i) (hd : i ≤ d)
    (hk : 1 ≤ k) (htotal : k * d < 2 * i) : k = 1 := by
  by_contra h
  have : 2 ≤ k := by omega
  nlinarith
end Degree

section Dimensions
/-- Dimension bookkeeping for r correspondences and r−1 matching diagonals. -/
theorem composed_dimension (r n s : ℤ) : r * n + s - (r - 1) * n = n + s := by ring

theorem composed_dimension_lower (r n s : ℤ) (hs : n - 1 ≤ s) :
    2 * n - 1 ≤ r * n + s - (r - 1) * n := by
  rw [composed_dimension]
  omega

/-- Exact integer dimension obstruction; no truncated natural subtraction. -/
theorem quotient_dimension_le_one (n b z : ℤ)
    (hlower : 2 * n - 1 ≤ z) (hupper : z ≤ max (2 * n - b) (2 * n - 2)) :
    b ≤ 1 := by omega
end Dimensions

section Relations
variable {X B ι : Type*}

/-- Both endpoint memberships agree on each related pair. -/
def Saturated (R : X → X → Prop) (U : Set X) : Prop :=
  ∀ ⦃x y⦄, R x y → (x ∈ U ↔ y ∈ U)

def relationPairs (R : X → X → Prop) : Set (X × X) := {p | R p.1 p.2}

/-- The quotient map is defined only on U; no extension to its complement is used. -/
def fiberPairs (U : Set X) (π : U → B) : Set (X × X) :=
  {p | ∃ hx : p.1 ∈ U, ∃ hy : p.2 ∈ U, π ⟨p.1, hx⟩ = π ⟨p.2, hy⟩}

/-- One-way preservation suffices when the generating relation is symmetric. -/
theorem saturated_of_symmetric (R : X → X → Prop) (U : Set X)
    (hsym : ∀ x y, R x y → R y x)
    (hpres : ∀ x y, R x y → x ∈ U → y ∈ U) : Saturated R U := by
  intro x y hxy
  exact ⟨hpres x y hxy, hpres y x (hsym x y hxy)⟩

theorem saturated_pair_decomposition (R : X → X → Prop) (U : Set X)
    (hU : Saturated R U) :
    relationPairs R ⊆ (relationPairs R ∩ (U ×ˢ U)) ∪ (Uᶜ ×ˢ Uᶜ) := by
  rintro ⟨x,y⟩ hxy
  by_cases hx : x ∈ U
  · exact Or.inl ⟨hxy, hx, (hU hxy).mp hx⟩
  · exact Or.inr ⟨hx, fun hy => hx ((hU hxy).mpr hy)⟩

theorem saturated_fiber_decomposition (R : X → X → Prop) (U : Set X) (π : U → B)
    (hU : Saturated R U) (hπ : ∀ x y : U, R x y → π x = π y) :
    relationPairs R ⊆ fiberPairs U π ∪ (Uᶜ ×ˢ Uᶜ) := by
  rintro ⟨x,y⟩ hxy
  by_cases hx : x ∈ U
  · have hy := (hU hxy).mp hx
    exact Or.inl ⟨hx, hy, hπ ⟨x,hx⟩ ⟨y,hy⟩ hxy⟩
  · exact Or.inr ⟨hx, fun hy => hx ((hU hxy).mpr hy)⟩

/-- Arbitrary support contained in the relation inherits the two-endpoint inclusion. -/
theorem supported_fiber_decomposition (Z : Set (X × X)) (R : X → X → Prop)
    (U : Set X) (π : U → B) (hZ : Z ⊆ relationPairs R)
    (hU : Saturated R U) (hπ : ∀ x y : U, R x y → π x = π y) :
    Z ⊆ fiberPairs U π ∪ (Uᶜ ×ˢ Uᶜ) :=
  hZ.trans (saturated_fiber_decomposition R U π hU hπ)

def Generates (G : ι → X → X → Prop) (x y : X) : Prop := ∃ a, G a x y

def Chain (G : ι → X → X → Prop) : X → X → Prop :=
  Relation.ReflTransGen (Generates G)

def Preserves (R : X → X → Prop) (F : Set X) : Prop :=
  ∀ ⦃x y⦄, R x y → x ∈ F → y ∈ F

/-- Induction over the genuine reflexive transitive closure. -/
theorem reflTransGen_preserves (R : X → X → Prop) (F : Set X)
    (h : Preserves R F) : Preserves (Relation.ReflTransGen R) F := by
  intro x y hxy hx
  induction hxy with
  | refl => exact hx
  | tail hxy hyz ih => exact h hyz ih

theorem chain_preserves (G : ι → X → X → Prop) (F : Set X)
    (h : ∀ a, Preserves (G a) F) : Preserves (Chain G) F := by
  apply reflTransGen_preserves
  rintro x y ⟨a, hxy⟩ hx
  exact h a hxy hx

/-- A nonempty proper invariant subset contradicts universal chain connectedness. -/
theorem no_full_chain_connection (G : ι → X → X → Prop) (F : Set X)
    (hin : F.Nonempty) (hout : Fᶜ.Nonempty) (h : ∀ a, Preserves (G a) F) :
    ¬ (∀ x y, Chain G x y) := by
  rintro hall
  obtain ⟨x,hx⟩ := hin
  obtain ⟨y,hy⟩ := hout
  exact hy (chain_preserves G F h (hall x y) hx)

/-- Under full connectivity some generating family must cross any nontrivial subset. -/
theorem exists_generator_escape (G : ι → X → X → Prop) (F : Set X)
    (hin : F.Nonempty) (hout : Fᶜ.Nonempty) (hall : ∀ x y, Chain G x y) :
    ∃ a x y, x ∈ F ∧ y ∉ F ∧ G a x y := by
  classical
  by_contra h
  apply no_full_chain_connection G F hin hout _ hall
  intro a x y hxy hx
  by_contra hy
  exact h ⟨a,x,y,hx,hy,hxy⟩
end Relations

section Span
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Vanishing on a spanning set forces a real linear functional to vanish everywhere.
The statement needs no finite-dimensional assumption. -/
theorem functional_zero_of_span (L : V →ₗ[ℝ] ℝ) (S : Set V)
    (hspan : Submodule.span ℝ S = ⊤) (hzero : ∀ v ∈ S, L v = 0) : L = 0 := by
  exact (Submodule.linearMap_eq_zero_iff_of_span_eq_top L hspan).mpr
    (fun v => hzero v v.property)

/-- The representative classes form an actual finite set. -/
theorem finite_span_nonzero_contradiction (L : V →ₗ[ℝ] ℝ) (s : Finset V)
    (hspan : Submodule.span ℝ (s : Set V) = ⊤)
    (hzero : ∀ v ∈ s, L v = 0) (w : V) (hw : L w ≠ 0) : False := by
  have hz := functional_zero_of_span L (s : Set V) hspan hzero
  exact hw (by rw [hz]; rfl)

/-- A positive ample-intersection value supplies the required nonzero witness. -/
theorem finite_span_positive_contradiction (L : V →ₗ[ℝ] ℝ) (s : Finset V)
    (hspan : Submodule.span ℝ (s : Set V) = ⊤)
    (hzero : ∀ v ∈ s, L v = 0) (w : V) (hw : 0 < L w) : False :=
  finite_span_nonzero_contradiction L s hspan hzero w (ne_of_gt hw)
end Span

section InductionArithmetic
/-- Positivity of the base dimension. -/
theorem base_dimension_positive (n r i : ℤ) (hr : 2 ≤ r) (hi : 2 ≤ i)
    (hlower : r * (i - 1) ≤ n) : 0 < n - i + 1 := by nlinarith

/-- Induction at the base's actual, potentially larger, pseudoindex. -/
theorem base_defect_inequality (n r i j : ℤ) (hr : 2 ≤ r) (hji : i ≤ j)
    (hupper : n - 1 ≤ r * (i - 1)) :
    (n - i + 1) - 1 ≤ (r - 1) * (j - 1) := by nlinarith

theorem picard_decreases (r : ℤ) (hr : 2 ≤ r) : 1 ≤ r - 1 ∧ r - 1 < r := by omega

/-- S1 on the base and the defect-one budget leave at most one unit of increase. -/
theorem pseudoindex_increase_budget (n r i j : ℤ)
    (hupper : n ≤ r * (i - 1) + 1)
    (hbase : (r - 1) * (j - 1) ≤ n - i + 1) :
    (r - 1) * (j - i) ≤ 1 := by nlinarith

theorem pseudoindex_eq_of_rank_ge_three (r i j : ℤ) (hr : 3 ≤ r)
    (hji : i ≤ j) (hbudget : (r - 1) * (j - i) ≤ 1) : j = i := by
  by_contra h
  have : i + 1 ≤ j := by omega
  nlinarith

theorem pseudoindex_rank_two (i j : ℤ) (hji : i ≤ j)
    (hbudget : (2 - 1) * (j - i) ≤ 1) : j = i ∨ j = i + 1 := by omega

/-- Arithmetic translating a lower Picard parameter into the exceptional actual-r equality case. -/
theorem parameterized_exception (n r r₀ i : ℤ) (hi : 2 ≤ i)
    (hexcess : r₀ < r) (hsource : r * (i - 1) ≤ n)
    (hparam : n - 1 ≤ r₀ * (i - 1)) :
    i = 2 ∧ r = r₀ + 1 ∧ n = r := by
  have hr : 1 ≤ r - r₀ := by omega
  have hprod : (r - r₀) * (i - 1) ≤ 1 := by nlinarith
  have heqi : i = 2 := by nlinarith
  subst i
  constructor
  · rfl
  · constructor <;> nlinarith
end InductionArithmetic
end AGM063
