import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators
namespace WheelFormal

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Independent finite vertex subsets, with the empty set included. -/
def Independent (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∀ u ∈ s, ∀ v ∈ s, u ≠ v → ¬ G.Adj u v

noncomputable instance independentFintype (G : SimpleGraph V) :
    Fintype {s : Finset V // Independent G s} := Fintype.ofFinite _

/-- A literal fractional colouring: nonnegative weights on all independent subsets. -/
structure FractionalColouring (G : SimpleGraph V) where
  weight : {s : Finset V // Independent G s} → ℝ
  nonnegative : ∀ s, 0 ≤ weight s
  coverage : ∀ v, 1 ≤ ∑ s, if v ∈ s.val then weight s else 0

noncomputable def FractionalColouring.total {G : SimpleGraph V}
    (c : FractionalColouring G) : ℝ := ∑ s, c.weight s

/-- Infimum of total weights of all literal fractional colourings. -/
noncomputable def fracChromatic (G : SimpleGraph V) : ℝ :=
  sInf (Set.range (fun c : FractionalColouring G => c.total))

def rimAdj (m : ℕ) (a b : ZMod m) : Prop :=
  a ≠ b ∧ (b = a + 1 ∨ a = b + 1)

def wheel (m : ℕ) : SimpleGraph (Option (ZMod m)) where
  Adj a b := match a, b with
    | none, none => False
    | none, some _ => True
    | some _, none => True
    | some i, some j => rimAdj m i j
  symm := ⟨by
    intro a b h
    cases a <;> cases b <;> simp_all [rimAdj, ne_comm, or_comm]⟩
  loopless := ⟨by
    intro a
    cases a <;> simp [rimAdj]⟩

/-- The actual Cartesian square, using mathlib's box product. -/
def wheelSquare (t : ℕ) := (wheel (2*t+1)).boxProd (wheel (2*t+1))

/-- Exact target proposition; no proof of this proposition is claimed here. -/
def Target : Prop := ∀ t : ℕ, 1 ≤ t →
  fracChromatic (wheelSquare t) =
    (6*(t:ℝ)^2+7*(t:ℝ)+3)/(2*(t:ℝ)^2+(t:ℝ)+1)

 theorem total_nonnegative {G : SimpleGraph V} (c : FractionalColouring G) :
    0 ≤ c.total := Finset.sum_nonneg (fun s _ => c.nonnegative s)

/-- The finite double count needed for the weighted lower bound. -/
theorem coverage_double_count (G : SimpleGraph V) (c : FractionalColouring G)
    (w : V → ℝ) :
    (∑ v, w v * (∑ s, if v ∈ s.val then c.weight s else 0)) =
    ∑ s, c.weight s * (∑ v ∈ s.val, w v) := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  apply Finset.sum_congr rfl
  intro v _
  exact mul_comm _ _

/-- Weak duality proved directly, without linear programming duality. -/
theorem weighted_lower (G : SimpleGraph V) (c : FractionalColouring G)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (C : ℝ)
    (bound : ∀ s : {s : Finset V // Independent G s}, (∑ v ∈ s.val, w v) ≤ C) :
    (∑ v, w v) ≤ C * c.total := by
  classical
  calc
    (∑ v, w v) ≤ ∑ v, w v * (∑ s, if v ∈ s.val then c.weight s else 0) := by
      apply Finset.sum_le_sum
      intro v _
      simpa using mul_le_mul_of_nonneg_left (c.coverage v) (hw v)
    _ = ∑ s, c.weight s * (∑ v ∈ s.val, w v) := coverage_double_count G c w
    _ ≤ ∑ s, c.weight s * C := by
      exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (bound s) (c.nonnegative s)
    _ = C * c.total := by simp [FractionalColouring.total, Finset.mul_sum, mul_comm]

/-- Singleton independent set, available in every simple graph. -/
def singletonSet (G : SimpleGraph V) (v : V) : {s : Finset V // Independent G s} :=
  ⟨{v}, by
    intro u hu z hz hn
    simp only [Finset.mem_singleton] at hu hz
    exact (hn (hu.trans hz.symm)).elim⟩

/-- Explicit feasible colouring, not claimed to attain the wheel formula. -/
noncomputable def singletonColouring (G : SimpleGraph V) : FractionalColouring G where
  weight s := if s.val.card = 1 then 1 else 0
  nonnegative s := by split <;> norm_num
  coverage v := by
    classical
    have h := Finset.single_le_sum
      (s := (Finset.univ : Finset {s : Finset V // Independent G s}))
      (f := fun s => if v ∈ s.val then (if s.val.card = 1 then (1:ℝ) else 0) else 0)
      (by intro i _; split <;> positivity) (Finset.mem_univ (singletonSet G v))
    simpa [singletonSet] using h

theorem feasible_nonempty (G : SimpleGraph V) :
    (Set.range (fun c : FractionalColouring G => c.total)).Nonempty :=
  ⟨_, ⟨singletonColouring G, rfl⟩⟩

theorem total_bddBelow (G : SimpleGraph V) :
    BddBelow (Set.range (fun c : FractionalColouring G => c.total)) :=
  ⟨0, by rintro _ ⟨c, rfl⟩; exact total_nonnegative c⟩

theorem fracChromatic_nonnegative (G : SimpleGraph V) : 0 ≤ fracChromatic G :=
  le_csInf (feasible_nonempty G) (by rintro _ ⟨c, rfl⟩; exact total_nonnegative c)

theorem fracChromatic_le_total (G : SimpleGraph V) (c : FractionalColouring G) :
    fracChromatic G ≤ c.total :=
  csInf_le (total_bddBelow G) ⟨c, rfl⟩

theorem weighted_lower_inf (G : SimpleGraph V) (w : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) (C : ℝ) (hC : 0 < C)
    (bound : ∀ s : {s : Finset V // Independent G s}, (∑ v ∈ s.val, w v) ≤ C) :
    (∑ v, w v) / C ≤ fracChromatic G := by
  apply le_csInf (feasible_nonempty G)
  rintro _ ⟨c, rfl⟩
  rw [div_le_iff₀ hC]
  simpa [mul_comm] using weighted_lower G c w hw C bound

/-- The exact factorization used in the two-sided deletion case. -/
theorem two_sided_arithmetic (t a b : ℝ) (ha : 1 ≤ a) (hat : a ≤ t)
    (hb : 1 ≤ b) (hbt : b ≤ t) :
    2*t - (t+1)*(a+b) + 2*a*b ≤ 0 := by
  have h₁ := mul_nonneg (sub_nonneg.mpr hat) (sub_nonneg.mpr hb)
  have h₂ := mul_nonneg (sub_nonneg.mpr hbt) (sub_nonneg.mpr ha)
  nlinarith
end WheelFormal
