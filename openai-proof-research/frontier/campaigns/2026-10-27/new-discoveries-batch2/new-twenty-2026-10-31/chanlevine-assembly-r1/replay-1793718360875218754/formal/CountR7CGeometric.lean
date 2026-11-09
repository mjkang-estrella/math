import CountR7CZero
import Mathlib.RingTheory.PowerSeries.WellKnown
noncomputable section
open scoped BigOperators
namespace ChanLevine.Round7C
open Round6 Round3
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]
variable {F : Type*} [Field F]

/-- Exact-total bounded chip vectors are the usual finitely supported antidiagonal. -/
def chipAntidiagEquiv (m : ℕ) : BoundedChips n m ≃
    ↥(Finset.finsuppAntidiag (Finset.univ : Finset (ZMod n)) m) where
  toFun x := ⟨Finsupp.equivFunOnFinite.symm (fun v => (x.val v).val), by
    simpa using x.property⟩
  invFun l := ⟨fun v => ⟨l.val v, by
    have hl := (Finset.mem_finsuppAntidiag.mp l.property).1
    change (∑ u, l.val u) = m at hl
    have hb := Finset.single_le_sum (fun u _ => Nat.zero_le (l.val u)) (Finset.mem_univ v)
    omega⟩, by simpa using (Finset.mem_finsuppAntidiag.mp l.property).1⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv l := by apply Subtype.ext; exact Finsupp.equivFunOnFinite.symm_apply_apply l.val

def chipSeries (z : F) (s : Finset (ZMod n)) : PowerSeries F :=
  ∏ v, if v ∈ s ∪ rightEnds s then 1 else PowerSeries.mk (fun a => (z^v.val)^a)

theorem chipSeries_coeff (z : F) (s : Finset (ZMod n)) (m : ℕ) :
    PowerSeries.coeff m (chipSeries z s) = chipSum z s m := by
  rw [chipSeries, PowerSeries.coeff_prod, ← Finset.sum_coe_sort]
  rw [← (chipAntidiagEquiv (n := n) m).sum_comp]
  unfold chipSum
  apply Finset.sum_congr rfl
  intro x _
  change (∏ v, PowerSeries.coeff ((x.val v).val)
    (if v ∈ s ∪ rightEnds s then (1 : PowerSeries F) else
      PowerSeries.mk (fun a => (z^v.val)^a))) = _
  by_cases hx : ∀ v ∈ s ∪ rightEnds s, (x.val v).val = 0
  · rw [ite_eq_left hx, mul_one]
    apply Finset.prod_congr rfl
    intro v _
    by_cases hv : v ∈ s ∪ rightEnds s
    · simp [hv, hx v hv]
    · simp [hv, PowerSeries.coeff_mk]
  · rw [ite_eq_right hx, mul_zero]
    push Not at hx
    obtain ⟨v,hv,hx⟩ := hx
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    simp [hv, PowerSeries.coeff_one, hx]


theorem geometric_cancel (a : F) :
    (1 - PowerSeries.X * PowerSeries.C a) * PowerSeries.mk (fun j => a^j) = 1 := by
  have h := congrArg (PowerSeries.rescale a) (PowerSeries.mk_one_mul_one_sub_eq_one F)
  have he : PowerSeries.rescale a (PowerSeries.mk (1 : ℕ → F)) =
      PowerSeries.mk (fun j => a^j) := by
    ext j
    simp [PowerSeries.coeff_rescale, PowerSeries.coeff_mk]
  rw [map_mul, he, map_sub, map_one, PowerSeries.rescale_X] at h
  simpa [mul_comm] using h

theorem denominator_prod (z : F) :
    denominator z n = ∏ v : ZMod n, (1-Polynomial.X*Polynomial.C (z^v.val)) := by
  have h (r : ℕ) : denominator z r =
      ∏ j ∈ Finset.range r, (1-Polynomial.X*Polynomial.C (z^j)) := by
    induction r with
    | zero => simp [denominator, orderedProduct]
    | succ r ih =>
      change denominator z r * _ = _
      rw [Finset.prod_range_succ, ih]
  rw [h, ← Fin.prod_univ_eq_prod_range]
  apply Fintype.prod_equiv (ZMod.finEquiv n).toEquiv
  intro v
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ r => rfl

theorem coe_prod {V : Type*} (t : Finset V) (f : V → Polynomial F) :
    ((∏ v ∈ t, f v : Polynomial F) : PowerSeries F) = ∏ v ∈ t, (f v : PowerSeries F) :=
  map_prod Polynomial.coeToPowerSeries.ringHom f t

theorem chipSeries_cancel (z : F) (s : Finset (ZMod n)) :
    (denominator z n : PowerSeries F) * chipSeries z s =
      ((∏ v ∈ s ∪ rightEnds s, (1-Polynomial.X*Polynomial.C (z^v.val)) : Polynomial F) : PowerSeries F) := by
  rw [denominator_prod, chipSeries]
  simp only [coe_prod, Polynomial.coe_sub, Polynomial.coe_one,
    Polynomial.coe_mul, Polynomial.coe_X, Polynomial.coe_C]
  rw [← Finset.prod_mul_distrib]
  have he : ∀ v : ZMod n,
      (1-PowerSeries.X*PowerSeries.C (z^v.val)) *
        (if v ∈ s ∪ rightEnds s then 1 else PowerSeries.mk (fun a => (z^v.val)^a)) =
      if v ∈ s ∪ rightEnds s then (1-PowerSeries.X*PowerSeries.C (z^v.val)) else 1 := by
    intro v
    by_cases hv : v ∈ s ∪ rightEnds s
    · simp [hv]
    · simp only [hv, ite_false, geometric_cancel]
  simp_rw [he]
  exact Finset.prod_ite_mem_eq _ _

/-- Geometric cancellation for every selected endpoint set, before the matching sum. -/
theorem chip_convolution (z : F) (s : Finset (ZMod n)) (m : ℕ) :
    (∏ v ∈ s ∪ rightEnds s, (1-Polynomial.X*Polynomial.C (z^v.val)) : Polynomial F).coeff m =
      ∑ i : Fin (m+1), (denominator z n).coeff (m-i.val) * chipSum z s i.val := by
  have h := congrArg (PowerSeries.coeff m) (chipSeries_cancel z s)
  rw [Polynomial.coeff_coe] at h
  rw [← h, PowerSeries.coeff_mul]
  rw [← Finset.Nat.sum_antidiagonal_swap, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.coeff_coe, chipSeries_coeff]
  -- The standard antidiagonal order is reversed to match the frozen convolution.
  rfl
end ChanLevine.Round7C
