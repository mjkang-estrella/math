import Counterexample

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace KuTorus
open scoped BigOperators
open Fin.NatCast

def sumSquares (k : ℕ) : ℤ := ∑ i ∈ Finset.range k, (i : ℤ)^2

theorem sumSquares_formula (k : ℕ) :
    6 * sumSquares k = (k : ℤ) * ((k : ℤ)-1) * (2*(k : ℤ)-1) := by
  induction k with
  | zero => simp [sumSquares]
  | succ k ih =>
    simp only [sumSquares, Finset.sum_range_succ] at *
    push_cast
    nlinarith

theorem mod_sumSquares (k : ℕ) [NeZero k] :
    (∑ a : ZMod k, a^2) = (sumSquares k : ZMod k) := by
  rw [← (ZMod.finEquiv k).toEquiv.sum_comp]
  simp only [sumSquares, Int.cast_sum, Int.cast_pow, Int.cast_natCast]
  have he (i : Fin k) : (ZMod.finEquiv k) i = (i.val : ZMod k) := by
    cases k with
    | zero => exact Fin.elim0 i
    | succ k =>
      change i = (Nat.cast (i.val) : Fin (k+1))
      exact (Fin.cast_val_eq_self i).symm
  change (∑ i : Fin k, ((ZMod.finEquiv k) i)^2) = _
  simpa only [he] using Fin.sum_univ_eq_sum_range (fun i => (i : ZMod k)^2) k

theorem sumSquares_obstruction (k : ℕ) [NeZero k] (hk3 : 3 ∣ k) :
    (4 : ZMod k) * (∑ a : ZMod k, a^2) ≠ 0 := by
  intro h
  rw [mod_sumSquares] at h
  have hd : (k : ℤ) ∣ 4 * sumSquares k :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by push_cast; exact h)
  obtain ⟨q, hq⟩ := hd
  have hk : (k : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne k)
  have he : (k : ℤ) * (3*q) =
      (k : ℤ) * (2*((k : ℤ)-1)*(2*(k : ℤ)-1)) := by
    nlinarith [sumSquares_formula k]
  have he' := mul_left_cancel₀ hk he
  obtain ⟨m, hm⟩ := hk3
  subst k
  have hexp : 3*q = 3*(12*(m : ℤ)^2-6*(m : ℤ))+2 := by
    push_cast at he'
    nlinarith [he']
  omega

theorem fiber_sum {k : ℕ} [NeZero k] (A : Finset (Board k))
    (f : Board k → ZMod k) (g : ZMod k → ZMod k)
    (hc : ∀ a, (A.filter (fun z => f z = a)).card = 2) :
    (∑ z ∈ A, g (f z)) = 2 * ∑ a, g a := by
  rw [← Finset.sum_fiberwise A f]
  calc
    _ = ∑ a : ZMod k, ∑ _z ∈ A.filter (fun z => f z = a), g a := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro z hz
      rw [(Finset.mem_filter.mp hz).2]
    _ = _ := by simp [hc, Finset.mul_sum]

def UniformTwo {k : ℕ} [NeZero k] (A : Finset (Board k)) : Prop :=
  (∀ a, (A.filter (fun z => z.1 = a)).card = 2) ∧
  (∀ a, (A.filter (fun z => z.2 = a)).card = 2) ∧
  (∀ a, (A.filter (fun z => z.1 + z.2 = a)).card = 2) ∧
  (∀ a, (A.filter (fun z => z.1 - z.2 = a)).card = 2)

theorem no_uniform_two (k : ℕ) [NeZero k] (hk3 : 3 ∣ k)
    (A : Finset (Board k)) : ¬ UniformTwo A := by
  rintro ⟨hx, hy, hs, hd⟩
  have h1 := fiber_sum A (fun z => z.1) (fun a => a^2) hx
  have h2 := fiber_sum A (fun z => z.2) (fun a => a^2) hy
  have h3 := fiber_sum A (fun z => z.1+z.2) (fun a => a^2) hs
  have h4 := fiber_sum A (fun z => z.1-z.2) (fun a => a^2) hd
  have hp : (∑ z ∈ A, (z.1+z.2)^2) + (∑ z ∈ A, (z.1-z.2)^2) =
      2*(∑ z ∈ A, z.1^2) + 2*(∑ z ∈ A, z.2^2) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [h1, h2, h3, h4] at hp
  exact sumSquares_obstruction k hk3 (by linear_combination -hp)

end KuTorus
