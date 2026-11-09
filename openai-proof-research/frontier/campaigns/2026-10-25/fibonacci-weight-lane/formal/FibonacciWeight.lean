import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.GroupTheory.Index
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Mathlib.Data.Fintype.Quotient
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
Weight preservation for recurrence periods (MathDB 371201).
The orbit-fiber counting argument is due to Shivam Patel, posted 2026-08-20.
Periods are actual SameCycle quotient classes, including fixed points.
-/
namespace FibonacciWeight
open scoped BigOperators
open Classical
attribute [local instance] propDecidable

abbrev Period {X : Type*} (T : Equiv.Perm X) :=
  Quotient (Equiv.Perm.SameCycle.setoid T)

def periodOf {X : Type*} (T : Equiv.Perm X) (x : X) : Period T :=
  Quotient.mk _ x

noncomputable def orbitSize {X : Type*} [Fintype X] (T : Equiv.Perm X)
    (q : Period T) : ℕ := by
  classical
  exact (Finset.univ.filter fun x => periodOf T x = q).card

/-- Equality of quotient periods is exactly equality after a forward time shift. -/
theorem period_eq_iff_iterate {X : Type*} [Fintype X] (T : Equiv.Perm X) (x y : X) :
    periodOf T x = periodOf T y ↔ ∃ n : ℕ, (T^[n]) x = y := by
  constructor
  · intro h
    obtain ⟨n, _, _, hn⟩ := (Quotient.exact h).exists_pow_eq T
    exact ⟨n, by simpa only [Equiv.Perm.coe_pow] using hn⟩
  · rintro ⟨n, hn⟩
    apply Quotient.sound
    change T.SameCycle x y
    have h : T.SameCycle x ((T ^ n) x) := Equiv.Perm.SameCycle.rfl.pow_right
    simpa only [Equiv.Perm.coe_pow, hn] using h

/-- Orbit cardinality equals the least positive return time, also for fixed points. -/
theorem orbitSize_eq_minimalPeriod {X : Type*} [Fintype X] (T : Equiv.Perm X) (x : X) :
    orbitSize T (periodOf T x) = Function.minimalPeriod T x := by
  classical
  let L := (List.range (Function.minimalPeriod T x)).map fun n => (T^[n]) x
  have hp := T.injective.mem_periodicPts x
  have hL : L.Nodup := Function.nodup_periodicOrbit (f := T) (x := x)
  have he : (Finset.univ.filter fun y => periodOf T y = periodOf T x) = L.toFinset := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
    change periodOf T y = periodOf T x ↔ y ∈ Function.periodicOrbit T x
    rw [Function.mem_periodicOrbit_iff hp, eq_comm, period_eq_iff_iterate]
  rw [orbitSize, he, List.toFinset_card_of_nodup hL]
  simp [L]

noncomputable def weight {X : Type*} [Fintype X] (T : Equiv.Perm X)
    (q : Period T) : ℚ := (orbitSize T q : ℚ) / Fintype.card X

theorem commute_pow {X Y : Type*} (T : Equiv.Perm X) (S : Equiv.Perm Y)
    (f : X → Y) (h : ∀ x, f (T x) = S (f x)) (n : ℕ) (x : X) :
    f ((T ^ n) x) = (S ^ n) (f x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ', Equiv.Perm.mul_apply, h, ih]

theorem map_sameCycle {X Y : Type*} [Fintype X] (T : Equiv.Perm X)
    (S : Equiv.Perm Y) (f : X → Y) (h : ∀ x, f (T x) = S (f x))
    {x y : X} (hxy : T.SameCycle x y) : S.SameCycle (f x) (f y) := by
  classical
  obtain ⟨n, _, _, hn⟩ := hxy.exists_pow_eq T
  rw [← hn, commute_pow T S f h]
  exact Equiv.Perm.SameCycle.rfl.pow_right

noncomputable def periodMap {X Y : Type*} [Fintype X] (T : Equiv.Perm X)
    (S : Equiv.Perm Y) (f : X → Y) (h : ∀ x, f (T x) = S (f x)) :
    Period T → Period S :=
  Quotient.map f (fun _ _ hxy => map_sameCycle T S f h hxy)

theorem periodMap_mk {X Y : Type*} [Fintype X] (T : Equiv.Perm X)
    (S : Equiv.Perm Y) (f : X → Y) (h : ∀ x, f (T x) = S (f x)) (x : X) :
    periodMap T S f h (periodOf T x) = periodOf S (f x) := rfl

/-- This is the orbit-decomposition bridge: the sum is over actual quotient orbits. -/
theorem orbit_sum_eq_preimage {X Y : Type*} [Fintype X] [Fintype Y]
    (T : Equiv.Perm X) (S : Equiv.Perm Y) (f : X → Y)
    (h : ∀ x, f (T x) = S (f x)) (q : Period S) :
    ∑ p ∈ Finset.univ.filter (fun p => periodMap T S f h p = q), orbitSize T p =
      (Finset.univ.filter fun x => periodOf S (f x) = q).card := by
  classical
  simpa only [orbitSize, Finset.mem_filter, Finset.mem_univ, true_and,
    periodMap_mk] using
    (Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset X)
      (Finset.univ.filter fun p => periodMap T S f h p = q) (periodOf T))

/-- A surjective homomorphism has constant-size fibers. -/
theorem uniform_fibers {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] (f : G →+ H) (hf : Function.Surjective f) (x y : H) :
    (Finset.univ.filter fun g => f g = x).card =
      (Finset.univ.filter fun g => f g = y).card := by
  classical
  exact AddMonoidHom.card_fiber_eq_of_mem_range f (hf x) (hf y)

/-- Count any inverse image by disjoint fibers, using the homomorphism's actual fibers. -/
theorem preimage_card {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (hf : Function.Surjective f)
    (A : Finset H) :
    (Finset.univ.filter fun g => f g ∈ A).card =
      A.card * (Finset.univ.filter fun g => f g = 0).card := by
  classical
  rw [← Finset.sum_card_fiberwise_eq_card_filter Finset.univ A f]
  calc
    ∑ y ∈ A, (Finset.univ.filter fun g => f g = y).card =
        ∑ _y ∈ A, (Finset.univ.filter fun g => f g = 0).card := by
      apply Finset.sum_congr rfl
      intro y _
      exact uniform_fibers f hf y 0
    _ = _ := by simp

theorem total_card {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (hf : Function.Surjective f) :
    Fintype.card G = Fintype.card H * (Finset.univ.filter fun g => f g = 0).card := by
  simpa using preimage_card f hf Finset.univ

/-- General weight preservation, with no orbit-size or fiber-size hypotheses. -/
theorem weight_preservation {G H : Type*} [AddGroup G] [AddGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (hf : Function.Surjective f)
    (T : Equiv.Perm G) (S : Equiv.Perm H) (h : ∀ x, f (T x) = S (f x))
    (q : Period S) :
    ∑ p ∈ Finset.univ.filter (fun p => periodMap T S f h p = q), weight T p =
      weight S q := by
  classical
  have hc := preimage_card f hf (Finset.univ.filter fun y => periodOf S y = q)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
  have hs : (∑ p ∈ Finset.univ.filter (fun p => periodMap T S f h p = q),
      orbitSize T p) = orbitSize S q * (Finset.univ.filter fun g => f g = 0).card :=
    (orbit_sum_eq_preimage T S f h q).trans hc
  have ht := total_card f hf
  have hG : (Fintype.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hH : (Fintype.card H : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [weight, ← Finset.sum_div, ← Nat.cast_sum]
  apply (div_eq_div_iff hG hH).2
  rw [hs, Nat.cast_mul, ht, Nat.cast_mul]
  ring

/-- Every upstairs orbit maps onto its entire downstairs orbit. -/
theorem orbit_maps_onto {X Y : Type*} [Fintype X] [Fintype Y]
    (T : Equiv.Perm X) (S : Equiv.Perm Y) (f : X → Y)
    (h : ∀ x, f (T x) = S (f x)) (x : X) (y : Y)
    (hy : periodOf S y = periodMap T S f h (periodOf T x)) :
    ∃ z, periodOf T z = periodOf T x ∧ f z = y := by
  classical
  have hc : S.SameCycle (f x) y := Quotient.exact hy.symm
  obtain ⟨n, _, _, hn⟩ := hc.exists_pow_eq S
  refine ⟨(T ^ n) x, ?_, ?_⟩
  · exact Quotient.sound Equiv.Perm.SameCycle.rfl.pow_left
  · rw [commute_pow T S f h, hn]

/-- The actual second-order recurrence, with its explicit inverse. -/
def recurrence (m : ℕ) (eps : ℤ) : Equiv.Perm (ZMod m × ZMod m) where
  toFun x := (x.2, x.1 + (eps : ZMod m) * x.2)
  invFun x := (x.2 - (eps : ZMod m) * x.1, x.1)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp

/-- Actual coordinatewise reduction, as an additive homomorphism. -/
def reduction {m d : ℕ} (hdm : d ∣ m) : (ZMod m × ZMod m) →+ (ZMod d × ZMod d) where
  toFun x := (ZMod.castHom hdm (ZMod d) x.1, ZMod.castHom hdm (ZMod d) x.2)
  map_zero' := by ext <;> simp
  map_add' x y := by
    exact Prod.ext ((ZMod.castHom hdm (ZMod d)).map_add x.1 y.1)
      ((ZMod.castHom hdm (ZMod d)).map_add x.2 y.2)

theorem reduction_surjective {m d : ℕ} (hdm : d ∣ m) :
    Function.Surjective (reduction hdm) := by
  intro y
  obtain ⟨a, ha⟩ := ZMod.castHom_surjective hdm y.1
  obtain ⟨b, hb⟩ := ZMod.castHom_surjective hdm y.2
  exact ⟨(a, b), Prod.ext ha hb⟩

theorem reduction_commutes {m d : ℕ} (hdm : d ∣ m) (eps : ℤ)
    (x : ZMod m × ZMod m) :
    reduction hdm (recurrence m eps x) = recurrence d eps (reduction hdm x) := by
  change (ZMod.castHom hdm (ZMod d) x.2,
    ZMod.castHom hdm (ZMod d) (x.1 + (eps : ZMod m) * x.2)) = _
  simp only [map_add, map_mul, map_intCast]
  rfl

theorem card_state (m : ℕ) [NeZero m] : Fintype.card (ZMod m × ZMod m) = m ^ 2 := by
  simp [Fintype.card_prod, ZMod.card, pow_two]

/-- The concrete reduction fibers have the expected square cardinality. -/
theorem reduction_fiber_card (m d : ℕ) [NeZero m] [NeZero d] (hdm : d ∣ m)
    (y : ZMod d × ZMod d) :
    (Finset.univ.filter fun x => reduction hdm x = y).card = (m / d) ^ 2 := by
  classical
  trans (Finset.univ.filter fun x : ZMod m × ZMod m => reduction hdm x = 0).card
  · convert uniform_fibers (reduction hdm) (reduction_surjective hdm) y 0 using 1 <;>
      congr 1 <;> ext x <;> simp
  · have ht := total_card (reduction hdm) (reduction_surjective hdm)
    rw [card_state, card_state] at ht
    apply Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (Nat.pos_of_ne_zero (NeZero.ne d)))
    calc
      d ^ 2 * (Finset.univ.filter fun x => reduction hdm x = 0).card = m ^ 2 := by
        convert ht.symm using 1
        congr 2
        ext x
        simp
      _ = (d * (m / d)) ^ 2 := by rw [Nat.mul_div_cancel' hdm]
      _ = d ^ 2 * (m / d) ^ 2 := mul_pow _ _ _

/-- In particular, the zero fixed point is a period of length one, not length zero. -/
theorem zero_period_length (m : ℕ) [NeZero m] (eps : ℤ) :
    orbitSize (recurrence m eps) (periodOf (recurrence m eps) (0, 0)) = 1 := by
  rw [orbitSize_eq_minimalPeriod, Function.minimalPeriod_eq_one_iff_isFixedPt]
  change recurrence m eps (0, 0) = (0, 0)
  simp [recurrence]

/-- MathDB371201 / Pudelko Conjecture 17, for every integer coefficient.
Taking eps = 1 and eps = -1 gives the two recurrences in the source. -/
theorem fibonacci_weight_preservation (m d : ℕ) [NeZero m] [NeZero d]
    (hdm : d ∣ m) (eps : ℤ) (q : Period (recurrence d eps)) :
    ∑ p ∈ Finset.univ.filter (fun p =>
      periodMap (recurrence m eps) (recurrence d eps) (reduction hdm)
        (reduction_commutes hdm eps) p = q),
      (orbitSize (recurrence m eps) p : ℚ) / (m : ℚ) ^ 2 =
      (orbitSize (recurrence d eps) q : ℚ) / (d : ℚ) ^ 2 := by
  simpa only [weight, card_state, Nat.cast_pow] using
    weight_preservation (reduction hdm) (reduction_surjective hdm)
      (recurrence m eps) (recurrence d eps) (reduction_commutes hdm eps) q

end FibonacciWeight
