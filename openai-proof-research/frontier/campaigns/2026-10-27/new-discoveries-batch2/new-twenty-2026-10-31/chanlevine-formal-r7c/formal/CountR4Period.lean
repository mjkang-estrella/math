import CountFinal2
import Mathlib.FieldTheory.KummerExtension
noncomputable section
open Polynomial
namespace ChanLevine.Round4
open Round3

 theorem orderedProduct_eq_prod {R : Type*} [CommMonoid R] (f : ℕ → R) (r : ℕ) :
    orderedProduct f r = ∏ i ∈ Finset.range r, f i := by
  induction r with
  | zero => simp
  | succ r ih => simp [orderedProduct_succ, Finset.prod_range_succ, ih]

 theorem primitive_denominator {F : Type*} [Field F] {z : F} {e : ℕ}
    (hz : IsPrimitiveRoot z e) (he : 0 < e) :
    denominator z e = universalDenominator e := by
  have hc : IsPrimitiveRoot (Polynomial.C z) e := hz.map_of_injective Polynomial.C_injective
  have h := X_pow_sub_C_eq_prod hc he (rfl : (X : Polynomial F)^e = X^e)
  have hv := congrArg (Polynomial.eval (1 : Polynomial F)) h
  simpa [denominator, orderedProduct_eq_prod, universalDenominator,
    Polynomial.eval_prod, mul_comm] using hv.symm

 theorem frequency_primitive (n : ℕ) [NeZero n] (k : ZMod n) :
    IsPrimitiveRoot (frequencyRoot n k) (addOrderOf k) := by
  constructor
  · exact frequencyRoot_pow n k
  · intro l hl
    have hzero : l • (-k) = 0 := by
      apply ((countingChar n).prim.zmod_char_eq_one_iff n _).mp
      rw [AddChar.map_nsmul_eq_pow]
      exact hl
    have hdiv := addOrderOf_dvd_of_nsmul_eq_zero hzero
    simpa using hdiv

 theorem frequency_denominator (n : ℕ) [NeZero n] (k : ZMod n) :
    denominator (frequencyRoot n k) (addOrderOf k) =
      universalDenominator (addOrderOf k) := by
  apply primitive_denominator (frequency_primitive n k)
  exact addOrderOf_pos k

theorem orderedProduct_map {M N : Type*} [Monoid M] [Monoid N]
    (φ : M →* N) (f : ℕ → M) (r : ℕ) :
    φ (orderedProduct f r) = orderedProduct (fun i => φ (f i)) r := by
  induction r with
  | zero => simp
  | succ r ih => simp [orderedProduct_succ, ih]

theorem orderedProduct_shift_trace {R : Type*} [CommRing R]
    (f : ℕ → Matrix (Fin 2) (Fin 2) R) (e : ℕ) (he : 0 < e)
    (hf : f e = f 0) :
    (orderedProduct (fun i => f (i+1)) e).trace = (orderedProduct f e).trace := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
  rw [orderedProduct_succ, hf]
  have h := orderedProduct_add f 1 r
  simp only [orderedProduct_succ, orderedProduct_zero, one_mul] at h
  rw [Nat.add_comm 1 r] at h
  rw [h, Matrix.trace_mul_comm]
  congr 2
  congr 1
  funext i
  rw [Nat.add_comm]

theorem transfer_constant {F : Type*} [Field F] (z : F) (r : ℕ) :
    (transferProduct z r).map (Polynomial.evalRingHom 0) = (dominoMatrix z 1)^r := by
  induction r with
  | zero => simp [transferProduct, orderedProduct]
  | succ r ih =>
    change (transferProduct z r * transferFactor z r).map _ = _
    rw [Matrix.map_mul, ih, pow_succ]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [transferFactor, dominoMatrix]

theorem transfer_trace_constant {F : Type*} [Field F] (z : F) (r : ℕ) :
    ((transferProduct z r).trace).coeff 0 = 1 + z^r := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  change (Polynomial.evalRingHom 0) ((transferProduct z r).trace) = _
  rw [AddMonoidHom.map_trace, transfer_constant, constant_domino_trace]


theorem transferFactor_comp {F : Type*} [Field F] (z : F) (i : ℕ) :
    (transferFactor z i).map (Polynomial.compRingHom (Polynomial.C z * X)) =
      transferFactor z (i+1) := by
  apply Matrix.ext
  intro a b
  change (transferFactor z i a b).comp (Polynomial.C z * X) = _
  fin_cases a <;> fin_cases b <;>
    simp [transferFactor, dominoMatrix, pow_succ] <;> ring_nf
  all_goals simp

theorem transfer_trace_invariant {F : Type*} [Field F] (z : F) (e : ℕ)
    (he : 0 < e) (hz : z^e = 1) :
    ((transferProduct z e).trace).comp (Polynomial.C z * X) =
      (transferProduct z e).trace := by
  let φ := Polynomial.compRingHom (Polynomial.C z * X)
  change φ ((transferProduct z e).trace) = _
  rw [AddMonoidHom.map_trace]
  have hm := orderedProduct_map (φ.mapMatrix.toMonoidHom) (transferFactor z) e
  change (transferProduct z e).map φ =
    orderedProduct (fun i => (transferFactor z i).map φ) e at hm
  rw [hm]
  simp only [φ, transferFactor_comp]
  apply orderedProduct_shift_trace _ e he
  simp [transferFactor, hz]

theorem invariant_coeff_zero {F : Type*} [Field F] {z : F} {e : ℕ}
    (hz : IsPrimitiveRoot z e) (p : Polynomial F)
    (hp : p.comp (Polynomial.C z * X) = p) (j : ℕ) (hj : ¬ e ∣ j) :
    p.coeff j = 0 := by
  have h := congrArg (fun q : Polynomial F => q.coeff j) hp
  rw [Polynomial.comp_C_mul_X_coeff] at h
  have hn : z^j ≠ 1 := fun h => hj (hz.dvd_of_pow_eq_one j h)
  exact (mul_eq_zero.mp (by linear_combination h : p.coeff j * (z^j-1) = 0)).resolve_right
    (sub_ne_zero.mpr hn)

theorem transfer_trace_coeff_zero {F : Type*} [Field F] {z : F} {e : ℕ}
    (hz : IsPrimitiveRoot z e) (he : 0 < e) (j : ℕ) (hj : ¬ e ∣ j) :
    ((transferProduct z e).trace).coeff j = 0 :=
  invariant_coeff_zero hz _ (transfer_trace_invariant z e he hz.pow_eq_one) j hj


theorem transferFactor_degree {F : Type*} [Field F] (z : F) (k : ℕ) (i j : Fin 2) :
    (transferFactor z k i j).natDegree ≤ 1 := by
  have hg : (1-X*Polynomial.C (z^k) : Polynomial F).natDegree ≤ 1 := by
    apply le_trans (Polynomial.natDegree_sub_le_of_le (m := 1) (n := 1) ?_ ?_) (by simp)
    · simp
    · exact Polynomial.natDegree_mul_le.trans (by simp)
  fin_cases i <;> fin_cases j <;> simp only [transferFactor, dominoMatrix, Matrix.of_apply]
  · exact Polynomial.natDegree_add_le_of_degree_le (by simp) (by simp)
  · exact Polynomial.natDegree_mul_le.trans (by simpa using hg)
  · exact hg
  · simp

theorem transferProduct_degree {F : Type*} [Field F] (z : F) (r : ℕ) :
    ∀ i j, (transferProduct z r i j).natDegree ≤ r := by
  induction r with
  | zero => intro i j; simp [transferProduct, orderedProduct, Matrix.one_apply]; split_ifs <;> simp
  | succ r ih =>
    intro i j
    change ((transferProduct z r * transferFactor z r) i j).natDegree ≤ r+1
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    apply Polynomial.natDegree_add_le_of_degree_le
    · exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (ih _ _) (transferFactor_degree z r _ _))
    · exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (ih _ _) (transferFactor_degree z r _ _))

theorem transfer_trace_degree {F : Type*} [Field F] (z : F) (r : ℕ) :
    ((transferProduct z r).trace).natDegree ≤ r := by
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  exact Polynomial.natDegree_add_le_of_degree_le (transferProduct_degree z r _ _)
    (transferProduct_degree z r _ _)


/-- All one-period trace coefficients except the top one are now determined. -/
theorem primitive_trace_shape {F : Type*} [Field F] {z : F} {e : ℕ}
    (hz : IsPrimitiveRoot z e) (he : 0 < e) :
    (transferProduct z e).trace =
      2 + Polynomial.C (((transferProduct z e).trace).coeff e) * X^e := by
  rw [show (2 : Polynomial F) = 1+1 by ring]
  ext j
  by_cases hj0 : j = 0
  · subst j
    simp [transfer_trace_constant, hz.pow_eq_one, Ne.symm he.ne']
  by_cases hje : j = e
  · subst j
    simp [Polynomial.coeff_one, he.ne']
  have hv : ((transferProduct z e).trace).coeff j = 0 := by
    by_cases hj : e < j
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt ((transfer_trace_degree z e).trans_lt hj)
    · apply transfer_trace_coeff_zero hz he j
      intro hd
      have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) hd
      omega
  simp [Polynomial.coeff_one, hv, hj0, hje]

/-- Remaining algebraic obligation: just the top coefficient, not the entire
period polynomial identity. This is a Prop definition, not an axiom. -/
def PrimitiveTopCoefficient : Prop :=
  ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ k : ZMod n,
    ((transferProduct (frequencyRoot n k) (addOrderOf k)).trace).coeff (addOrderOf k) =
      (parityCoefficient (addOrderOf k) : CountingField n)

theorem primitivePeriodData (ht : PrimitiveTopCoefficient) : PrimitivePeriodData := by
  intro n _ hn k
  constructor
  · rw [primitive_trace_shape (frequency_primitive n k) (addOrderOf_pos k), ht n hn k]
    rfl
  · exact frequency_denominator n k

end ChanLevine.Round4
