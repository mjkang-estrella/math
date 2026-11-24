# Lean source appendix

Status COMPLETE. RFIMinimality.conj_10_1 proves the literal conjecture.

### `RFIDefinitions.lean`

```lean
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

noncomputable section
namespace RFIMinimality
open Matrix

def Valid (r : ℕ) (b : Fin r → ℕ) : Prop :=
  (∀ i, 1 ≤ b i) ∧ ∀ h : 0 < r, 2 ≤ b ⟨r-1, by omega⟩

def TG (r : ℕ) (b : Fin r → ℕ) : SimpleGraph (Σ i : Fin r, Fin (b i)) where
  Adj x y := x ≠ y ∧ Odd ((min x.1 y.1 : Fin r).val + 1)
  symm := ⟨by intro x y h; exact ⟨h.1.symm, by simpa [min_comm] using h.2⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

instance (r : ℕ) (b : Fin r → ℕ) : DecidableRel (TG r b).Adj :=
  fun _ _ => Classical.propDecidable _

def f (X Y : ℝ) : ℝ := (X*Y-1)/(X+Y-2)
def g (X Y : ℝ) : ℝ := X*Y/(X+Y)

/-- Real floor followed by Int.toNat, as required by the source transcription. -/
def greedy (t : ℝ) : ℕ := 1 + (Int.floor t).toNat

/-- d downward steps from the final block. Only d < r is used by rfiInitial. -/
def rfiState (N : ℝ) (r : ℕ) : ℕ → ℕ × ℝ
  | 0 => if Odd r then
      let a := greedy (N+1)
      (a, 1-(1+N)/a)
    else (2, -N/2)
  | d+1 =>
      let s := (rfiState N r d).2
      if Odd (r-(d+1)) then
        let a := greedy ((N+1)/(1-1/s))
        (a, f s (1-(N+1)/a))
      else
        let a := greedy (N/s)
        (a, g s (-N/a))

def rfiInitial (N : ℝ) (r : ℕ) : Fin r → ℕ :=
  fun i => (rfiState N r (r-1-i.val)).1

def IntervalFree (N : ℝ) (r : ℕ) (b : Fin r → ℕ) : Prop :=
  ∀ μ : ℝ, 0 < μ → μ ≤ N →
    ¬ ∃ v : (Σ i : Fin r, Fin (b i)) → ℝ,
      v ≠ 0 ∧ (TG r b).adjMatrix ℝ *ᵥ v = μ • v

def oddBlocks (r : ℕ) := {i : Fin r // Odd (i.val+1)}
instance (r : ℕ) : Fintype (oddBlocks r) := by unfold oddBlocks; infer_instance
instance (r : ℕ) : DecidableEq (oddBlocks r) := by unfold oddBlocks; infer_instance

def B (N : ℝ) (r : ℕ) (b : Fin r → ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => if i = j then
    if Odd (i.val+1) then 1-(N+1)/b i else -N/b i
  else if Odd ((min i j).val+1) then 1 else 0

def Cmat (N : ℝ) (r : ℕ) (b : Fin r → ℕ) : Matrix (oddBlocks r) (oddBlocks r) ℝ :=
  fun i j => 1 + (1/N) * (∑ e : Fin r,
    if Even (e.val+1) ∧ max i.val.val j.val.val < e.val then (b e : ℝ) else 0)
    - (if i = j then (N+1)/b i.val else 0)

def qform {n : Type*} [Fintype n] (A : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  dotProduct x (A *ᵥ x)

def positiveOn {n : Type*} [Fintype n] (A : Matrix n n ℝ)
    (P : Submodule ℝ (n → ℝ)) : Prop :=
  ∀ x ∈ P, x ≠ 0 → 0 < qform A x

def nonpositiveOn {n : Type*} [Fintype n] (A : Matrix n n ℝ)
    (P : Submodule ℝ (n → ℝ)) : Prop := ∀ x ∈ P, qform A x ≤ 0

def blockLift {r : ℕ} (b : Fin r → ℕ) (y : Fin r → ℝ) :
    (Σ i : Fin r, Fin (b i)) → ℝ := fun x => y x.1 / b x.1

def decrement {r : ℕ} (a : Fin r → ℕ) (i : Fin r) : Fin r → ℕ :=
  Function.update a i (a i-1)

def suffixB (N : ℝ) (r j : ℕ) : Matrix {i : Fin r // j ≤ i.val} {i : Fin r // j ≤ i.val} ℝ :=
  (B N r (rfiInitial N r)).submatrix Subtype.val Subtype.val

#print axioms TG
#print axioms rfiInitial
end RFIMinimality
```

### `RFIExamples.lean`

```lean
import RFIDefinitions
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

namespace RFIMinimality

theorem example14 : rfiInitial (24/5) 5 = ![5,145,5,145,6] := by
  funext i
  fin_cases i <;> norm_num [rfiInitial, rfiState, greedy, f, g, Nat.odd_iff]

theorem example15 : rfiInitial (24/5) 6 = ![6,44,6,36,5,2] := by
  funext i
  fin_cases i <;> norm_num [rfiInitial, rfiState, greedy, f, g, Nat.odd_iff]

#print axioms example14
#print axioms example15
end RFIMinimality
```

### `RFISigns.lean`

```lean
import RFIDefinitions
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
namespace RFIMinimality

lemma greedy_pos (t : ℝ) : 0 < greedy t := by unfold greedy; omega

lemma greedy_cast (t : ℝ) (ht : 0 ≤ t) : (greedy t : ℝ) = (⌊t⌋ : ℤ) + 1 := by
  have hf : (⌊t⌋.toNat : ℤ) = ⌊t⌋ := Int.toNat_of_nonneg (Int.floor_nonneg.mpr ht)
  have hc := congrArg (fun z : ℤ => (z : ℝ)) hf
  simp only [Int.cast_natCast] at hc
  simp only [greedy, Nat.cast_add, Nat.cast_one]
  linarith

lemma lt_greedy (t : ℝ) (ht : 0 ≤ t) : t < greedy t := by
  rw [greedy_cast t ht]
  exact Int.lt_floor_add_one t

lemma greedy_le (t : ℝ) (ht : 0 ≤ t) : (greedy t : ℝ) ≤ t+1 := by
  rw [greedy_cast t ht]
  linarith [Int.floor_le t]

/-- The odd extension preserves the positive sign and has a nonzero f denominator. -/
lemma odd_step (N s : ℝ) (hN : 0 < N) (hs : s < 0) :
    0 ≤ (N+1)/(1-1/s) ∧
    0 < f s (1-(N+1)/(greedy ((N+1)/(1-1/s)) : ℝ)) ∧
    s + (1-(N+1)/(greedy ((N+1)/(1-1/s)) : ℝ)) - 2 ≠ 0 := by
  have hs0 : s ≠ 0 := ne_of_lt hs
  have hh : 1/s < 0 := one_div_neg.mpr hs
  have hd : 0 < 1-1/s := by linarith
  have ht : 0 ≤ (N+1)/(1-1/s) := le_of_lt (div_pos (by linarith) hd)
  have ha : 0 < (greedy ((N+1)/(1-1/s)) : ℝ) := by exact_mod_cast greedy_pos _
  have hl := (div_lt_iff₀ hd).mp (lt_greedy _ ht)
  have hy : 1/s < 1-(N+1)/(greedy ((N+1)/(1-1/s)) : ℝ) := by
    apply (lt_sub_iff_add_lt).mpr
    have h := (div_lt_iff₀ ha).mpr (by nlinarith : N+1 < (1-1/s)*(greedy ((N+1)/(1-1/s)) : ℝ))
    linarith
  have hy1 : 1-(N+1)/(greedy ((N+1)/(1-1/s)) : ℝ) < 1 := by
    have hp : 0 < (N+1)/(greedy ((N+1)/(1-1/s)) : ℝ) := div_pos (by linarith) ha
    linarith
  have hn : s*(1-(N+1)/(greedy ((N+1)/(1-1/s)) : ℝ))-1 < 0 := by
    have hmul := (mul_lt_mul_of_neg_left hy hs)
    have he : s*(1/s) = 1 := by field_simp
    nlinarith
  have hden : s+(1-(N+1)/(greedy ((N+1)/(1-1/s)) : ℝ))-2 < 0 := by linarith
  exact ⟨ht, div_pos_of_neg_of_neg hn hden, ne_of_lt hden⟩

/-- The even extension preserves the negative sign and has a nonzero g denominator. -/
lemma even_step (N s : ℝ) (hN : 0 < N) (hs : 0 < s) :
    0 ≤ N/s ∧  g s (-N/(greedy (N/s) : ℝ)) < 0 ∧
    s + (-N/(greedy (N/s) : ℝ)) ≠ 0 := by
  have ht : 0 ≤ N/s := (div_pos hN hs).le
  have ha : 0 < (greedy (N/s) : ℝ) := by exact_mod_cast greedy_pos _
  have hl := (div_lt_iff₀ hs).mp (lt_greedy _ ht)
  have hn : -N/(greedy (N/s) : ℝ) < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hN) ha
  have hd : 0 < s+(-N/(greedy (N/s) : ℝ)) := by
    have h := (div_lt_iff₀ ha).mpr (by nlinarith : N < s*(greedy (N/s) : ℝ))
    rw [neg_div]
    linarith
  exact ⟨ht, div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hs hn) hd, ne_of_gt hd⟩

/-- Every visited state uses a positive block size and the source's alternating sign. -/
theorem rfi_signs (N : ℝ) (hN : 0 < N) (r d : ℕ) (hd : d < r) :
    0 < (rfiState N r d).1 ∧
    (Odd (r-d) → 0 < (rfiState N r d).2) ∧
    (Even (r-d) → (rfiState N r d).2 < 0) := by
  induction d with
  | zero =>
    by_cases ho : Odd r
    · simp only [rfiState, ite_eq_left ho, Nat.sub_zero]
      have ht : 0 ≤ N+1 := by linarith
      have ha : 0 < (greedy (N+1) : ℝ) := by exact_mod_cast greedy_pos _
      have hy : 0 < 1-(1+N)/(greedy (N+1) : ℝ) := by
        have hl := lt_greedy (N+1) ht
        have hh := (div_lt_one ha).mpr (by linarith : 1+N < (greedy (N+1) : ℝ))
        linarith
      refine ⟨greedy_pos _, fun _ => hy, ?_⟩
      intro he
      exact False.elim ((Nat.not_even_iff_odd.mpr ho) he)
    · simp only [rfiState, ite_eq_right ho, Nat.sub_zero]
      exact ⟨by omega, fun hh => False.elim (ho hh), fun _ => by linarith⟩
  | succ d ih =>
    have hi := ih (by omega)
    have heq : r-d = (r-(d+1))+1 := by omega
    by_cases ho : Odd (r-(d+1))
    · have he : Even (r-d) := by
        rw [Nat.even_iff]
        rw [Nat.odd_iff] at ho
        omega
      have hh := odd_step N (rfiState N r d).2 hN (hi.2.2 he)
      simp only [rfiState, ite_eq_left ho]
      refine ⟨greedy_pos _, fun _ => hh.2.1, ?_⟩
      intro he'
      exact False.elim ((Nat.not_even_iff_odd.mpr ho) he')
    · have he : Even (r-(d+1)) := Nat.not_odd_iff_even.mp ho
      have hoo : Odd (r-d) := by rw [heq, Nat.odd_add_one]; exact ho
      have hh := even_step N (rfiState N r d).2 hN (hi.2.1 hoo)
      simp only [rfiState, ite_eq_right ho]
      exact ⟨greedy_pos _, fun hh' => False.elim (ho hh'), fun _ => hh.2.1⟩

theorem rfi_floor_nonneg (N : ℝ) (hN : 0 < N) (r d : ℕ) (hd : d+1 < r) :
    0 ≤ (if Odd (r-(d+1)) then
      (N+1)/(1-1/(rfiState N r d).2) else N/(rfiState N r d).2) := by
  have hi := rfi_signs N hN r d (by omega)
  have heq : r-d = (r-(d+1))+1 := by omega
  split_ifs with ho
  · have he : Even (r-d) := by
        rw [Nat.even_iff]
        rw [Nat.odd_iff] at ho
        omega
    exact (odd_step N _ hN (hi.2.2 he)).1
  · have hoo : Odd (r-d) := by rw [heq, Nat.odd_add_one]; exact ho
    exact (even_step N _ hN (hi.2.1 hoo)).1

theorem rfi_valid (N : ℝ) (hN : 0 < N) (r : ℕ) (_hr : 2 ≤ r) :
    Valid r (rfiInitial N r) := by
  constructor
  · intro i
    exact (rfi_signs N hN r (r-1-i.val) (by omega)).1
  · intro h
    simp only [rfiInitial, Nat.sub_self, rfiState]
    split_ifs with ho
    · have hl := lt_greedy (N+1) (by linarith : 0 ≤ N+1)
      have hh : (1 : ℝ) < greedy (N+1) := by linarith
      have hh' : 1 < greedy (N+1) := by exact_mod_cast hh
      exact hh'
    · exact le_rfl

#print axioms rfi_signs
#print axioms rfi_floor_nonneg
#print axioms rfi_valid
end RFIMinimality
```

### `RFISpectral.lean`

```lean
import RFIDefinitions
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
namespace RFIMinimality
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Orthonormal eigenbasis coordinates, on the literal Pi vector space. -/
def eigCoords {A : Matrix n n ℝ} (hA : A.IsHermitian) : (n → ℝ) ≃ₗ[ℝ] (n → ℝ) :=
  (WithLp.linearEquiv 2 ℝ (n → ℝ)).symm.trans
    (hA.eigenvectorBasis.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 ℝ (n → ℝ)))

lemma eigCoords_apply {A : Matrix n n ℝ} (hA : A.IsHermitian) (x : n → ℝ) (i : n) :
    eigCoords hA x i = dotProduct (hA.eigenvectorBasis i).ofLp x := by
  simp [eigCoords, OrthonormalBasis.repr_apply_apply,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

lemma eigCoords_dot {A : Matrix n n ℝ} (hA : A.IsHermitian) (x y : n → ℝ) :
    dotProduct (eigCoords hA x) (eigCoords hA y) = dotProduct x y := by
  have h := hA.eigenvectorBasis.repr.inner_map_map
    (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  change dotProduct (hA.eigenvectorBasis.repr (WithLp.toLp 2 x)).ofLp
    (hA.eigenvectorBasis.repr (WithLp.toLp 2 y)).ofLp = dotProduct x y
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, WithLp.ofLp_toLp,
    dotProduct_comm] using h

lemma eigCoords_mulVec {A : Matrix n n ℝ} (hA : A.IsHermitian) (x : n → ℝ) (i : n) :
    eigCoords hA (A *ᵥ x) i = hA.eigenvalues i * eigCoords hA x i := by
  rw [eigCoords_apply]
  have h := hA.star_dotProduct_mulVec_comm (hA.eigenvectorBasis i).ofLp x
  simp only [star_trivial] at h
  rw [h, hA.mulVec_eigenvectorBasis, dotProduct_smul, eigCoords_apply, dotProduct_comm]
  rfl

lemma spectral_qform {A : Matrix n n ℝ} (hA : A.IsHermitian) (x : n → ℝ) :
    qform A x = ∑ i, hA.eigenvalues i * (eigCoords hA x i)^2 := by
  rw [qform, ← eigCoords_dot hA]
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro i _
  rw [eigCoords_mulVec]
  ring

lemma spectral_shift_qform {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (N : ℝ) (x : n → ℝ) :
    qform (A-N • 1) x = ∑ i, (hA.eigenvalues i-N) * (eigCoords hA x i)^2 := by
  have he : eigCoords hA ((A-N • 1) *ᵥ x) =
      eigCoords hA (A *ᵥ x) - N • eigCoords hA x := by
    simp [sub_mulVec, smul_mulVec, one_mulVec]
  rw [qform, ← eigCoords_dot hA, he]
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, eigCoords_mulVec]
  ring

omit [DecidableEq n] in
/-- A coordinate projection injective on a subspace bounds its dimension. -/
lemma finrank_le_card_of_coord_kernel (e : (n → ℝ) ≃ₗ[ℝ] (n → ℝ))
    (s : Set n) [Fintype s] (P : Submodule ℝ (n → ℝ))
    (hker : ∀ x ∈ P, (∀ i ∈ s, e x i = 0) → x = 0) :
    Module.finrank ℝ P ≤ Fintype.card s := by
  classical
  let T : P →ₗ[ℝ] (s → ℝ) :=
    (LinearMap.funLeft ℝ ℝ (fun i : s => i.val)).comp (e.toLinearMap.comp P.subtype)
  have hinj : Function.Injective T := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    apply Subtype.ext
    exact hker x x.property (fun i hi => congrFun hx ⟨i, hi⟩)
  simpa only [Module.finrank_pi] using LinearMap.finrank_le_finrank_of_injective hinj

lemma positive_finrank_le_card {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (P : Submodule ℝ (n → ℝ)) (hP : positiveOn A P) :
    Module.finrank ℝ P ≤ Fintype.card {i // 0 < hA.eigenvalues i} := by
  classical
  apply finrank_le_card_of_coord_kernel (eigCoords hA) {i | 0 < hA.eigenvalues i} P
  intro x hx hz
  by_contra hne
  have hp := hP x hx hne
  rw [spectral_qform hA] at hp
  have hn : (∑ i, hA.eigenvalues i * (eigCoords hA x i)^2) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    by_cases hi : 0 < hA.eigenvalues i
    · rw [hz i hi]; simp
    · exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hi) (sq_nonneg _)
  exact (not_lt_of_ge hn) hp

/-- A nonpositive shifted subspace has dimension at most the number of original
nonpositive eigenvalues, provided the interval (0,N] contains no eigenvalue. -/
lemma nonpositive_finrank_le_card {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (N : ℝ) (Q : Submodule ℝ (n → ℝ)) (hQ : nonpositiveOn (A-N • 1) Q)
    (hgap : ∀ i, 0 < hA.eigenvalues i → N < hA.eigenvalues i) :
    Module.finrank ℝ Q ≤ Fintype.card {i // hA.eigenvalues i ≤ 0} := by
  classical
  apply finrank_le_card_of_coord_kernel (eigCoords hA) {i | hA.eigenvalues i ≤ 0} Q
  intro x hx hz
  by_contra hne
  have hex : ∃ i, eigCoords hA x i ≠ 0 := by
    by_contra hall
    push Not at hall
    have he : eigCoords hA x = 0 := funext hall
    exact hne (eigs_zero he)
  obtain ⟨i, hi⟩ := hex
  have hpos : 0 < hA.eigenvalues i := by
    by_contra h
    exact hi (hz i (le_of_not_gt h))
  have hs : 0 < ∑ j, (hA.eigenvalues j-N) * (eigCoords hA x j)^2 := by
    apply (Finset.sum_pos_iff_of_nonneg _).mpr
    · exact ⟨i, Finset.mem_univ _, mul_pos (sub_pos.mpr (hgap i hpos)) (sq_pos_of_ne_zero hi)⟩
    · intro j _
      by_cases hj : hA.eigenvalues j ≤ 0
      · rw [hz j hj]; simp
      · exact mul_nonneg (sub_nonneg.mpr (hgap j (lt_of_not_ge hj)).le) (sq_nonneg _)
  have hn := hQ x hx
  rw [spectral_shift_qform hA] at hn
  exact (not_lt_of_ge hn) hs
where
  eigs_zero {x : n → ℝ} (h : eigCoords hA x = 0) : x = 0 :=
    (eigCoords hA).injective (h.trans (map_zero (eigCoords hA)).symm)

/-- The spectral bridge needed by the threshold-graph argument. It includes
an eigenvalue equal to N and does not use an inertia law. -/
theorem interval_eigenvalue_of_subspaces
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (N : ℝ) (_hN : 0 < N)
    (P Q : Submodule ℝ (n → ℝ))
    (hP : positiveOn A P) (hQ : nonpositiveOn (A-N • 1) Q)
    (hdim : Fintype.card n < Module.finrank ℝ P + Module.finrank ℝ Q) :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ N ∧ ∃ v : n → ℝ, v ≠ 0 ∧ A *ᵥ v = μ • v := by
  classical
  by_contra hf
  have hgap : ∀ i, 0 < hA.eigenvalues i → N < hA.eigenvalues i := by
    intro i hi
    by_contra hle
    apply hf
    refine ⟨hA.eigenvalues i, hi, le_of_not_gt hle,
      (hA.eigenvectorBasis i).ofLp, ?_, hA.mulVec_eigenvectorBasis i⟩
    exact (WithLp.ofLp_eq_zero 2).ne.2 (hA.eigenvectorBasis.orthonormal.ne_zero i)
  have hp := positive_finrank_le_card hA P hP
  have hq := nonpositive_finrank_le_card hA N Q hQ hgap
  have hc : Fintype.card {i // 0 < hA.eigenvalues i} +
      Fintype.card {i // hA.eigenvalues i ≤ 0} = Fintype.card n := by
    have h := Fintype.card_subtype_compl (fun i => 0 < hA.eigenvalues i)
    have hb := Fintype.card_subtype_le (fun i => 0 < hA.eigenvalues i)
    simp only [not_lt] at h
    omega
  omega

#print axioms interval_eigenvalue_of_subspaces
end RFIMinimality
```

### `RFIBlocks.lean`

```lean
import RFIDefinitions
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
namespace RFIMinimality
open Matrix

/-- The blow-up matrix includes the loops of odd (clique) blocks. -/
def H (r : ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => if Odd ((min i j).val+1) then 1 else 0

/-- Summation of vertex coordinates in each block. -/
def aggregate (r : ℕ) (b : Fin r → ℕ) : Matrix (Fin r) (Σ i, Fin (b i)) ℝ :=
  fun i x => if i = x.1 then 1 else 0

lemma aggregate_mulVec (r : ℕ) (b : Fin r → ℕ)
    (v : (Σ i, Fin (b i)) → ℝ) (i : Fin r) :
    (aggregate r b *ᵥ v) i = ∑ t : Fin (b i), v ⟨i,t⟩ := by
  classical
  simp only [aggregate, mulVec, dotProduct, Fintype.sum_sigma, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

lemma adjacency_eq (r : ℕ) (b : Fin r → ℕ) :
    (TG r b).adjMatrix ℝ =
      (aggregate r b)ᵀ * H r * aggregate r b -
      diagonal (fun x => if Odd (x.1.val+1) then (1:ℝ) else 0) := by
  classical
  ext x y
  have hmul : ((aggregate r b)ᵀ * H r * aggregate r b) x y = H r x.1 y.1 := by
    simp [aggregate, Matrix.mul_apply]
  rw [Matrix.sub_apply, hmul]
  by_cases he : x = y
  · subst y
    simp [SimpleGraph.adjMatrix, TG, H]
  · simp [SimpleGraph.adjMatrix, TG, H, he]

lemma qform_congruence {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m m ℝ) (E : Matrix m n ℝ) (x : n → ℝ) :
    qform (Eᵀ*A*E) x = qform A (E *ᵥ x) := by
  unfold qform
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_transpose_mulVec]
  exact dotProduct_comm _ _

lemma qform_sub {n : Type*} [Fintype n]
    (A D : Matrix n n ℝ) (x : n → ℝ) :
    qform (A-D) x = qform A x - qform D x := by
  simp [qform, sub_mulVec, dotProduct_sub]

lemma qform_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (d x : n → ℝ) : qform (diagonal d) x = ∑ i, d i*(x i)^2 := by
  simp only [qform, mulVec_diagonal, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact quadratic-form reduction on arbitrary vertex vectors. -/
theorem adjacency_form (N : ℝ) (r : ℕ) (b : Fin r → ℕ)
    (v : (Σ i, Fin (b i)) → ℝ) :
    qform ((TG r b).adjMatrix ℝ - N • 1) v =
    qform (H r) (aggregate r b *ᵥ v) -
      ∑ x : (Σ i, Fin (b i)), (N + if Odd (x.1.val+1) then 1 else 0) * (v x)^2 := by
  classical
  have hId : N • (1 : Matrix (Σ i, Fin (b i)) (Σ i, Fin (b i)) ℝ) =
      diagonal (fun _ => N) := by ext x y; simp [diagonal_apply, Matrix.one_apply]
  rw [adjacency_eq, hId, qform_sub, qform_sub, qform_congruence,
    qform_diagonal, qform_diagonal]
  rw [sub_sub, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma aggregate_blockLift (r : ℕ) (b : Fin r → ℕ) (hb : ∀ i, 0 < b i)
    (y : Fin r → ℝ) : aggregate r b *ᵥ blockLift b y = y := by
  funext i
  rw [aggregate_mulVec]
  have hi : (b i : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hb i))
  simp only [blockLift, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The block-sum-coordinate matrix is exactly B, including the shift. -/
theorem block_form (N : ℝ) (r : ℕ) (b : Fin r → ℕ) (hb : Valid r b)
    (y : Fin r → ℝ) :
    qform ((TG r b).adjMatrix ℝ - N • 1) (blockLift b y) = qform (B N r b) y := by
  classical
  have hp : ∀ i, 0 < b i := fun i => hb.1 i
  have heq : B N r b = H r - diagonal (fun i =>
      (N + if Odd (i.val+1) then 1 else 0)/(b i : ℝ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases ho : Odd (i.val+1) <;> simp [B, H, ho]
      ring
    · simp [B, H, hij]
  rw [adjacency_form, aggregate_blockLift r b hp, heq, qform_sub, qform_diagonal]
  congr 1
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (b i : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hp i))
  change (∑ _ : Fin (b i), (N + if Odd (i.val+1) then 1 else 0) * (y i / (b i : ℝ))^2) = _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

#print axioms adjacency_form
#print axioms block_form
end RFIMinimality
```

### `RFICMatrix.lean`

```lean
import RFIBlocks
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
namespace RFIMinimality
open Matrix

/-- The rank-one vector contributed by an even block. -/
def before (r : ℕ) (e : Fin r) : oddBlocks r → ℝ :=
  fun i => if i.val.val < e.val then 1 else 0

def outer {n : Type*} (w : n → ℝ) : Matrix n n ℝ := fun i j => w i * w j

lemma qform_outer {n : Type*} [Fintype n] (w x : n → ℝ) :
    qform (outer w) x = (dotProduct w x)^2 := by
  simp only [qform, outer, mulVec, dotProduct, pow_two, Finset.sum_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma qform_add {n : Type*} [Fintype n] (A D : Matrix n n ℝ) (x : n → ℝ) :
    qform (A+D) x = qform A x + qform D x := by
  simp [qform, add_mulVec, dotProduct_add]

lemma qform_smul {n : Type*} [Fintype n] (t : ℝ) (A : Matrix n n ℝ) (x : n → ℝ) :
    qform (t • A) x = t*qform A x := by
  simp [qform, smul_mulVec, dotProduct_smul]

lemma qform_sum {n e : Type*} [Fintype n] [Fintype e]
    (A : e → Matrix n n ℝ) (x : n → ℝ) :
    qform (∑ i, A i) x = ∑ i, qform (A i) x := by
  classical
  simp only [qform, Matrix.sum_mulVec, dotProduct_sum]

lemma Cmat_decomposition (N : ℝ) (r : ℕ) (b : Fin r → ℕ) :
    Cmat N r b = outer (fun _ => (1:ℝ)) -
      diagonal (fun i : oddBlocks r => (N+1)/(b i.val : ℝ)) +
      ∑ e : Fin r, (if Even (e.val+1) then (b e : ℝ)/N else 0) • outer (before r e) := by
  classical
  ext i j
  simp only [Cmat, outer, Matrix.add_apply, Matrix.sub_apply, one_mul,
    diagonal_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  have hsum : (∑ e : Fin r, 1/N *
      (if Even (e.val+1) ∧ max i.val.val j.val.val < e.val then (b e : ℝ) else 0)) =
      ∑ e : Fin r, (if Even (e.val+1) then (b e : ℝ)/N else 0) *
        (before r e i * before r e j) := by
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : Even (e.val+1) <;>
      by_cases hi : i.val.val < e.val <;> by_cases hj : j.val.val < e.val <;>
      simp [before, he, hi, hj, max_lt_iff, div_eq_mul_inv, mul_comm]
  rw [hsum]
  ring

/-- The C form as a sum of signed squares. This also records its Schur rank-one structure. -/
theorem Cmat_form (N : ℝ) (r : ℕ) (b : Fin r → ℕ) (x : oddBlocks r → ℝ) :
    qform (Cmat N r b) x = (∑ i, x i)^2 -
      (∑ i : oddBlocks r, ((N+1)/(b i.val : ℝ))*(x i)^2) +
      ∑ e : Fin r, (if Even (e.val+1) then (b e : ℝ)/N else 0) *
        (dotProduct (before r e) x)^2 := by
  rw [Cmat_decomposition, qform_add, qform_sub, qform_outer, qform_diagonal, qform_sum]
  simp only [qform_smul, qform_outer, dotProduct, one_mul]

/-- Coordinatewise increasing block sizes increases C in quadratic-form order. -/
theorem C_mono (N : ℝ) (hN : 0 < N) (r : ℕ) (a b : Fin r → ℕ)
    (_ha : Valid r a) (hb : Valid r b) (hle : ∀ i, b i ≤ a i) (x : oddBlocks r → ℝ) :
    qform (Cmat N r b) x ≤ qform (Cmat N r a) x := by
  rw [Cmat_form, Cmat_form]
  have hodd : (∑ i : oddBlocks r, ((N+1)/(a i.val : ℝ))*(x i)^2) ≤
      ∑ i : oddBlocks r, ((N+1)/(b i.val : ℝ))*(x i)^2 := by
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hbpos : 0 < (b i.val : ℝ) := by exact_mod_cast hb.1 i.val
    exact div_le_div_of_nonneg_left (by linarith) hbpos (by exact_mod_cast hle i.val)
  have heven : (∑ e : Fin r, (if Even (e.val+1) then (b e : ℝ)/N else 0) *
      (dotProduct (before r e) x)^2) ≤
      ∑ e : Fin r, (if Even (e.val+1) then (a e : ℝ)/N else 0) *
      (dotProduct (before r e) x)^2 := by
    apply Finset.sum_le_sum
    intro e _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    split_ifs
    · exact div_le_div_of_nonneg_right (by exact_mod_cast hle e) hN.le
    · exact le_rfl
  linarith

#print axioms Cmat_form
#print axioms C_mono
end RFIMinimality
```

### `RFILifting.lean`

```lean
import RFIBlocks
import RFISpectral
import Mathlib.Algebra.Order.Chebyshev

noncomputable section
namespace RFIMinimality
open Matrix

lemma B_eq (N : ℝ) (r : ℕ) (b : Fin r → ℕ) :
    B N r b = H r - diagonal (fun i =>
      (N + if Odd (i.val+1) then 1 else 0)/(b i : ℝ)) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases ho : Odd (i.val+1) <;> simp [B, H, ho]
    ring
  · simp [B, H, hij]

/-- Block averaging can only increase the shifted quadratic form for N ≥ 0. -/
theorem graph_form_le (N : ℝ) (hN : 0 ≤ N) (r : ℕ) (b : Fin r → ℕ)
    (hb : Valid r b) (v : (Σ i, Fin (b i)) → ℝ) :
    qform ((TG r b).adjMatrix ℝ-N • 1) v ≤ qform (B N r b) (aggregate r b *ᵥ v) := by
  classical
  rw [adjacency_form, B_eq, qform_sub, qform_diagonal]
  apply sub_le_sub_left
  rw [Fintype.sum_sigma]
  apply Finset.sum_le_sum
  intro i _
  rw [aggregate_mulVec]
  have hp : 0 < (b i : ℝ) := by exact_mod_cast hb.1 i
  have hc : 0 ≤ N + if Odd (i.val+1) then 1 else 0 := by split_ifs <;> linarith
  have hs : (∑ t : Fin (b i), v ⟨i,t⟩)^2 ≤
      (b i : ℝ) * ∑ t : Fin (b i), (v ⟨i,t⟩)^2 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun t : Fin (b i) => v ⟨i,t⟩))
  have hdiv : (∑ t : Fin (b i), v ⟨i,t⟩)^2 / (b i : ℝ) ≤
      ∑ t : Fin (b i), (v ⟨i,t⟩)^2 :=
    (div_le_iff₀ hp).mpr (by nlinarith [hs])
  have hh := mul_le_mul_of_nonneg_left hdiv hc
  simp only [Finset.mul_sum] at hh
  convert hh using 1
  ring

def blockLiftLinear (r : ℕ) (b : Fin r → ℕ) :
    (Fin r → ℝ) →ₗ[ℝ] ((Σ i, Fin (b i)) → ℝ) where
  toFun := blockLift b
  map_add' x y := by funext v; simp [blockLift, add_div]
  map_smul' t x := by funext v; simp [blockLift, mul_div_assoc]

lemma blockLift_injective (r : ℕ) (b : Fin r → ℕ) (hb : Valid r b) :
    Function.Injective (blockLiftLinear r b) := by
  intro x y he
  have h := congrArg (fun v => aggregate r b *ᵥ v) he
  simpa only [blockLiftLinear, LinearMap.coe_mk, AddHom.coe_mk,
    aggregate_blockLift r b (fun i => hb.1 i)] using h

/-- A purely linear dimension bound for the preimage of a subspace. -/
lemma finrank_comap_lower {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module ℝ V] [Module ℝ W] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (T : V →ₗ[ℝ] W) (Q : Submodule ℝ W) :
    Module.finrank ℝ V + Module.finrank ℝ Q ≤
      Module.finrank ℝ W + Module.finrank ℝ (Q.comap T) := by
  let F := Q.mkQ.comp T
  have hk : F.ker = Q.comap T := by simp only [F, LinearMap.ker_comp, Submodule.ker_mkQ]
  have h := F.finrank_range_add_finrank_ker
  have hh := (LinearMap.range F).finrank_le
  have hq := Q.finrank_quotient_add_finrank
  rw [hk] at h
  omega

/-- Spectral extraction can now be done entirely with r-dimensional block subspaces. -/
theorem interval_eigenvalue_of_block_subspaces
    (N : ℝ) (hN : 0 < N) (r : ℕ) (b : Fin r → ℕ) (hb : Valid r b)
    (P Q : Submodule ℝ (Fin r → ℝ))
    (hP : positiveOn (B 0 r b) P) (hQ : nonpositiveOn (B N r b) Q)
    (hdim : r < Module.finrank ℝ P + Module.finrank ℝ Q) :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ N ∧
      ∃ v : (Σ i, Fin (b i)) → ℝ, v ≠ 0 ∧ (TG r b).adjMatrix ℝ *ᵥ v = μ • v := by
  classical
  let T := (aggregate r b).mulVecLin
  let PG := P.map (blockLiftLinear r b)
  let QG := Q.comap T
  have hPG : positiveOn ((TG r b).adjMatrix ℝ) PG := by
    intro v hv hne
    obtain ⟨y, hy, rfl⟩ := hv
    have hyne : y ≠ 0 := by intro he; simp [he] at hne
    have hh := block_form 0 r b hb y
    simp only [zero_smul, sub_zero] at hh
    rw [show (blockLiftLinear r b) y = blockLift b y from rfl, hh]
    exact hP y hy hyne
  have hQG : nonpositiveOn ((TG r b).adjMatrix ℝ-N • 1) QG := by
    intro v hv
    exact (graph_form_le N hN.le r b hb v).trans (hQ (T v) hv)
  have hdimPG : Module.finrank ℝ PG = Module.finrank ℝ P := by
    exact (Submodule.equivMapOfInjective (blockLiftLinear r b) (blockLift_injective r b hb) P).finrank_eq.symm
  have hdimQG := finrank_comap_lower T Q
  simp only [Module.finrank_pi, Fintype.card_fin] at hdimQG
  have hA : ((TG r b).adjMatrix ℝ).IsHermitian :=
    Matrix.isHermitian_iff_isSymm.mpr ((TG r b).isSymm_adjMatrix (α := ℝ))
  apply interval_eigenvalue_of_subspaces ((TG r b).adjMatrix ℝ) hA N hN PG QG hPG hQG
  change Fintype.card (Σ i, Fin (b i)) < Module.finrank ℝ PG + Module.finrank ℝ (Q.comap T)
  rw [hdimPG]
  omega

#print axioms graph_form_le
#print axioms interval_eigenvalue_of_block_subspaces
end RFIMinimality
```

### `RFISchur.lean`

```lean
import RFICMatrix
import RFILifting
import Mathlib.Data.Matrix.Block

noncomputable section
namespace RFIMinimality
open Matrix
variable {o e : Type*} [Fintype o] [Fintype e] [DecidableEq e]

/-- General Schur complement against a negative diagonal block. -/
def schur (A : Matrix o o ℝ) (X : Matrix o e ℝ) (d : e → ℝ) : Matrix o o ℝ :=
  A + X * diagonal (fun j => 1/d j) * Xᵀ

def schurBlock (A : Matrix o o ℝ) (X : Matrix o e ℝ) (d : e → ℝ) :
    Matrix (o ⊕ e) (o ⊕ e) ℝ := fromBlocks A X Xᵀ (-diagonal d)

lemma schur_form (A : Matrix o o ℝ) (X : Matrix o e ℝ) (d : e → ℝ) (x : o → ℝ) :
    qform (schur A X d) x = qform A x + ∑ j, ((Xᵀ *ᵥ x) j)^2/d j := by
  rw [schur, qform_add]
  have h := qform_congruence (diagonal (fun j => 1/d j)) Xᵀ x
  rw [transpose_transpose] at h
  rw [h, qform_diagonal]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma schurBlock_form (A : Matrix o o ℝ) (X : Matrix o e ℝ) (d : e → ℝ)
    (x : o → ℝ) (y : e → ℝ) :
    qform (schurBlock A X d) (Sum.elim x y) =
      qform A x + 2*dotProduct (Xᵀ *ᵥ x) y - ∑ j, d j*(y j)^2 := by
  unfold qform schurBlock
  rw [fromBlocks_mulVec, sumElim_dotProduct_sumElim]
  change x ⬝ᵥ (A *ᵥ x + X *ᵥ y) + y ⬝ᵥ (Xᵀ *ᵥ x + (-diagonal d) *ᵥ y) = _
  rw [dotProduct_add, dotProduct_add, neg_mulVec, dotProduct_neg,
    ← dotProduct_transpose_mulVec X y x]
  have hh := qform_diagonal d y
  unfold qform at hh
  rw [hh, dotProduct_comm y (Xᵀ *ᵥ x)]
  ring

/-- Completing the square. No matrix inverse, determinant or inertia theorem is needed. -/
theorem schur_bound (A : Matrix o o ℝ) (X : Matrix o e ℝ) (d : e → ℝ)
    (hd : ∀ j, 0 < d j) (v : o ⊕ e → ℝ) :
    qform (schurBlock A X d) v ≤ qform (schur A X d) (fun i => v (.inl i)) := by
  let x := fun i => v (.inl i)
  let y := fun j => v (.inr j)
  have hv : v = Sum.elim x y := by funext i; cases i <;> rfl
  rw [hv, schurBlock_form, schur_form]
  have he : 2*dotProduct (Xᵀ *ᵥ x) y - ∑ j, d j*(y j)^2 ≤
      ∑ j, ((Xᵀ *ᵥ x) j)^2/d j := by
    unfold dotProduct
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro j _
    have hs := sq_nonneg (d j*y j - (Xᵀ *ᵥ x) j)
    apply (le_div_iff₀ (hd j)).mpr
    nlinarith
  dsimp only [Sum.elim_inl]
  linarith

lemma qform_smul_vec {n : Type*} [Fintype n] (A : Matrix n n ℝ) (t : ℝ) (x : n → ℝ) :
    qform A (t • x) = t^2*qform A x := by
  simp only [qform, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- A nonpositive Schur vector supplies the needed large nonpositive block subspace. -/
theorem nonpositive_subspace_of_schur (A : Matrix o o ℝ) (X : Matrix o e ℝ) (d : e → ℝ)
    (hd : ∀ j, 0 < d j) (x : o → ℝ) (hx : x ≠ 0)
    (hCx : qform (schur A X d) x ≤ 0) :
    ∃ Q : Submodule ℝ (o ⊕ e → ℝ), nonpositiveOn (schurBlock A X d) Q ∧
      Fintype.card (o ⊕ e) < Fintype.card o + Module.finrank ℝ Q := by
  let T : (o ⊕ e → ℝ) →ₗ[ℝ] (o → ℝ) := LinearMap.funLeft ℝ ℝ Sum.inl
  let L : Submodule ℝ (o → ℝ) := Submodule.span ℝ {x}
  refine ⟨L.comap T, ?_, ?_⟩
  · intro v hv
    have hmem : T v ∈ Submodule.span ℝ {x} := hv
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
    have hb := schur_bound A X d hd v
    change qform (schurBlock A X d) v ≤ qform (schur A X d) (T v) at hb
    rw [← ht, qform_smul_vec] at hb
    exact hb.trans (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) hCx)
  · have hl : Module.finrank ℝ L = 1 := finrank_span_singleton hx
    have h := finrank_comap_lower T L
    simp only [Module.finrank_pi] at h
    omega

#print axioms schur_bound
#print axioms nonpositive_subspace_of_schur
end RFIMinimality
```

### `RFIParitySchur.lean`

```lean
import RFISchur
import Mathlib.Logic.Equiv.Sum

set_option linter.unusedSimpArgs false
noncomputable section
namespace RFIMinimality
open Matrix

def evenBlocks (r : ℕ) := {i : Fin r // ¬ Odd (i.val+1)}
instance (r : ℕ) : Fintype (evenBlocks r) := by unfold evenBlocks; infer_instance
instance (r : ℕ) : DecidableEq (evenBlocks r) := by unfold evenBlocks; infer_instance

def parityEquiv (r : ℕ) : oddBlocks r ⊕ evenBlocks r ≃ Fin r :=
  Equiv.sumCompl (fun i : Fin r => Odd (i.val+1))

@[simp] lemma parityEquiv_inl (r : ℕ) (i : oddBlocks r) :
    parityEquiv r (.inl i) = i.val := rfl
@[simp] lemma parityEquiv_inr (r : ℕ) (i : evenBlocks r) :
    parityEquiv r (.inr i) = i.val := rfl

def oddA (N : ℝ) (r : ℕ) (b : Fin r → ℕ) : Matrix (oddBlocks r) (oddBlocks r) ℝ :=
  outer (fun _ => 1) - diagonal (fun i => (N+1)/(b i.val : ℝ))

def crossX (r : ℕ) : Matrix (oddBlocks r) (evenBlocks r) ℝ :=
  fun i e => if i.val < e.val then 1 else 0

def evenD (N : ℝ) (r : ℕ) (b : Fin r → ℕ) : evenBlocks r → ℝ :=
  fun e => N/(b e.val : ℝ)

lemma B_parity (N : ℝ) (r : ℕ) (b : Fin r → ℕ) :
    (B N r b).submatrix (parityEquiv r) (parityEquiv r) =
      schurBlock (oddA N r b) (crossX r) (evenD N r b) := by
  classical
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · have hm : Odd ((min i.val j.val).val+1) := by
      rcases le_total i.val j.val with h | h
      · simpa only [min_eq_left h] using i.property
      · simpa only [min_eq_right h] using j.property
    change Odd (min i.val.val j.val.val+1) at hm
    by_cases hij : i = j
    · subst j
      simp [submatrix_apply, schurBlock, oddA, B, i.property, outer, diagonal_apply]
    · have hv : i.val ≠ j.val := fun h => hij (Subtype.ext h)
      simp [submatrix_apply, schurBlock, oddA, B, hm, outer, diagonal_apply, hij, hv]

  · have hn : i.val ≠ j.val := by
      intro h; exact j.property (h ▸ i.property)
    by_cases hl : i.val < j.val
    · simp [submatrix_apply, diagonal_apply, schurBlock, B, crossX, hn, min_eq_left hl.le,
        i.property, hl]
    · simp [submatrix_apply, diagonal_apply, schurBlock, B, crossX, hn,
        min_eq_right (le_of_not_gt hl), j.property, hl]
  · have hn : i.val ≠ j.val := by
      intro h; exact i.property (h.symm ▸ j.property)
    by_cases hl : j.val < i.val
    · simp [submatrix_apply, diagonal_apply, schurBlock, B, crossX, hn,
        min_eq_right hl.le, j.property, hl]
    · simp [submatrix_apply, diagonal_apply, schurBlock, B, crossX, hn,
        min_eq_left (le_of_not_gt hl), i.property, hl]
  · have hm : ¬ Odd ((min i.val j.val).val+1) := by
      rcases le_total i.val j.val with h | h
      · simpa only [min_eq_left h] using i.property
      · simpa only [min_eq_right h] using j.property
    change ¬ Odd (min i.val.val j.val.val+1) at hm
    by_cases hij : i = j
    · subst j
      simp [submatrix_apply, schurBlock, evenD, B, i.property, diagonal_apply, neg_div]
    · have hv : i.val ≠ j.val := fun h => hij (Subtype.ext h)
      simp [submatrix_apply, schurBlock, evenD, B, hm, diagonal_apply, hij, hv]

lemma C_schur (N : ℝ) (_hN : 0 < N) (r : ℕ) (b : Fin r → ℕ) (_hb : Valid r b) :
    schur (oddA N r b) (crossX r) (evenD N r b) = Cmat N r b := by
  classical
  ext i j
  have hs : (∑ e : evenBlocks r, (if i.val.val < e.val.val ∧ j.val.val < e.val.val then
      (b e.val : ℝ)/N else 0)) =
      ∑ e : Fin r, if Even (e.val+1) ∧ max i.val.val j.val.val < e.val then (b e : ℝ)/N else 0 := by
    have hsplit := Fintype.sum_subtype_add_sum_subtype (fun e : Fin r => ¬ Odd (e.val+1))
      (fun e => if Even (e.val+1) ∧ max i.val.val j.val.val < e.val then (b e : ℝ)/N else 0)
    have hz : (∑ e : {e : Fin r // ¬ ¬ Odd (e.val+1)},
        if Even (e.val.val+1) ∧ max i.val.val j.val.val < e.val.val then (b e.val : ℝ)/N else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro e _
      have he : ¬ Even (e.val.val+1) := Nat.not_even_iff_odd.mpr (not_not.mp e.property)
      simp [he]
    rw [hz, add_zero] at hsplit
    rw [← hsplit]
    apply Finset.sum_congr rfl
    intro e _
    have he : Even (e.val.val+1) := Nat.not_odd_iff_even.mp e.property
    simp [he, max_lt_iff]
  have hentry : (crossX r * diagonal (fun e => 1/evenD N r b e) * (crossX r)ᵀ) i j =
      ∑ e : evenBlocks r, if i.val.val < e.val.val ∧ j.val.val < e.val.val then (b e.val : ℝ)/N else 0 := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, transpose_apply, crossX, evenD]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hi : i.val < e.val <;> by_cases hj : j.val < e.val <;>
      simp [hi, hj, one_div_div]
  simp only [schur, Matrix.add_apply, oddA, Matrix.sub_apply, outer, one_mul,
    diagonal_apply, hentry, hs, Cmat]
  rw [Finset.mul_sum]
  have heq : (∑ e : Fin r, if Even (e.val+1) ∧ max i.val.val j.val.val < e.val then (b e : ℝ)/N else 0) =
      ∑ e : Fin r, 1/N * (if Even (e.val+1) ∧ max i.val.val j.val.val < e.val then (b e : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> simp [div_eq_mul_inv, mul_comm]
  rw [heq]
  ring

lemma qform_reindex {n m : Type*} [Fintype n] [Fintype m]
    (A : Matrix n n ℝ) (E : m ≃ n) (x : n → ℝ) :
    qform (A.submatrix E E) (x ∘ E) = qform A x := by
  have he : (x ∘ E) ∘ E.symm = x := by funext i; simp
  rw [qform, submatrix_mulVec_equiv, he, comp_equiv_dotProduct_comp_equiv]
  rfl

/-- The actual B form is bounded by its odd-coordinate Schur complement C. -/
theorem B_le_C (N : ℝ) (hN : 0 < N) (r : ℕ) (b : Fin r → ℕ) (hb : Valid r b)
    (y : Fin r → ℝ) :
    qform (B N r b) y ≤ qform (Cmat N r b) (fun i => y i.val) := by
  have hd : ∀ e, 0 < evenD N r b e := by
    intro e
    exact div_pos hN (by exact_mod_cast hb.1 e.val)
  have h := schur_bound (oddA N r b) (crossX r) (evenD N r b) hd (y ∘ parityEquiv r)
  rw [← B_parity, qform_reindex, C_schur N hN r b hb] at h
  exact h

/-- The C obstruction now yields a nonpositive subspace of B of codimension at most k-1. -/
theorem B_nonpositive_subspace (N : ℝ) (hN : 0 < N) (r : ℕ) (b : Fin r → ℕ)
    (hb : Valid r b) (x : oddBlocks r → ℝ) (hx : x ≠ 0) (hCx : qform (Cmat N r b) x ≤ 0) :
    ∃ Q : Submodule ℝ (Fin r → ℝ), nonpositiveOn (B N r b) Q ∧
      r < Fintype.card (oddBlocks r) + Module.finrank ℝ Q := by
  let T : (Fin r → ℝ) →ₗ[ℝ] (oddBlocks r → ℝ) := LinearMap.funLeft ℝ ℝ Subtype.val
  let L : Submodule ℝ (oddBlocks r → ℝ) := Submodule.span ℝ {x}
  refine ⟨L.comap T, ?_, ?_⟩
  · intro v hv
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (show T v ∈ Submodule.span ℝ {x} from hv)
    have h := B_le_C N hN r b hb v
    change qform (B N r b) v ≤ qform (Cmat N r b) (T v) at h
    rw [← ht, qform_smul_vec] at h
    exact h.trans (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) hCx)
  · have hl : Module.finrank ℝ L = 1 := finrank_span_singleton hx
    have h := finrank_comap_lower T L
    simp only [Module.finrank_pi, Fintype.card_fin] at h
    omega

#print axioms B_le_C
#print axioms B_nonpositive_subspace
end RFIMinimality
```

### `PairedFloor.lean`

```lean
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace RFIMinimality

/-- The real inequality behind the consecutive greedy block obstruction. -/
theorem paired_bound (N u c : ℝ) (hN : 0 < N) (hu : 0 < u)
    (hu1 : u ≤ 1) (hc : 0 < c)
    (hcle : c ≤ N * (N + 1) / (N + u) + 1) :
    1 - (N + 1) / c + (u - 1) / N ≤ 0 := by
  have hden : 0 < N + u := by linarith
  have hprod : 0 ≤ (1 - u) * (2 * N + u) :=
    mul_nonneg (by linarith) (by linarith)
  have hcv : c * (N + u - 1) ≤ N * (N + 1) := by
    by_cases hv : 0 ≤ N + u - 1
    · have hb := mul_le_mul_of_nonneg_right hcle hv
      have hid : (N * (N + 1) / (N + u) + 1) * (N + u) =
          N * (N + 1) + (N + u) := by
        field_simp
      have hbound : (N * (N + 1) / (N + u) + 1) * (N + u - 1) ≤
          N * (N + 1) := by
        apply (mul_le_mul_iff_left₀ hden).mp
        nlinarith [hprod, hid]
      exact hb.trans hbound
    · have hn : c * (N + u - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc.le (by linarith)
      exact hn.trans (by positivity)
  apply (mul_le_mul_iff_left₀ (mul_pos hc hN)).mp
  field_simp
  nlinarith [hcv]

theorem paired_floor_bound (N u : ℝ) (hN : 0 < N) (hu : 0 < u)
    (hu1 : u ≤ 1) :
    let c : ℝ := (⌊N * (N + 1) / (N + u)⌋ : ℤ) + 1
    1 - (N + 1) / c + (u - 1) / N ≤ 0 := by
  dsimp
  apply paired_bound N u _ hN hu hu1
  · have h := Int.lt_floor_add_one (N * (N + 1) / (N + u))
    have hp : 0 < N * (N + 1) / (N + u) := by positivity
    linarith
  · have h := Int.floor_le (N * (N + 1) / (N + u))
    linarith

#print axioms paired_bound
#print axioms paired_floor_bound
end RFIMinimality
```

### `RFIPivots.lean`

```lean
import RFISigns
import PairedFloor

noncomputable section
namespace RFIMinimality

/-- The greedy choice is exactly the first integer with positive odd Schur pivot. -/
theorem odd_decrement_pivot (N h : ℝ) (hN : 0 < N) (hh : h < 0)
    (hc : 0 < greedy ((N+1)/(1-h))-1) :
    1 - (N+1)/((greedy ((N+1)/(1-h))-1 : ℕ) : ℝ) - h ≤ 0 := by
  let t := (N+1)/(1-h)
  have ht : 0 ≤ t := (div_pos (by linarith) (by linarith)).le
  have ha : 0 < greedy t := greedy_pos t
  have he : ((greedy t-1 : ℕ) : ℝ) = (greedy t : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ greedy t), Nat.cast_one]
  have hcc : 0 < ((greedy t-1 : ℕ) : ℝ) := by exact_mod_cast hc
  have hbound : ((greedy t-1 : ℕ) : ℝ) ≤ (N+1)/(1-h) := by
    rw [he]
    linarith [greedy_le t ht]
  have hm := (le_div_iff₀ (by linarith : 0 < 1-h)).mp hbound
  have hd : 1-h ≤ (N+1)/((greedy t-1 : ℕ) : ℝ) :=
    (le_div_iff₀ hcc).mpr (by nlinarith [hm])
  dsimp only [t] at hd
  linarith

/-- Exact response at a greedy even step, without a matrix inverse. -/
theorem even_step_value (N s : ℝ) (hN : 0 < N) (hs : 0 < s) :
    g s (-N/(greedy (N/s) : ℝ)) = -N/((greedy (N/s) : ℝ)-N/s) := by
  have ha : 0 < (greedy (N/s) : ℝ) := by exact_mod_cast greedy_pos (N/s)
  have hu : 0 < (greedy (N/s) : ℝ)-N/s := sub_pos.mpr (lt_greedy _ (div_pos hN hs).le)
  unfold g
  field_simp
  ring

/-- The consecutive even/odd floor choices already force a nonpositive paired pivot
when the even block is reduced. This includes the equality case. -/
theorem even_pair_pivot (N s : ℝ) (hN : 0 < N) (hs : 0 < s) :
    let b := greedy (N/s)
    let c := greedy ((N+1)/(1-1/(g s (-N/(b : ℝ)))))
    1-(N+1)/(c : ℝ)+(((b : ℝ)-N/s)-1)/N ≤ 0 := by
  dsimp only
  let u := (greedy (N/s) : ℝ)-N/s
  have ht : 0 ≤ N/s := (div_pos hN hs).le
  have hu : 0 < u := sub_pos.mpr (lt_greedy _ ht)
  have hu1 : u ≤ 1 := by dsimp [u]; linarith [greedy_le (N/s) ht]
  have harg : (N+1)/(1-1/(g s (-N/(greedy (N/s) : ℝ)))) = N*(N+1)/(N+u) := by
    rw [even_step_value N s hN hs]
    change (N+1)/(1-1/(-N/u)) = N*(N+1)/(N+u)
    field_simp [ne_of_gt hN, ne_of_gt hu, ne_of_gt (add_pos hN hu)]
    ring
  rw [harg]
  change 1-(N+1)/(greedy (N*(N+1)/(N+u)) : ℝ)+(u-1)/N ≤ 0
  apply paired_bound N u _ hN hu hu1
  · exact_mod_cast greedy_pos (N*(N+1)/(N+u))
  · exact greedy_le _ (by positivity)

#print axioms odd_decrement_pivot
#print axioms even_step_value
#print axioms even_pair_pivot
end RFIMinimality
```

### `RFIAssembly.lean`

```lean
import RFIParitySchur
import RFISigns

noncomputable section
namespace RFIMinimality
open Matrix

lemma valid_mono (r : ℕ) (a b : Fin r → ℕ) (hb : Valid r b) (hle : ∀ i, b i ≤ a i) :
    Valid r a := by
  exact ⟨fun i => (hb.1 i).trans (hle i), fun h => (hb.2 h).trans (hle _)⟩

/-- The full graph subspace required in DESIGN, proved directly from the Schur obstruction. -/
theorem nonpositive_subspace (N : ℝ) (hN : 0 < N) (r : ℕ) (_hr : 2 ≤ r)
    (b : Fin r → ℕ) (hb : Valid r b)
    (x : oddBlocks r → ℝ) (hx : x ≠ 0) (hCx : qform (Cmat N r b) x ≤ 0) :
    ∃ Q : Submodule ℝ ((Σ i : Fin r, Fin (b i)) → ℝ),
      nonpositiveOn ((TG r b).adjMatrix ℝ - N • 1) Q ∧
      Fintype.card (Σ i : Fin r, Fin (b i)) <
        Fintype.card (oddBlocks r) + Module.finrank ℝ Q := by
  obtain ⟨Q,hQ,hQd⟩ := B_nonpositive_subspace N hN r b hb x hx hCx
  let T := (aggregate r b).mulVecLin
  refine ⟨Q.comap T, ?_, ?_⟩
  · intro v hv
    exact (graph_form_le N hN.le r b hb v).trans (hQ (T v) hv)
  · have h := finrank_comap_lower T Q
    simp only [Module.finrank_pi, Fintype.card_fin] at h
    omega

/-- Once a k-dimensional positive B(0) subspace is provided, the C obstruction
has a literal adjacency eigenvector in the source's interval. -/
theorem eigenvalue_of_C_obstruction_of_positive
    (N : ℝ) (hN : 0 < N) (r : ℕ) (b : Fin r → ℕ) (hb : Valid r b)
    (hpos : ∃ P : Submodule ℝ (Fin r → ℝ), positiveOn (B 0 r b) P ∧
      Module.finrank ℝ P = Fintype.card (oddBlocks r))
    (x : oddBlocks r → ℝ) (hx : x ≠ 0) (hCx : qform (Cmat N r b) x ≤ 0) :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ N ∧ ∃ v : (Σ i, Fin (b i)) → ℝ,
      v ≠ 0 ∧ (TG r b).adjMatrix ℝ *ᵥ v = μ • v := by
  obtain ⟨P,hP,hPd⟩ := hpos
  obtain ⟨Q,hQ,hQd⟩ := B_nonpositive_subspace N hN r b hb x hx hCx
  apply interval_eigenvalue_of_block_subspaces N hN r b hb P Q hP hQ
  omega

/-- Formal assembly of the exact endpoint from two explicit remaining inputs.
This is a conditional helper, not a proof of the conjecture. -/
theorem minimality_of_positive_and_decrements
    (N : ℝ) (hN : 0 < N) (r : ℕ) (_hr : 2 ≤ r)
    (hpositive : ∀ b : Fin r → ℕ, Valid r b →
      ∃ P : Submodule ℝ (Fin r → ℝ), positiveOn (B 0 r b) P ∧
        Module.finrank ℝ P = Fintype.card (oddBlocks r))
    (hdecrements : ∀ i : Fin r, Valid r (decrement (rfiInitial N r) i) →
      ∃ x : oddBlocks r → ℝ, x ≠ 0 ∧
        qform (Cmat N r (decrement (rfiInitial N r) i)) x ≤ 0)
    (b : Fin r → ℕ) (hb : Valid r b) (hle : ∀ i, b i ≤ rfiInitial N r i)
    (hfree : ∀ μ : ℝ, 0 < μ → μ ≤ N →
       ¬ ∃ v : (Σ i : Fin r, Fin (b i)) → ℝ,
         v ≠ 0 ∧ (TG r b).adjMatrix ℝ *ᵥ v = μ • v) :
    b = rfiInitial N r := by
  classical
  by_contra hne
  have hex : ∃ i, b i < rfiInitial N r i := by
    by_contra hh
    apply hne
    funext i
    have h := not_exists.mp hh i
    exact Nat.le_antisymm (hle i) (Nat.le_of_not_gt h)
  obtain ⟨i,hi⟩ := hex
  have hbd : ∀ j, b j ≤ decrement (rfiInitial N r) i j := by
    intro j
    by_cases hji : j = i
    · subst j
      simp only [decrement, Function.update_self]
      omega
    · simpa only [decrement, Function.update_of_ne hji] using hle j
  have hdv := valid_mono r (decrement (rfiInitial N r) i) b hb hbd
  obtain ⟨x,hx,hCx⟩ := hdecrements i hdv
  have hCb : qform (Cmat N r b) x ≤ 0 :=
    (C_mono N hN r _ b hdv hb hbd x).trans hCx
  obtain ⟨μ,hμ,hμN,v,hv,he⟩ :=
    eigenvalue_of_C_obstruction_of_positive N hN r b hb (hpositive b hb) x hx hCb
  exact hfree μ hμ hμN ⟨v,hv,he⟩

#print axioms nonpositive_subspace
#print axioms eigenvalue_of_C_obstruction_of_positive
#print axioms minimality_of_positive_and_decrements
end RFIMinimality
```

### `RFITarget.lean`

```lean
import RFIAssembly
import RFIExamples
import RFIPivots

namespace RFIMinimality
open Matrix

/-- Literal requested endpoint proposition. This declaration is a definition,
not a theorem establishing it. The proof remains a continuation task. -/
def Conjecture352345 : Prop :=
  ∀ (N : ℝ), 0 < N → ∀ (r : ℕ), 2 ≤ r → ∀ (b : Fin r → ℕ),
    Valid r b → (∀ i, b i ≤ rfiInitial N r i) →
    (∀ μ : ℝ, 0 < μ → μ ≤ N →
       ¬ ∃ v : (Σ i : Fin r, Fin (b i)) → ℝ,
         v ≠ 0 ∧ (TG r b).adjMatrix ℝ *ᵥ v = μ • v) →
    b = rfiInitial N r

#print Conjecture352345
#print axioms Conjecture352345
#eval Lean.versionString
end RFIMinimality
```

### `RFIPositive.lean`

```lean
import RFIAssembly
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace RFIMinimality
open Matrix

lemma qform_cons {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (t : ℝ) (y : Fin n → ℝ) :
    qform A (Fin.cons t y) = A 0 0*t^2 +
      t * (∑ i, A 0 i.succ * y i) +
      t * (∑ i, A i.succ 0 * y i) +
      qform (A.submatrix Fin.succ Fin.succ) y := by
  simp only [qform, mulVec, dotProduct, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ, submatrix_apply]
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_mul]
  simp only [mul_comm, mul_left_comm, mul_assoc]
  ring

lemma B_pair_form (n : ℕ) (b : Fin (n+2) → ℕ) (t u : ℝ) (y : Fin n → ℝ) :
    qform (B 0 (n+2) b) (Fin.cons t (Fin.cons u y)) =
      (1-1/(b 0 : ℝ))*t^2 + 2*t*(u+∑ i, y i) +
      qform (B 0 n (fun i => b i.succ.succ)) y := by
  classical
  rw [qform_cons, qform_cons]
  have ho : Odd (1 : ℕ) := by decide
  have he : ¬ Odd (2 : ℕ) := by decide
  have htail : ((B 0 (n+2) b).submatrix Fin.succ Fin.succ).submatrix Fin.succ Fin.succ =
      B 0 n (fun i => b i.succ.succ) := by
    ext i j
    simp only [submatrix_apply, B, Fin.succ_inj, Fin.val_succ]
    have hp (k : ℕ) : Odd (k+1+1+1) ↔ Odd (k+1) := by
      simp only [Nat.odd_iff]; omega
    simp only [hp]
    have hm : min i.succ.succ j.succ.succ = (min i j).succ.succ := by
      apply Fin.ext; simp
    simp only [hm, Fin.val_succ, hp]
  have h0 (i : Fin (n+1)) : B 0 (n+2) b 0 i.succ = 1 ∧
      B 0 (n+2) b i.succ 0 = 1 := by
    have hn : (0 : Fin (n+2)) ≠ i.succ := by
      intro h; have hh := congrArg Fin.val h; simp at hh
    simp [B, ho, hn]
  have h1 (i : Fin n) : B 0 (n+2) b 1 i.succ.succ = 0 ∧
      B 0 (n+2) b i.succ.succ 1 = 0 := by
    have hne : (1 : Fin (n+2)) ≠ i.succ.succ := by
      intro h; have := congrArg Fin.val h; simp at this
    have hl : (1 : Fin (n+2)) ≤ i.succ.succ := by simp [Fin.le_def]
    simp [B, hne, Ne.symm hne, min_eq_left hl, min_eq_right hl, he]
  simp only [submatrix_apply, htail, (h0 _).1, (h0 _).2, one_mul]
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  simp only [show (0 : Fin (n+1)).succ = (1 : Fin (n+2)) from rfl,
    (h1 _).1, (h1 _).2, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
  simp [B, ho, he]
  ring

lemma odd_card_sum (r : ℕ) : Fintype.card (oddBlocks r) =
    ∑ i : Fin r, if Odd (i.val+1) then 1 else 0 := by
  classical
  exact (Fintype.card_subtype (fun i : Fin r => Odd (i.val+1))).trans (by simp)

lemma odd_card_pair (n : ℕ) :
    Fintype.card (oddBlocks (n+2)) = 1 + Fintype.card (oddBlocks n) := by
  classical
  simp only [odd_card_sum, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
  have hp (k : ℕ) : Odd (k+1+1+1) ↔ Odd (k+1) := by
    simp only [Nat.odd_iff]; omega
  simp only [hp]
  norm_num

/-- Explicit injection which adds one positive square for each new odd/even pair. -/
def positivePairMap (n : ℕ) (P : Submodule ℝ (Fin n → ℝ)) :
    (ℝ × P) →ₗ[ℝ] (Fin (n+2) → ℝ) where
  toFun z := Fin.cons z.1 (Fin.cons (z.1 - ∑ i, (z.2 : Fin n → ℝ) i) z.2)
  map_add' z w := by
    ext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;>
      simp [Finset.sum_add_distrib] <;> ring
  map_smul' t z := by
    ext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;>
      simp [Finset.sum_add_distrib, Finset.sum_mul, ← Finset.mul_sum] <;> ring

lemma positivePairMap_injective (n : ℕ) (P : Submodule ℝ (Fin n → ℝ)) :
    Function.Injective (positivePairMap n P) := by
  intro z w h
  apply Prod.ext
  · exact congrFun h 0
  · apply Subtype.ext
    funext i
    exact congrFun h i.succ.succ

/-- All valid block vectors have one strictly positive direction per odd block. -/
theorem B_positive_subspace (r : ℕ) (b : Fin r → ℕ) (hb : Valid r b) :
    ∃ P : Submodule ℝ (Fin r → ℝ), positiveOn (B 0 r b) P ∧
      Module.finrank ℝ P = Fintype.card (oddBlocks r) := by
  classical
  induction r using Nat.strong_induction_on with
  | h r ih =>
    rcases r with _ | r
    · refine ⟨⊥, ?_, ?_⟩
      · intro x hx hne
        exact False.elim (hne ((by simpa using hx)))
      · simp [odd_card_sum]
    rcases r with _ | n
    · refine ⟨⊤, ?_, ?_⟩
      · intro x _ hx
        have hx0 : x 0 ≠ 0 := by
          intro he
          apply hx
          funext i
          have hi : i = 0 := by apply Fin.ext; omega
          simpa [hi] using he
        have hb0 : (2 : ℝ) ≤ b 0 := by exact_mod_cast hb.2 (by omega)
        have hc : 0 < 1-1/(b 0 : ℝ) := by
          have : 1/(b 0 : ℝ) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
          linarith
        simpa [qform, mulVec, dotProduct, B, Fin.sum_univ_one, pow_two, mul_comm, mul_left_comm, mul_assoc] using
          mul_pos hc (sq_pos_of_ne_zero hx0)
      · simp [odd_card_sum, Fin.sum_univ_one]
    · let c : Fin n → ℕ := fun i => b i.succ.succ
      have hc : Valid n c := by
        refine ⟨fun i => hb.1 _, ?_⟩
        intro hn
        have hh := hb.2 (by omega : 0 < n+2)
        convert hh using 1
        change b (Fin.succ (Fin.succ _)) = b _
        congr 1
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      obtain ⟨P,hP,hPd⟩ := ih n (by omega) c hc
      let T := positivePairMap n P
      refine ⟨T.range, ?_, ?_⟩
      · intro v hv hvne
        obtain ⟨⟨t,y⟩,rfl⟩ := hv
        change 0 < qform (B 0 (n+2) b) (Fin.cons t (Fin.cons (t-∑ i, (y : Fin n → ℝ) i) y))
        rw [B_pair_form]
        have hb0 : (1 : ℝ) ≤ b 0 := by exact_mod_cast hb.1 0
        have hcoef : 0 < 3-1/(b 0 : ℝ) := by
          have : 1/(b 0 : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr hb0
          linarith
        have hid : (1-1/(b 0 : ℝ))*t^2 + 2*t*(t-(∑ i, (y : Fin n → ℝ) i)+∑ i, (y : Fin n → ℝ) i) =
            (3-1/(b 0 : ℝ))*t^2 := by ring
        rw [hid]
        by_cases hy : (y : Fin n → ℝ) = 0
        · have ht : t ≠ 0 := by
            intro ht
            apply hvne
            ext i
            refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;>
              simp [T, positivePairMap, ht, hy]
          have hq : qform (B 0 n c) y = 0 := by simp [hy, qform]
          change 0 < (3-1/(b 0 : ℝ))*t^2 + qform (B 0 n c) y
          rw [hq, add_zero]
          exact mul_pos hcoef (sq_pos_of_ne_zero ht)
        · exact add_pos_of_nonneg_of_pos (mul_nonneg hcoef.le (sq_nonneg t)) (hP y y.property hy)
      · have hd := LinearMap.finrank_range_of_inj (positivePairMap_injective n P)
        rw [hd]
        simp only [Module.finrank_prod, Module.finrank_self, hPd, odd_card_pair]

/-- The positive directions lift to the literal adjacency matrix. -/
theorem positive_subspace (r : ℕ) (_hr : 2 ≤ r) (b : Fin r → ℕ) (hb : Valid r b) :
    ∃ P : Submodule ℝ ((Σ i : Fin r, Fin (b i)) → ℝ),
      positiveOn ((TG r b).adjMatrix ℝ) P ∧
      Module.finrank ℝ P = Fintype.card (oddBlocks r) := by
  obtain ⟨P,hP,hPd⟩ := B_positive_subspace r b hb
  refine ⟨P.map (blockLiftLinear r b), ?_, ?_⟩
  · intro v hv hvne
    obtain ⟨y,hy,rfl⟩ := hv
    have hyne : y ≠ 0 := by intro he; simp [he] at hvne
    have hh := block_form 0 r b hb y
    simp only [zero_smul, sub_zero] at hh
    change 0 < qform ((TG r b).adjMatrix ℝ) (blockLift b y)
    rw [hh]
    exact hP y hy hyne
  · rw [← hPd]
    exact (Submodule.equivMapOfInjective (blockLiftLinear r b) (blockLift_injective r b hb) P).finrank_eq.symm

theorem eigenvalue_of_C_obstruction (N : ℝ) (hN : 0 < N) (r : ℕ) (_hr : 2 ≤ r)
    (b : Fin r → ℕ) (hb : Valid r b)
    (x : oddBlocks r → ℝ) (hx : x ≠ 0) (hCx : qform (Cmat N r b) x ≤ 0) :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ N ∧ ∃ v, v ≠ 0 ∧ (TG r b).adjMatrix ℝ *ᵥ v = μ • v := by
  exact eigenvalue_of_C_obstruction_of_positive N hN r b hb (B_positive_subspace r b hb) x hx hCx

#print axioms B_positive_subspace
#print axioms positive_subspace
#print axioms eigenvalue_of_C_obstruction

end RFIMinimality
```

### `RFIResponse.lean`

```lean
import RFIAssembly

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace RFIMinimality
open Matrix

lemma B_earlier (N : ℝ) (r : ℕ) (b : Fin r → ℕ) (j i : Fin r) (hji : j < i) :
    B N r b j i = (if Odd (j.val+1) then 1 else 0) ∧
    B N r b i j = (if Odd (j.val+1) then 1 else 0) := by
  simp [B, ne_of_lt hji, ne_of_gt hji, min_eq_left hji.le, min_eq_right hji.le]

lemma B_head_response (N : ℝ) (r : ℕ) (b : Fin r → ℕ) (j : Fin r)
    (w : Fin r → ℝ) (hw : ∀ i, i ≤ j → w i = 0) :
    (B N r b *ᵥ w) j = (if Odd (j.val+1) then 1 else 0) * ∑ i, w i := by
  classical
  simp only [mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ≤ j
  · simp [hw i hi]
  · rw [(B_earlier N r b j i (lt_of_not_ge hi)).1]

/-- A response vector for a suffix, extended by zero to the original index set. -/
def Response (N : ℝ) (r : ℕ) (b : Fin r → ℕ) (j : ℕ) (h : ℝ) : Prop :=
  ∃ w : Fin r → ℝ, (∀ i, i.val < j → w i = 0) ∧
    (∀ i, j ≤ i.val → (B N r b *ᵥ w) i = 1) ∧ ∑ i, w i = h

lemma response_extend (N : ℝ) (r : ℕ) (b : Fin r → ℕ) (j : Fin r) (h c t : ℝ)
    (hr : Response N r b (j.val+1) h)
    (hc : B N r b j j*c + (if Odd (j.val+1) then 1 else 0)*t*h = 1)
    (ht : (if Odd (j.val+1) then 1 else 0)*c + t = 1) :
    Response N r b j.val (c+t*h) := by
  classical
  obtain ⟨w,hw,he,hs⟩ := hr
  let v : Fin r → ℝ := c • Pi.single j 1 + t • w
  have hm (i : Fin r) : (B N r b *ᵥ v) i = B N r b i j*c + t*(B N r b *ᵥ w) i := by
    simp [v, mulVec_add, mulVec_smul, mulVec_single, smul_eq_mul, mul_comm]
  refine ⟨v, ?_, ?_, ?_⟩
  · intro i hi
    have hij : i ≠ j := by intro hh; subst i; omega
    simp [v, Pi.single_eq_of_ne hij, hw i (by omega)]
  · intro i hi
    rw [hm]
    by_cases hij : i = j
    · subst i
      rw [B_head_response N r b j w (fun k hk => hw k (by have hh : k.val ≤ j.val := hk; omega)), hs]
      nlinarith [hc]
    · have hji : j < i := by exact_mod_cast (show j.val < i.val by omega)
      rw [(B_earlier N r b j i hji).2, he i (by omega)]
      simpa using ht
  · simp only [v, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [hs]

lemma response_even (N : ℝ) (r : ℕ) (b : Fin r → ℕ) (j : Fin r) (s : ℝ)
    (hj : ¬ Odd (j.val+1)) (hs : s ≠ 0) (hy : -N/(b j : ℝ) ≠ 0)
    (hr : Response N r b (j.val+1) (1/s)) :
    Response N r b j.val (1/g s (-N/(b j : ℝ))) := by
  have hb : (b j : ℝ) ≠ 0 := (div_ne_zero_iff.mp hy).2
  have hN : N ≠ 0 := neg_ne_zero.mp (div_ne_zero_iff.mp hy).1
  have heq : 1/(-N/(b j : ℝ)) + 1*(1/s) = 1/g s (-N/(b j : ℝ)) := by
    simp only [g, one_div_div]
    field_simp
    <;> ring
  rw [← heq]
  apply response_extend N r b j (1/s) (1/(-N/(b j : ℝ))) 1 hr
  · rw [show B N r b j j = -N/(b j : ℝ) by simp [B, hj]]
    simp only [ite_eq_right hj, zero_mul, add_zero]
    field_simp
  · simp [hj]

lemma response_odd (N : ℝ) (r : ℕ) (b : Fin r → ℕ) (j : Fin r) (s : ℝ)
    (hj : Odd (j.val+1)) (hs : s ≠ 0)
    (hp : 1-(N+1)/(b j : ℝ) - 1/s ≠ 0)
    (hr : Response N r b (j.val+1) (1/s)) :
    Response N r b j.val (1/f s (1-(N+1)/(b j : ℝ))) := by
  let y := 1-(N+1)/(b j : ℝ)
  have hp' : y - 1/s ≠ 0 := hp
  have hn : s*y-1 ≠ 0 := by
    intro hh
    apply hp'
    apply (sub_eq_zero.mpr ((eq_div_iff hs).mpr (by nlinarith)))
  have heq : (1-1/s)/(y-1/s) + (y-1)/(y-1/s)*(1/s) = 1/f s y := by
    unfold f
    field_simp
    <;> ring
  rw [← heq]
  apply response_extend N r b j (1/s) ((1-1/s)/(y-1/s)) ((y-1)/(y-1/s)) hr
  · rw [show B N r b j j = y by simp [B, hj, y]]
    rw [ite_eq_left hj]
    calc
      _ = (y-1/s)/(y-1/s) := by ring
      _ = 1 := div_self hp'
  · rw [ite_eq_left hj]
    calc
      _ = (y-1/s)/(y-1/s) := by ring
      _ = 1 := div_self hp'

lemma response_last (N : ℝ) (r : ℕ) (b : Fin r → ℕ) (j : Fin r)
    (hj : j.val+1 = r) (hs : B N r b j j ≠ 0) :
    Response N r b j.val (1/(B N r b j j)) := by
  classical
  have hr : Response N r b (j.val+1) 0 := by
    refine ⟨0, fun _ _ => rfl, ?_, by simp⟩
    intro i hi
    omega
  have hh := response_extend N r b j 0 (1/(B N r b j j))
    (1-(if Odd (j.val+1) then 1 else 0)*(1/(B N r b j j))) hr
    (by simp [hs]) (by ring)
  simpa using hh

/-- Constructive suffix response: no inverse is needed by the decrement argument. -/
theorem rfi_response_state (N : ℝ) (hN : 0 < N) (r d : ℕ) (hd : d < r) :
    Response N r (rfiInitial N r) (r-1-d) (1/(rfiState N r d).2) := by
  induction d with
  | zero =>
    let j : Fin r := ⟨r-1, by omega⟩
    have hdiag : B N r (rfiInitial N r) j j = (rfiState N r 0).2 := by
      have hj : j.val+1 = r := by dsimp [j]; omega
      simp only [B, ite_eq_left rfl, hj, rfiInitial, j, Nat.sub_self, rfiState]
      split_ifs with ho <;> simp [add_comm]
    have hs : (rfiState N r 0).2 ≠ 0 := by
      by_cases ho : Odd r
      · exact ne_of_gt ((rfi_signs N hN r 0 hd).2.1 (by simpa using ho))
      · exact ne_of_lt ((rfi_signs N hN r 0 hd).2.2 (by simpa using Nat.not_odd_iff_even.mp ho))
    have hh := response_last N r (rfiInitial N r) j (by dsimp [j]; omega) (hdiag ▸ hs)
    simpa only [hdiag, j, Nat.sub_zero] using hh
  | succ d ih =>
    let j : Fin r := ⟨r-1-(d+1), by omega⟩
    let s := (rfiState N r d).2
    have hj : j.val+1 = r-(d+1) := by dsimp [j]; omega
    have hind : Response N r (rfiInitial N r) (j.val+1) (1/s) := by
      have hi := ih (by omega)
      convert hi using 1 <;> dsimp [j] <;> omega
    have hidx : r-1-j.val = d+1 := by dsimp [j]; omega
    by_cases ho : Odd (j.val+1)
    · have he : Even (r-d) := by
        rw [Nat.even_iff]
        have hh := Nat.odd_iff.mp ho
        omega
      have hs : s < 0 := (rfi_signs N hN r d (by omega)).2.2 he
      have hsize : rfiInitial N r j = greedy ((N+1)/(1-1/s)) := by
        simp only [rfiInitial, hidx, rfiState, ← hj, ite_eq_left ho]
        rfl
      have hstep : (rfiState N r (d+1)).2 = f s (1-(N+1)/(rfiInitial N r j : ℝ)) := by
        rw [hsize]
        simp only [rfiState, ← hj, ite_eq_left ho]
        rfl
      have hp : 1-(N+1)/(rfiInitial N r j : ℝ) - 1/s ≠ 0 := by
        intro hh
        have hxy : s*(1-(N+1)/(rfiInitial N r j : ℝ))-1 = 0 := by
          have hx := sub_eq_zero.mp hh
          rw [hx]
          field_simp [ne_of_lt hs]
          ring
        have hpos := (rfi_signs N hN r (d+1) hd).2.1 (by simpa only [← hj] using ho)
        rw [hstep, f, hxy, zero_div] at hpos
        exact (lt_irrefl 0 hpos)
      have hh := response_odd N r (rfiInitial N r) j s ho (ne_of_lt hs) hp hind
      simpa only [hstep, j] using hh
    · have hoo : Odd (r-d) := by
        rw [Nat.odd_iff]
        have hh := Nat.even_iff.mp (Nat.not_odd_iff_even.mp ho)
        omega
      have hs : 0 < s := (rfi_signs N hN r d (by omega)).2.1 hoo
      have hsize : rfiInitial N r j = greedy (N/s) := by
        simp only [rfiInitial, hidx, rfiState, ← hj, ite_eq_right ho]
        rfl
      have hstep : (rfiState N r (d+1)).2 = g s (-N/(rfiInitial N r j : ℝ)) := by
        rw [hsize]
        simp only [rfiState, ← hj, ite_eq_right ho]
        rfl
      have hy : -N/(rfiInitial N r j : ℝ) ≠ 0 := by
        apply div_ne_zero (ne_of_lt (neg_neg_of_pos hN))
        rw [hsize]
        exact_mod_cast Nat.ne_of_gt (greedy_pos (N/s))
      have hh := response_even N r (rfiInitial N r) j s ho (ne_of_gt hs) hy hind
      simpa only [hstep, j] using hh

theorem suffix_response_vector (N : ℝ) (hN : 0 < N) (r j : ℕ) (hj : j < r) :
    Response N r (rfiInitial N r) j (1/(rfiState N r (r-1-j)).2) := by
  have hh := rfi_response_state N hN r (r-1-j) (by omega)
  simpa only [show r-1-(r-1-j) = j by omega] using hh

#print axioms rfi_response_state
#print axioms suffix_response_vector

end RFIMinimality
```

### `RFIWitness.lean`

```lean
import RFIResponse

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace RFIMinimality
open Matrix

lemma schur_eq_of_stationary {o e : Type*} [Fintype o] [Fintype e] [DecidableEq e]
    (A : Matrix o o ℝ) (X : Matrix o e ℝ) (d : e → ℝ) (hd : ∀ j, d j ≠ 0)
    (x : o → ℝ) (y : e → ℝ) (hy : ∀ j, (Xᵀ *ᵥ x) j = d j*y j) :
    qform (schurBlock A X d) (Sum.elim x y) = qform (schur A X d) x := by
  rw [schurBlock_form, schur_form]
  have hh : 2*dotProduct (Xᵀ *ᵥ x) y - ∑ j, d j*(y j)^2 =
      ∑ j, ((Xᵀ *ᵥ x) j)^2/d j := by
    unfold dotProduct
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hy j]
    field_simp
    <;> ring
  linarith

lemma B_even_row (N : ℝ) (r : ℕ) (b : Fin r → ℕ) (v : Fin r → ℝ) (e : evenBlocks r) :
    (B N r b *ᵥ v) e.val =
      ((crossX r)ᵀ *ᵥ (fun i : oddBlocks r => v i.val)) e - evenD N r b e * v e.val := by
  have heq := congrArg (fun A => (A *ᵥ (v ∘ parityEquiv r)) (.inr e)) (B_parity N r b)
  rw [submatrix_mulVec_equiv] at heq
  have hcomp : (v ∘ parityEquiv r) ∘ (parityEquiv r).symm = v := by funext i; simp
  rw [hcomp] at heq
  have hv : (v ∘ parityEquiv r) = Sum.elim (fun i : oddBlocks r => v i.val)
      (fun i : evenBlocks r => v i.val) := by funext i; cases i <;> rfl
  rw [hv] at heq
  simpa [schurBlock, fromBlocks_mulVec, evenD, Function.comp_def, neg_mulVec,
    mulVec_diagonal, sub_eq_add_neg] using heq

lemma B_eq_C_of_even_stationary (N : ℝ) (hN : 0 < N) (r : ℕ)
    (b : Fin r → ℕ) (hb : Valid r b) (v : Fin r → ℝ)
    (hv : ∀ e : evenBlocks r, (B N r b *ᵥ v) e.val = 0) :
    qform (B N r b) v = qform (Cmat N r b) (fun i => v i.val) := by
  have hstat : ∀ e, ((crossX r)ᵀ *ᵥ (fun i : oddBlocks r => v i.val)) e =
      evenD N r b e * v e.val := by
    intro e
    have hh := B_even_row N r b v e
    rw [hv e] at hh
    linarith
  have hd : ∀ e, evenD N r b e ≠ 0 := by
    intro e; exact ne_of_gt (div_pos hN (by exact_mod_cast hb.1 e.val))
  rw [← qform_reindex (B N r b) (parityEquiv r), B_parity]
  have hh := schur_eq_of_stationary (oddA N r b) (crossX r) (evenD N r b) hd
    (fun i : oddBlocks r => v i.val) (fun e : evenBlocks r => v e.val) hstat
  have hvv : v ∘ parityEquiv r = Sum.elim (fun i : oddBlocks r => v i.val)
      (fun e : evenBlocks r => v e.val) := by funext i; cases i <;> rfl
  rw [hvv, hh, C_schur N hN r b hb]

lemma response_congr (N : ℝ) (r : ℕ) (a b : Fin r → ℕ) (j : ℕ) (h : ℝ)
    (hab : ∀ i : Fin r, j ≤ i.val → a i = b i) :
    Response N r a j h → Response N r b j h := by
  rintro ⟨w,hw,he,hs⟩
  refine ⟨w,hw,?_,hs⟩
  intro i hi
  rw [← he i hi]
  unfold mulVec dotProduct
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  by_cases hik : i = k
  · subst k; simp [B, hab i hi]
  · simp [B, hik]

lemma B_early_even_zero (N : ℝ) (r : ℕ) (b : Fin r → ℕ) (e : Fin r)
    (he : ¬ Odd (e.val+1)) (v : Fin r → ℝ) (hv : ∀ k, k ≤ e → v k = 0) :
    (B N r b *ᵥ v) e = 0 := by
  unfold mulVec dotProduct
  apply Finset.sum_eq_zero
  intro k _
  change B N r b e k * v k = 0
  by_cases hk : k ≤ e
  · simp [hv k hk]
  · rw [(B_earlier N r b e k (lt_of_not_ge hk)).1]
    simp [he]

/-- A nonpositive odd Schur pivot is a literal C-vector obstruction. -/
theorem odd_response_obstruction (N : ℝ) (hN : 0 < N) (r : ℕ)
    (b : Fin r → ℕ) (hb : Valid r b) (j : Fin r) (hj : Odd (j.val+1)) (h : ℝ)
    (hr : Response N r b (j.val+1) h) (hp : B N r b j j - h ≤ 0) :
    ∃ x : oddBlocks r → ℝ, x ≠ 0 ∧ qform (Cmat N r b) x ≤ 0 := by
  classical
  obtain ⟨w,hw,he,hs⟩ := hr
  let v : Fin r → ℝ := Pi.single j 1 - w
  have hvj : v j = 1 := by simp [v, hw j (by omega)]
  have hvsmall : ∀ k, k < j → v k = 0 := by
    intro k hk
    simp [v, Pi.single_eq_of_ne (ne_of_lt hk), hw k (by have hh : k.val < j.val := hk; omega)]
  have hm (i : Fin r) : (B N r b *ᵥ v) i = B N r b i j - (B N r b *ᵥ w) i := by
    simp [v, mulVec_sub, mulVec_single]
  have hmlarge : ∀ i, j < i → (B N r b *ᵥ v) i = 0 := by
    intro i hi
    rw [hm, (B_earlier N r b j i hi).2, he i (by have hh : j.val < i.val := hi; omega)]
    simp [hj]
  have hmj : (B N r b *ᵥ v) j = B N r b j j - h := by
    rw [hm, B_head_response N r b j w (fun k hk => hw k (by have hh : k.val ≤ j.val := hk; omega)), hs]
    simp [hj]
  have hq : qform (B N r b) v = B N r b j j - h := by
    unfold qform dotProduct
    rw [Finset.sum_eq_single j]
    · rw [hvj, hmj, one_mul]
    · intro i _ hij
      by_cases hi : i < j
      · simp [hvsmall i hi]
      · simp [hmlarge i (lt_of_le_of_ne (le_of_not_gt hi) (Ne.symm hij))]
    · simp
  have hstat : ∀ e : evenBlocks r, (B N r b *ᵥ v) e.val = 0 := by
    intro e
    have hne : e.val ≠ j := by intro hh; exact e.property (hh ▸ hj)
    by_cases hearly : e.val < j
    · exact B_early_even_zero N r b e.val e.property v (fun k hk => hvsmall k (lt_of_le_of_lt hk hearly))
    · exact hmlarge e.val (lt_of_le_of_ne (le_of_not_gt hearly) (Ne.symm hne))
  refine ⟨fun i => v i.val, ?_, ?_⟩
  · intro hh
    have hhj := congrFun hh (⟨j,hj⟩ : oddBlocks r)
    change v j = 0 at hhj
    rw [hvj] at hhj
    norm_num at hhj
  · rw [← B_eq_C_of_even_stationary N hN r b hb v hstat, hq]
    exact hp

#print axioms B_eq_C_of_even_stationary
#print axioms odd_response_obstruction

end RFIMinimality
```

### `RFIDecrement.lean`

```lean
import RFIWitness
import RFIPivots

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace RFIMinimality
open Matrix

lemma initial_step (N : ℝ) (r : ℕ) (i : Fin r) (hi : i.val+1 < r) :
    rfiInitial N r i = if Odd (i.val+1) then
      greedy ((N+1)/(1-1/(rfiState N r (r-2-i.val)).2))
    else greedy (N/(rfiState N r (r-2-i.val)).2) := by
  have hidx : r-1-i.val = (r-2-i.val)+1 := by omega
  have hpar : r-((r-2-i.val)+1) = i.val+1 := by omega
  simp only [rfiInitial, hidx, rfiState, hpar]
  split_ifs <;> rfl

lemma initial_state_step (N : ℝ) (r : ℕ) (i : Fin r) (hi : i.val+1 < r) :
    (rfiState N r (r-1-i.val)).2 = if Odd (i.val+1) then
      f (rfiState N r (r-2-i.val)).2 (1-(N+1)/(rfiInitial N r i : ℝ))
    else g (rfiState N r (r-2-i.val)).2 (-N/(rfiInitial N r i : ℝ)) := by
  rw [initial_step N r i hi]
  have hidx : r-1-i.val = (r-2-i.val)+1 := by omega
  have hpar : r-((r-2-i.val)+1) = i.val+1 := by omega
  rw [hidx, rfiState, hpar]
  split_ifs <;> rfl

lemma response_decrement_tail (N : ℝ) (hN : 0 < N) (r : ℕ) (i : Fin r)
    (hi : i.val+1 < r) :
    Response N r (decrement (rfiInitial N r) i) (i.val+1)
      (1/(rfiState N r (r-2-i.val)).2) := by
  have hh := suffix_response_vector N hN r (i.val+1) hi
  have hidx : r-1-(i.val+1) = r-2-i.val := by omega
  rw [hidx] at hh
  apply response_congr N r (rfiInitial N r) _ (i.val+1) _ ?_ hh
  intro k hk
  have hki : k ≠ i := by intro he; subst k; omega
  simp [decrement, Function.update_of_ne hki]

theorem odd_decrement (N : ℝ) (hN : 0 < N) (r : ℕ) (_hr : 2 ≤ r)
    (i : Fin r) (hi : Odd (i.val+1))
    (hv : Valid r (decrement (rfiInitial N r) i)) :
    ∃ x : oddBlocks r → ℝ, x ≠ 0 ∧
      qform (Cmat N r (decrement (rfiInitial N r) i)) x ≤ 0 := by
  classical
  let b := decrement (rfiInitial N r) i
  have hbi : 0 < (rfiInitial N r i-1 : ℕ) := by
    have hh : 1 ≤ rfiInitial N r i-1 := by simpa [decrement] using hv.1 i
    omega
  by_cases hlast : i.val+1 = r
  · have hodd : Odd r := hlast ▸ hi
    have hidx : r-1-i.val = 0 := by omega
    have hsize : rfiInitial N r i = greedy (N+1) := by
      simp [rfiInitial, hidx, rfiState, hodd]
    have hle : ((rfiInitial N r i-1 : ℕ) : ℝ) ≤ N+1 := by
      have hl := greedy_le (N+1) (by linarith : 0 ≤ N+1)
      rw [hsize]
      have hg := greedy_pos (N+1)
      rw [Nat.cast_sub (by omega : 1 ≤ greedy (N+1))]
      norm_num
      linarith
    have hp : B N r b i i - 0 ≤ 0 := by
      have hbpos : 0 < ((rfiInitial N r i-1 : ℕ) : ℝ) := by exact_mod_cast hbi
      have hh : (1 : ℝ) ≤ (N+1)/((rfiInitial N r i-1 : ℕ) : ℝ) :=
        (le_div_iff₀ hbpos).mpr (by simpa using hle)
      simpa [B, b, decrement, hi] using (sub_nonpos.mpr hh)
    have hr : Response N r b (i.val+1) 0 := by
      refine ⟨0,fun _ _ => rfl,?_,by simp⟩
      intro k hk; omega
    exact odd_response_obstruction N hN r b hv i hi 0 hr hp
  · have hlt : i.val+1 < r := by omega
    let s := (rfiState N r (r-2-i.val)).2
    have hs : s < 0 := by
      apply (rfi_signs N hN r (r-2-i.val) (by omega)).2.2
      have heq : r-(r-2-i.val) = (i.val+1)+1 := by omega
      rw [heq, Nat.even_add_one]
      exact Nat.not_even_iff_odd.mpr hi
    have hsize : rfiInitial N r i = greedy ((N+1)/(1-1/s)) := by
      simpa [hi, s] using initial_step N r i hlt
    have hp := odd_decrement_pivot N (1/s) hN (one_div_neg.mpr hs)
      (by simpa only [← hsize] using hbi)
    have hbp : B N r b i i - 1/s ≤ 0 := by
      simpa only [B, ite_true, ite_eq_left hi, b, decrement, Function.update_self, hsize] using hp
    exact odd_response_obstruction N hN r b hv i hi (1/s)
      (response_decrement_tail N hN r i hlt) hbp

#print axioms odd_decrement
theorem even_decrement (N : ℝ) (hN : 0 < N) (r : ℕ) (_hr : 2 ≤ r)
    (i : Fin r) (hi : Even (i.val+1))
    (hv : Valid r (decrement (rfiInitial N r) i)) :
    ∃ x : oddBlocks r → ℝ, x ≠ 0 ∧
      qform (Cmat N r (decrement (rfiInitial N r) i)) x ≤ 0 := by
  classical
  let b := decrement (rfiInitial N r) i
  have hni : ¬ Odd (i.val+1) := Nat.not_odd_iff_even.mpr hi
  have hbi : 0 < (rfiInitial N r i-1 : ℕ) := by
    have hh : 1 ≤ rfiInitial N r i-1 := by simpa [decrement] using hv.1 i
    omega
  have hlt : i.val+1 < r := by
    by_contra hh
    have hlast : i.val+1 = r := by omega
    have hidx : r-1-i.val = 0 := by omega
    have hsize : rfiInitial N r i = 2 := by simp [rfiInitial, hidx, rfiState, ← hlast, hni]
    have hvlast := hv.2 (by omega : 0 < r)
    have heq : (⟨r-1, by omega⟩ : Fin r) = i := by apply Fin.ext; change r-1 = i.val; omega
    rw [heq] at hvlast
    simp [decrement, hsize] at hvlast
  let j : Fin r := ⟨i.val-1, by omega⟩
  have hi0 : 0 < i.val := by
    have hh := Nat.even_iff.mp hi
    omega
  have hji : j.val+1 = i.val := by dsimp [j]; omega
  have hjodd : Odd (j.val+1) := by
    rw [Nat.odd_iff]
    have hh := Nat.even_iff.mp hi
    omega
  have hjne : j ≠ i := by intro hh; have := congrArg Fin.val hh; omega
  let s := (rfiState N r (r-2-i.val)).2
  have hs : 0 < s := by
    apply (rfi_signs N hN r (r-2-i.val) (by omega)).2.1
    have hidx : r-(r-2-i.val) = (i.val+1)+1 := by omega
    rw [hidx, Nat.odd_add_one]
    exact Nat.not_odd_iff_even.mpr hi
  have hsize : rfiInitial N r i = greedy (N/s) := by
    simpa [hni, s] using initial_step N r i hlt
  have hstate : (rfiState N r (r-1-i.val)).2 = g s (-N/(rfiInitial N r i : ℝ)) := by
    simpa [hni, s] using initial_state_step N r i hlt
  have hc : rfiInitial N r j =
      greedy ((N+1)/(1-1/(g s (-N/(greedy (N/s) : ℝ))))) := by
    have hidx : r-2-j.val = r-1-i.val := by omega
    rw [initial_step N r j (by omega), ite_eq_left hjodd, hidx, hstate, hsize]
  have hr : Response N r b i.val (-(b i : ℝ)/N+1/s) := by
    have hbpos : 0 < (b i : ℝ) := by exact_mod_cast hv.1 i
    have hh := response_extend N r b i (1/s) (-(b i : ℝ)/N) 1
      (response_decrement_tail N hN r i hlt)
      (by
        rw [show B N r b i i = -N/(b i : ℝ) by simp [B, hni]]
        simp only [ite_eq_right hni, zero_mul, add_zero]
        field_simp)
      (by simp [hni])
    simpa using hh
  have hp : B N r b j j - (-(b i : ℝ)/N+1/s) ≤ 0 := by
    have hh := even_pair_pivot N s hN hs
    dsimp only at hh
    have hbcast : (b i : ℝ) = (greedy (N/s) : ℝ)-1 := by
      simp only [b, decrement, Function.update_self, hsize]
      rw [Nat.cast_sub (by have := greedy_pos (N/s); omega), Nat.cast_one]
    have hbj : b j = rfiInitial N r j := by simp [b, decrement, Function.update_of_ne hjne]
    rw [show B N r b j j = 1-(N+1)/(b j : ℝ) by simp [B, hjodd], hbj, hc, hbcast]
    convert hh using 1 <;> field_simp <;> ring
  apply odd_response_obstruction N hN r b hv j hjodd (-(b i : ℝ)/N+1/s)
  · simpa only [hji] using hr
  · exact hp

#print axioms even_decrement

end RFIMinimality
```

### `RFINonvacuity.lean`

```lean
import RFITarget
import Mathlib.Tactic.FinCases

set_option linter.unusedSimpArgs false
noncomputable section
namespace RFIMinimality
open Matrix

abbrev tinyB (i : Fin 2) : ℕ := 1+i.val
def tinyCenter : (Σ i : Fin 2, Fin (tinyB i)) := ⟨0,⟨0,by norm_num [tinyB]⟩⟩
def tinyLeaf0 : (Σ i : Fin 2, Fin (tinyB i)) := ⟨1,⟨0,by norm_num [tinyB]⟩⟩
def tinyLeaf1 : (Σ i : Fin 2, Fin (tinyB i)) := ⟨1,⟨1,by norm_num [tinyB]⟩⟩

lemma tiny_sum (w : (Σ i : Fin 2, Fin (tinyB i)) → ℝ) :
    ∑ x, w x = w tinyCenter + w tinyLeaf0 + w tinyLeaf1 := by
  rw [Fintype.sum_sigma]
  simp [tinyB, Fin.sum_univ_succ, tinyCenter, tinyLeaf0, tinyLeaf1]
  ring

lemma tiny_rows (v : (Σ i : Fin 2, Fin (tinyB i)) → ℝ) :
    ((TG 2 tinyB).adjMatrix ℝ *ᵥ v) tinyCenter = v tinyLeaf0 + v tinyLeaf1 ∧
    ((TG 2 tinyB).adjMatrix ℝ *ᵥ v) tinyLeaf0 = v tinyCenter ∧
    ((TG 2 tinyB).adjMatrix ℝ *ᵥ v) tinyLeaf1 = v tinyCenter := by
  simp only [mulVec, dotProduct, tiny_sum]
  norm_num [TG, SimpleGraph.adjMatrix, tinyCenter, tinyLeaf0, tinyLeaf1, tinyB, min_def]

lemma tiny_valid : Valid 2 tinyB := by
  constructor
  · intro i; fin_cases i <;> norm_num [tinyB]
  · intro _; norm_num [tinyB]

/-- The freeness premise has a concrete literal-graph witness. -/
theorem tiny_free : IntervalFree 1 2 tinyB := by
  intro μ hμ hμN ⟨v,hv,he⟩
  obtain ⟨hc,h0,h1⟩ := tiny_rows v
  rw [he] at hc h0 h1
  simp only [Pi.smul_apply, smul_eq_mul] at hc h0 h1
  have hleaf : v tinyLeaf0 = v tinyLeaf1 := by nlinarith
  have hc0 : v tinyCenter = 0 := by
    have hrel : μ^2 * v tinyCenter = 2*v tinyCenter := by nlinarith
    have hlt : μ^2 < 2 := by nlinarith
    nlinarith
  have hl0 : v tinyLeaf0 = 0 := by nlinarith
  have hl1 : v tinyLeaf1 = 0 := by nlinarith
  apply hv
  funext x
  change v x = 0
  rcases x with ⟨i,k⟩
  fin_cases i
  · have hk : k = ⟨0,by norm_num [tinyB]⟩ := by apply Fin.ext; have := k.isLt; simp [tinyB] at *
    subst k
    exact hc0
  · fin_cases k
    · exact hl0
    · exact hl1

lemma tiny_initial : rfiInitial 1 2 = tinyB := by
  ext i
  fin_cases i <;> norm_num [rfiInitial, rfiState, greedy, tinyB, show ¬ Odd (2 : ℕ) from by decide]

theorem endpoint_nonvacuity : ∃ b : Fin 2 → ℕ,
    Valid 2 b ∧ (∀ i, b i ≤ rfiInitial 1 2 i) ∧ IntervalFree 1 2 b := by
  refine ⟨tinyB,tiny_valid,?_,tiny_free⟩
  rw [tiny_initial]
  exact fun _ => le_rfl

#print axioms tiny_free
#print axioms endpoint_nonvacuity
end RFIMinimality
```

### `RFIFinal.lean`

```lean
import RFIPositive
import RFIDecrement
import RFITarget

noncomputable section
namespace RFIMinimality
open Matrix

/-- Conjecture 10.1 (journal Conjecture 29), with the closed upper endpoint. -/
theorem conj_10_1 (N : ℝ) (hN : 0 < N) (r : ℕ) (hr : 2 ≤ r) (b : Fin r → ℕ)
    (hb : Valid r b) (hle : ∀ i, b i ≤ rfiInitial N r i)
    (hfree : ∀ μ : ℝ, 0 < μ → μ ≤ N →
       ¬ ∃ v : (Σ i : Fin r, Fin (b i)) → ℝ, v ≠ 0 ∧ (TG r b).adjMatrix ℝ *ᵥ v = μ • v) :
    b = rfiInitial N r := by
  apply minimality_of_positive_and_decrements N hN r hr (B_positive_subspace r) ?_ b hb hle hfree
  intro i hv
  by_cases hi : Odd (i.val+1)
  · exact odd_decrement N hN r hr i hi hv
  · exact even_decrement N hN r hr i (Nat.not_odd_iff_even.mp hi) hv

/-- Definitional check against the unchanged stage-1 literal proposition. -/
theorem conjecture352345_proved : Conjecture352345 := conj_10_1

#print conj_10_1
#print axioms conj_10_1
#print axioms conjecture352345_proved
end RFIMinimality
```

