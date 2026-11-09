import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic

namespace PermutationSpectrum

open Matrix

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

def IsPermutationLike (A : Matrix ι ι K) : Prop :=
  ∀ j, ∃ i, A i j = 1 ∧ ∀ k, k ≠ i → A k j = 0

def IsPermutationMatrix (A : Matrix ι ι K) : Prop :=
  IsPermutationLike A ∧ IsPermutationLike A.transpose

def IsEigenvalue (A : Matrix ι ι K) (μ : K) : Prop :=
  ∃ v : ι → K, v ≠ 0 ∧ A *ᵥ v = μ • v

def transition (f : ι → ι) : Matrix ι ι K := fun i j => if i = f j then 1 else 0

omit [Fintype ι] in
theorem representation {A : Matrix ι ι K} (h : IsPermutationLike A) :
    ∃ f : ι → ι, A = transition f := by
  classical
  choose f hf using h
  refine ⟨f, ?_⟩
  ext i j
  by_cases hij : i = f j
  · simp [transition, hij, (hf j).1]
  · simp [transition, hij, (hf j).2 i hij]

omit [Fintype ι] in
theorem transition_is_permutation_like (f : ι → ι) :
    IsPermutationLike (transition f : Matrix ι ι K) := by
  intro j
  refine ⟨f j, by simp [transition], ?_⟩
  intro k hk
  simp [transition, hk]

theorem transition_mul (f g : ι → ι) :
    (transition f : Matrix ι ι K) * transition g = transition (f ∘ g) := by
  ext i j
  simp only [Matrix.mul_apply, transition]
  rw [Finset.sum_eq_single (g j)]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

omit [Fintype ι] in
theorem transition_id : (transition id : Matrix ι ι K) = 1 := by
  ext i j
  simp [transition, Matrix.one_apply]

theorem transition_pow (f : ι → ι) (n : ℕ) :
    (transition f : Matrix ι ι K) ^ n = transition (f^[n]) := by
  induction n with
  | zero => simpa using (transition_id (K := K) (ι := ι)).symm
  | succ n ih =>
    rw [pow_succ', ih, transition_mul]
    rw [Function.iterate_succ']

theorem powers_repeat (f : ι → ι) :
    ∃ p q : ℕ, p < q ∧ (transition f : Matrix ι ι K) ^ p = transition f ^ q := by
  obtain ⟨p, q, hpq, he⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => f^[n])
  rcases lt_or_gt_of_ne hpq with h | h
  · exact ⟨p, q, h, by rw [transition_pow, transition_pow, he]⟩
  · exact ⟨q, p, h, by rw [transition_pow, transition_pow, he]⟩

theorem eigenvector_power {A : Matrix ι ι K} {μ : K} {v : ι → K}
    (hv : A *ᵥ v = μ • v) (n : ℕ) : A ^ n *ᵥ v = μ ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hv, smul_smul, pow_succ', mul_comm]

theorem eigenvalue_zero_or_root_of_unity {A : Matrix ι ι K}
    (hA : IsPermutationLike A) {μ : K} (hμ : IsEigenvalue A μ) :
    μ = 0 ∨ ∃ k : ℕ, 0 < k ∧ μ ^ k = 1 := by
  by_cases hz : μ = 0
  · exact Or.inl hz
  right
  obtain ⟨f, rfl⟩ := representation hA
  obtain ⟨p, q, hpq, he⟩ := powers_repeat (K := K) f
  obtain ⟨v, hv, hev⟩ := hμ
  have hcoord : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  obtain ⟨i, hi⟩ := hcoord
  have hs : μ ^ p • v = μ ^ q • v := by
    rw [← eigenvector_power hev p, ← eigenvector_power hev q, he]
  have hpow : μ ^ p = μ ^ q := by
    have heq := congrFun hs i
    exact mul_right_cancel₀ hi heq
  refine ⟨q - p, Nat.sub_pos_of_lt hpq, ?_⟩
  have heq : μ ^ p * 1 = μ ^ p * μ ^ (q - p) := by
    rw [mul_one, ← pow_add, Nat.add_sub_of_le (le_of_lt hpq)]
    exact hpow
  exact (mul_left_cancel₀ (pow_ne_zero p hz) heq).symm

theorem isEigenvalue_iff_library {A : Matrix ι ι K} {μ : K} :
    IsEigenvalue A μ ↔ Module.End.HasEigenvalue A.toLin' μ := by
  constructor
  · rintro ⟨v, hv, he⟩
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := v)
    exact ⟨Module.End.mem_eigenspace_iff.mpr he, hv⟩
  · intro h
    obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    exact ⟨v, hv.2, hv.apply_eq_smul⟩

theorem transition_mulVec_single (f : ι → ι) (j : ι) :
    (transition f : Matrix ι ι K) *ᵥ Pi.single j 1 = Pi.single (f j) 1 := by
  ext i
  simp [Matrix.mulVec, dotProduct, transition, Pi.single_apply, eq_comm]

theorem zero_eigenvalue_iff_not_injective (f : ι → ι) :
    IsEigenvalue (transition f : Matrix ι ι K) 0 ↔ ¬ Function.Injective f := by
  classical
  constructor
  · rintro ⟨v, hv, hev⟩ hf
    have hb : Function.Bijective f := (Finite.injective_iff_bijective).mp hf
    let e := Equiv.ofBijective f hb
    have hinv : (transition (e.symm : ι → ι) : Matrix ι ι K) * transition f = 1 := by
      rw [transition_mul]
      have he : (e.symm : ι → ι) ∘ f = id := by
        funext i
        exact e.symm_apply_apply i
      rw [he, transition_id]
    have hzero := congrArg (fun w => transition (e.symm : ι → ι) *ᵥ w) hev
    rw [Matrix.mulVec_mulVec, hinv] at hzero
    simp only [Matrix.one_mulVec, zero_smul, Matrix.mulVec_zero] at hzero
    exact hv hzero
  · intro hf
    obtain ⟨i, j, he, hij⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
      unfold Function.Injective at hf
      push Not at hf
      exact hf
    refine ⟨Pi.single i 1 - Pi.single j 1, ?_, ?_⟩
    · intro hz
      have hc := congrFun hz i
      simp [hij] at hc
    · rw [Matrix.mulVec_sub, transition_mulVec_single, transition_mulVec_single, he]
      simp

theorem transition_permutation_iff_injective (f : ι → ι) :
    IsPermutationMatrix (transition f : Matrix ι ι K) ↔ Function.Injective f := by
  constructor
  · intro h i j hij
    obtain ⟨k, hk, hother⟩ := h.2 (f i)
    have hi : i = k := by
      by_contra hn
      have := hother i hn
      simp [Matrix.transpose_apply, transition] at this
    have hj : j = k := by
      by_contra hn
      have := hother j hn
      simp [Matrix.transpose_apply, transition, hij] at this
    exact hi.trans hj.symm
  · intro hf
    refine ⟨transition_is_permutation_like f, ?_⟩
    have hs : Function.Surjective f := Finite.surjective_of_injective hf
    intro i
    obtain ⟨j, hj⟩ := hs i
    refine ⟨j, ?_, ?_⟩
    · simp [Matrix.transpose_apply, transition, hj]
    · intro k hk
      have hn : i ≠ f k := by
        intro he
        exact hk (hf (he.symm.trans hj.symm))
      simp [Matrix.transpose_apply, transition, hn]

theorem zero_eigenvalue_iff_not_permutation {A : Matrix ι ι K}
    (hA : IsPermutationLike A) : IsEigenvalue A 0 ↔ ¬ IsPermutationMatrix A := by
  obtain ⟨f, rfl⟩ := representation hA
  rw [zero_eigenvalue_iff_not_injective, transition_permutation_iff_injective]

theorem identity_is_permutation : IsPermutationMatrix (1 : Matrix ι ι K) := by
  have h := (transition_permutation_iff_injective (K := K) (id : ι → ι)).mpr
    Function.injective_id
  rwa [transition_id] at h

theorem main_conjecture {A : Matrix ι ι K} (hA : IsPermutationLike A) :
    (∀ μ, Module.End.HasEigenvalue A.toLin' μ →
      μ = 0 ∨ ∃ k : ℕ, 0 < k ∧ μ ^ k = 1) ∧
    (Module.End.HasEigenvalue A.toLin' 0 ↔ ¬ IsPermutationMatrix A) := by
  constructor
  · intro μ hμ
    exact eigenvalue_zero_or_root_of_unity hA (isEigenvalue_iff_library.mpr hμ)
  · rw [← isEigenvalue_iff_library]
    exact zero_eigenvalue_iff_not_permutation hA

theorem exact_mathdb_conclusion {A : Matrix ι ι K} (hA : IsPermutationLike A) :
    (∀ μ, Module.End.HasEigenvalue A.toLin' μ →
      μ = 0 ∨ ∃ k : ℕ, 0 < k ∧ μ ^ k = 1) ∧
    (Module.End.HasEigenvalue A.toLin' 0 ↔ ¬ IsPermutationMatrix A ∧ A ≠ 1) := by
  refine ⟨(main_conjecture hA).1, ?_⟩
  rw [(main_conjecture hA).2]
  constructor
  · intro h
    refine ⟨h, ?_⟩
    intro he
    exact h (he ▸ identity_is_permutation)
  · exact And.left

end PermutationSpectrum
