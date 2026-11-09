import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.Finite.GaloisField

set_option autoImplicit false

namespace BSym334207

open Finset

variable (F : Type*) [Field F]

/-- Coordinate `k` of the `j`-th vector of the recursive window sequence of dimension `b`
and length `n` (entries are `0` or `1`). -/
def sv : ℕ → ℕ → ℕ → ℕ → F
  | 0, _, _, _ => 0
  | b + 1, n, j, k =>
    if n % (b + 1) = 0 then (if j % (b + 1) = k then 1 else 0)
    else if j < n / (b + 1) * (b + 1) then (if j % (b + 1) = k then 1 else 0)
    else sv (n % (b + 1)) ((b + 1) + n % (b + 1)) (n % (b + 1) + k) (j - n / (b + 1) * (b + 1))
termination_by b _ _ _ => b
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos b)

variable {F}

theorem sv_dvd {b n j k : ℕ} (hb : b ≠ 0) (h : n % b = 0) :
    sv F b n j k = if j % b = k then 1 else 0 := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
  rw [sv]; simp [h]

theorem sv_block {b n j k : ℕ} (hb : b ≠ 0) (h : n % b ≠ 0) (hj : j < n / b * b) :
    sv F b n j k = if j % b = k then 1 else 0 := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
  rw [sv]; simp [h, hj]

theorem sv_bridge {b n j k : ℕ} (hb : b ≠ 0) (h : n % b ≠ 0) (hj : n / b * b ≤ j) :
    sv F b n j k = sv F (n % b) (b + n % b) (n % b + k) (j - n / b * b) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
  rw [sv]; simp [h, Nat.not_lt.mpr hj]


/-- The `j`-th vector of the recursive window sequence. -/
def V (b n j : ℕ) : Fin b → F := fun k => sv F b n j k

/-- Every `b` cyclically consecutive vectors (indices mod `n`) are linearly independent. -/
def Good (b n : ℕ) (v : ℕ → Fin b → F) : Prop :=
  ∀ s, s < n → LinearIndependent F (fun t : Fin b => v ((s + t) % n))

theorem ite_pos' {α : Sort*} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

theorem ite_neg' {α : Sort*} {c : Prop} [Decidable c] (h : ¬c) (a b : α) :
    (if c then a else b) = b := by simp [h]

theorem mod_window {M b q : ℕ} (hM : 1 ≤ M) (h1 : M * b - b ≤ q) (h2 : q < M * b) :
    q % b = q + b - M * b := by
  have hMb : M * b = (M - 1) * b + b := by
    rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left b hM)]
  have hq : q = (q + b - M * b) + (M - 1) * b := by omega
  rw [hq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  omega

theorem li_single {b : ℕ} (f : Fin b → Fin b) (hf : Function.Injective f) :
    LinearIndependent F (fun t : Fin b => (Pi.single (f t) (1 : F) : Fin b → F)) := by
  have := (Pi.basisFun F (Fin b)).linearIndependent.comp f hf
  simpa [Function.comp_def, Pi.basisFun_apply] using this

theorem single_eq_ite {b : ℕ} (i : Fin b) (k : Fin b) :
    (Pi.single i (1 : F) : Fin b → F) k = if (i : ℕ) = k then 1 else 0 := by
  by_cases h : k = i
  · subst h; simp
  · have h' : (i : ℕ) ≠ k := fun e => h (Fin.ext e.symm)
    simp [h, h']

theorem mod_inj_window {b s t₁ t₂ : ℕ} (h₁ : t₁ < b) (h₂ : t₂ < b)
    (h : (s + t₁) % b = (s + t₂) % b) : t₁ = t₂ := by
  have := Nat.ModEq.add_left_cancel' s h
  unfold Nat.ModEq at this
  rwa [Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at this

/-- Windows consisting only of block vectors `e_{j mod b}` are independent. -/
theorem li_block {b : ℕ} (hb : b ≠ 0) (w : Fin b → Fin b → F) (s : ℕ)
    (hw : ∀ t : Fin b, ∀ k : Fin b, w t k = if (s + t) % b = k then 1 else 0) :
    LinearIndependent F w := by
  have hbpos : 0 < b := Nat.pos_of_ne_zero hb
  let f : Fin b → Fin b := fun t => ⟨(s + t) % b, Nat.mod_lt _ hbpos⟩
  have hf : Function.Injective f := by
    intro t₁ t₂ h
    exact Fin.ext (mod_inj_window t₁.2 t₂.2 (congrArg Fin.val h))
  have hw' : w = fun t => (Pi.single (f t) (1 : F) : Fin b → F) := by
    funext t k; rw [hw, single_eq_ite]
  rw [hw']; exact li_single f hf


/-- Coordinate of a non-bridge vector in a bridge-touching window. -/
def kap (b n N s t : ℕ) : ℕ := if s + t < N then s + t + b - N else s + t - n

/-- Coordinates hit by non-bridge vectors of a bridge-touching window. -/
def hit (b n N s k : ℕ) : Prop := (s < N ∧ s + b - N ≤ k) ∨ k < s + b - n

theorem mod_two {x n : ℕ} (h : x < 2 * n) :
    x % n = if x < n then x else x - n := by
  split_ifs with hx
  · exact Nat.mod_eq_of_lt hx
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem bridge_window {b n : ℕ} (hb : b ≠ 0) (hnb : n % b ≠ 0) (hbn : b ≤ n)
    (IHe : ∀ j k : ℕ, j < n % b → k < n % b →
      sv F (n % b) (b + n % b) j k = if j = k then 1 else 0)
    (IHg : Good (n % b) (b + n % b) (V (F := F) (n % b) (b + n % b)))
    (s : ℕ) (hs : s < n) (hsb : n / b * b < s + b) :
    LinearIndependent F (fun t : Fin b => V (F := F) b n ((s + t) % n)) := by
  have hbpos : 0 < b := Nat.pos_of_ne_zero hb
  have hdm := Nat.div_add_mod' n b
  have hr0 : 0 < n % b := Nat.pos_of_ne_zero hnb
  have hrb : n % b < b := Nat.mod_lt _ hbpos
  have hM : 1 ≤ n / b := (Nat.one_le_div_iff hbpos).mpr hbn
  have hNb : b ≤ n / b * b := Nat.le_mul_of_pos_left b hM
  generalize hr : n % b = r at *
  generalize hN : n / b * b = N at *
  have hn : n = N + r := by omega
  -- positions
  have hq : ∀ t : Fin b, (s + t) % n = if s + (t : ℕ) < n then s + t else s + t - n := by
    intro t; exact mod_two (by omega)
  -- bridge vectors
  have hBr : ∀ t : Fin b, N ≤ s + t → s + (t : ℕ) < n → ∀ k : Fin b,
      V (F := F) b n ((s + t) % n) k = V (F := F) r (b + r) (r + k) ⟨(s + t - N) % r, Nat.mod_lt _ hr0⟩ := by
    intro t h1 h2 k
    rw [hq, ite_pos' h2]
    simp only [V]
    rw [sv_bridge hb (by rw [hr]; exact hnb) (by rw [hN]; exact h1), hr, hN,
      Nat.mod_eq_of_lt (a := s + t - N) (by omega)]
  -- non-bridge vectors
  have hNon : ∀ t : Fin b, ¬(N ≤ s + t ∧ s + (t : ℕ) < n) → ∀ k : Fin b,
      V (F := F) b n ((s + t) % n) k = if kap b n N s t = k then 1 else 0 := by
    intro t h k
    simp only [V]
    rw [hq]
    by_cases h1 : s + (t : ℕ) < N
    · have hk : kap b n N s t = s + t + b - N := by simp [kap, h1]
      rw [hk, ite_pos' (show s + (t : ℕ) < n by omega) _ _,
        sv_block hb (by rw [hr]; exact hnb) (by rw [hN]; exact h1),
        mod_window (M := n / b) hM (by rw [hN]; omega) (by rw [hN]; exact h1), hN]
    · have h2 : n ≤ s + t := by omega
      have hk : kap b n N s t = s + t - n := by simp [kap, h1]
      rw [hk, ite_neg' (show ¬ (s + (t : ℕ) < n) by omega) _ _,
        sv_block hb (by rw [hr]; exact hnb) (by rw [hN]; omega), Nat.mod_eq_of_lt (by omega)]
  have hkap : ∀ t : Fin b, ¬(N ≤ s + t ∧ s + (t : ℕ) < n) →
      hit b n N s (kap b n N s t) ∧ kap b n N s t < b := by
    intro t h; simp only [hit, kap]; split_ifs <;> omega
  have hkap_inj : ∀ t₁ t₂ : Fin b, ¬(N ≤ s + t₁ ∧ s + (t₁ : ℕ) < n) →
      ¬(N ≤ s + t₂ ∧ s + (t₂ : ℕ) < n) → kap b n N s t₁ = kap b n N s t₂ → t₁ = t₂ := by
    intro t₁ t₂ h₁ h₂ h; apply Fin.ext; simp only [kap] at h; split_ifs at h <;> omega
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hcoord : ∀ k : Fin b, ∑ t, g t * V (F := F) b n ((s + t) % n) k = 0 := by
    intro k
    have := congrFun hg k
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
  -- the functional
  let cf : Fin b → F := fun t => if N ≤ s + (t : ℕ) ∧ s + (t : ℕ) < n then g t else 0
  let ℓ : (Fin r → F) →ₗ[F] F := ∑ t : Fin b, cf t •
    LinearMap.proj (R := F) (φ := fun _ : Fin r => F) (⟨(s + t - N) % r, Nat.mod_lt _ hr0⟩ : Fin r)
  have hℓ : ∀ x : Fin r → F, ℓ x = ∑ t : Fin b, cf t * x ⟨(s + t - N) % r, Nat.mod_lt _ hr0⟩ := by
    intro x; simp [ℓ, LinearMap.sum_apply]
  -- step 1
  have step1 : ∀ k : Fin b, ¬ hit b n N s k → ℓ (V (F := F) r (b + r) (r + k)) = 0 := by
    intro k hk
    rw [hℓ, ← hcoord k]
    apply Finset.sum_congr rfl
    intro t _
    by_cases h : N ≤ s + (t : ℕ) ∧ s + (t : ℕ) < n
    · simp only [cf, ite_pos' h]; rw [hBr t h.1 h.2 k]
    · simp only [cf, ite_neg' h, zero_mul]
      have hne : ¬ kap b n N s t = (k : ℕ) := fun heq => hk (heq ▸ (hkap t h).1)
      rw [hNon t h k, ite_neg' hne _ _, mul_zero]
  -- standard vectors of T
  have hTe : ∀ x (hx : x < r), V (F := F) r (b + r) x = Pi.single (⟨x, hx⟩ : Fin r) (1 : F) := by
    intro x hx; funext c; simp only [V]; rw [IHe x c hx c.2, single_eq_ite]
  -- the window of T
  obtain ⟨σ, hσ'⟩ : ∃ σ : ℕ, (s < N ∧ s + b ≤ n ∧ σ = s + b - N) ∨
      (¬(s < N ∧ s + b ≤ n) ∧ σ = r + (s + b - n)) := by
    by_cases hc : s < N ∧ s + b ≤ n
    · exact ⟨_, Or.inl ⟨hc.1, hc.2, rfl⟩⟩
    · exact ⟨_, Or.inr ⟨hc, rfl⟩⟩
  have hσ : σ < b + r := by omega
  have hwin : ∀ i : Fin r, ℓ (V (F := F) r (b + r) ((σ + i) % (b + r))) = 0 := by
    intro i
    have hx := mod_two (x := σ + i) (n := b + r) (by omega)
    generalize hxdef : (σ + i) % (b + r) = x at hx ⊢
    by_cases hlt : x < r
    · rw [hTe _ hlt, hℓ]
      apply Finset.sum_eq_zero
      intro t _
      by_cases h : N ≤ s + (t : ℕ) ∧ s + (t : ℕ) < n
      · simp only [cf, ite_pos' h]
        have hne : ¬ ((⟨x, hlt⟩ : Fin r) : ℕ) = ((⟨(s + t - N) % r, Nat.mod_lt _ hr0⟩ : Fin r) : ℕ) := by
          intro heq
          simp only at heq
          rw [Nat.mod_eq_of_lt (a := s + t - N) (by omega)] at heq
          split_ifs at hx <;> omega
        rw [single_eq_ite, ite_neg' hne _ _, mul_zero]
      · simp only [cf, ite_neg' h, zero_mul]
    · have hk : x - r < b := by split_ifs at hx <;> omega
      have := step1 ⟨x - r, hk⟩ (by simp only [hit]; split_ifs at hx <;> omega)
      simpa [Nat.add_sub_cancel' (show r ≤ x by omega)] using this
  have : Nonempty (Fin r) := ⟨⟨0, hr0⟩⟩
  have hspan := (IHg σ hσ).span_eq_top_of_card_eq_finrank (by simp)
  have hℓ0 : ℓ = 0 := LinearMap.ext_on_range hspan (fun i => by simpa using hwin i)
  -- step 5
  have hbr0 : ∀ t : Fin b, (N ≤ s + t ∧ s + (t : ℕ) < n) → g t = 0 := by
    intro t ht
    have h0 := congrArg (fun L : (Fin r → F) →ₗ[F] F =>
      L (Pi.single (⟨(s + t - N) % r, Nat.mod_lt _ hr0⟩ : Fin r) (1 : F))) hℓ0
    simp only [LinearMap.zero_apply] at h0
    rw [hℓ, Finset.sum_eq_single t] at h0
    · simpa [cf, ht] using h0
    · intro t' _ ht'
      by_cases h' : N ≤ s + (t' : ℕ) ∧ s + (t' : ℕ) < n
      · simp only [cf, ite_pos' h']
        have hne : ¬ ((⟨(s + t - N) % r, Nat.mod_lt _ hr0⟩ : Fin r) : ℕ) =
            ((⟨(s + t' - N) % r, Nat.mod_lt _ hr0⟩ : Fin r) : ℕ) := by
          intro heq
          simp only at heq
          rw [Nat.mod_eq_of_lt (a := s + t - N) (by omega),
            Nat.mod_eq_of_lt (a := s + t' - N) (by omega)] at heq
          exact ht' (Fin.ext (by omega))
        rw [single_eq_ite, ite_neg' hne _ _, mul_zero]
      · simp only [cf, ite_neg' h', zero_mul]
    · simp
  intro t
  by_cases ht : N ≤ s + (t : ℕ) ∧ s + (t : ℕ) < n
  · exact hbr0 t ht
  · have hk := hcoord ⟨kap b n N s t, (hkap t ht).2⟩
    rw [Finset.sum_eq_single t] at hk
    · rw [hNon t ht] at hk; simpa using hk
    · intro t' _ ht'
      by_cases h' : N ≤ s + (t' : ℕ) ∧ s + (t' : ℕ) < n
      · rw [hbr0 t' h', zero_mul]
      · have hne : ¬ kap b n N s t' = ((⟨kap b n N s t, (hkap t ht).2⟩ : Fin b) : ℕ) :=
          fun heq => ht' (hkap_inj t' t h' ht heq)
        rw [hNon t' h', ite_neg' hne _ _, mul_zero]
    · simp

/-- Theorem A: the recursive sequence starts with the standard basis and is `b`-good. -/
theorem windows_good (b : ℕ) : ∀ n, 1 ≤ b → b ≤ n →
    (∀ j k : ℕ, j < b → k < b → sv F b n j k = if j = k then 1 else 0) ∧
    Good b n (V (F := F) b n) := by
  induction b using Nat.strong_induction_on with
  | _ b IH =>
  intro n hb1 hbn
  have hb : b ≠ 0 := by omega
  have hbpos : 0 < b := by omega
  by_cases hdiv : n % b = 0
  · refine ⟨?_, ?_⟩
    · intro j k hj _; rw [sv_dvd hb hdiv, Nat.mod_eq_of_lt hj]
    · intro s _
      apply li_block hb _ s
      intro t k
      simp only [V]
      rw [sv_dvd hb hdiv, Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero hdiv)]
  · have hM : 1 ≤ n / b := (Nat.one_le_div_iff hbpos).mpr hbn
    have hNb : b ≤ n / b * b := Nat.le_mul_of_pos_left b hM
    have hNle : n / b * b ≤ n := Nat.div_mul_le_self n b
    have hr : n % b < b := Nat.mod_lt _ hbpos
    obtain ⟨IHe, IHg⟩ := IH (n % b) hr (b + n % b) (Nat.pos_of_ne_zero hdiv) (by omega)
    refine ⟨?_, ?_⟩
    · intro j k hj _
      rw [sv_block hb hdiv (by omega), Nat.mod_eq_of_lt hj]
    · intro s hs
      by_cases hsb : n / b * b < s + b
      · exact bridge_window hb hdiv hbn IHe IHg s hs hsb
      · apply li_block hb _ s
        intro t k
        simp only [V]
        have hlt : s + (t : ℕ) < n := by omega
        rw [Nat.mod_eq_of_lt hlt, sv_block hb hdiv (by omega)]


/-! ## Source definitions (Ding–Zhang–Ge, arXiv:1609.09236, Section 2) -/

section Defs
open Classical

variable {n : ℕ}

/-- The `i`-th cyclic index `i + j mod n`. -/
def cyc (i : Fin n) (j : ℕ) : Fin n := ⟨((i : ℕ) + j) % n, Nat.mod_lt _ ((Nat.zero_le _).trans_lt i.2)⟩

/-- `wt_b(x) = |{0 ≤ i ≤ n-1 : (x_i, …, x_{i+b-1}) ≠ 0}|`, indices mod `n`. -/
noncomputable def bWeight (b : ℕ) (x : Fin n → F) : ℕ :=
  (univ.filter fun i : Fin n => ∃ j, j < b ∧ x (cyc i j) ≠ 0).card

/-- `D_b(x, y) = |{0 ≤ i ≤ n-1 : (x_i, …, x_{i+b-1}) ≠ (y_i, …, y_{i+b-1})}|`. -/
noncomputable def bDist (b : ℕ) (x y : Fin n → F) : ℕ :=
  (univ.filter fun i : Fin n => ∃ j, j < b ∧ x (cyc i j) ≠ y (cyc i j)).card

/-- `C` has minimum `b`-distance `d`: the minimum of `D_b` over pairs of distinct codewords is `d`. -/
def HasMinBDist (b : ℕ) (C : Set (Fin n → F)) (d : ℕ) : Prop :=
  (∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ bDist b x y = d) ∧ ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ bDist b x y

/-- A linear MDS `(n, d)_q` `b`-symbol code over `F = F_q`: a subspace `C ⊆ F^n` which is an
`(n, |C|, d)_q` `b`-symbol code with `|C| = q^(n - d + b)` (the Singleton-type bound with equality). -/
def IsLinearMDSBSymbol (b d : ℕ) (C : Submodule F (Fin n → F)) : Prop :=
  HasMinBDist b (C : Set (Fin n → F)) d ∧ Nat.card C = Nat.card F ^ (n - d + b)

end Defs

theorem bDist_eq_bWeight {n : ℕ} (b : ℕ) (x y : Fin n → F) : bDist b x y = bWeight b (x - y) := by
  classical
  simp only [bDist, bWeight, Pi.sub_apply, ne_eq, sub_eq_zero]

/-- The parity-check map `x ↦ ∑ j, x j • v_j`. -/
noncomputable def parity (b n : ℕ) : (Fin n → F) →ₗ[F] (Fin b → F) :=
  Fintype.linearCombination F (fun j : Fin n => V (F := F) b n j)

theorem parity_apply (b n : ℕ) (x : Fin n → F) :
    parity (F := F) b n x = ∑ j : Fin n, x j • V (F := F) b n j := by
  simp [parity, Fintype.linearCombination_apply]

theorem parity_single (b n : ℕ) (j : Fin n) :
    parity (F := F) b n (Pi.single j 1) = V (F := F) b n j := by
  rw [parity_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hij; simp [hij]
  · simp

theorem parity_surj {b n : ℕ} (hb : 1 ≤ b) (hbn : b ≤ n) :
    LinearMap.range (parity (F := F) b n) = ⊤ := by
  have hA := (windows_good (F := F) b n hb hbn).1
  have he : ∀ k : Fin b, (Pi.single k (1 : F) : Fin b → F) ∈ LinearMap.range (parity (F := F) b n) := by
    intro k
    refine ⟨Pi.single (⟨k, by omega⟩ : Fin n) 1, ?_⟩
    rw [parity_single]
    funext c
    simp only [V]
    rw [hA k c k.2 c.2, single_eq_ite]
  rw [eq_top_iff, ← (Pi.basisFun F (Fin b)).span_eq, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  simpa [Pi.basisFun_apply] using he k

theorem card_ker {b n : ℕ} (hb : 1 ≤ b) (hbn : b ≤ n) :
    Nat.card (LinearMap.ker (parity (F := F) b n)) = Nat.card F ^ (n - b) := by
  have hrk := LinearMap.finrank_range_add_finrank_ker (parity (F := F) b n)
  rw [parity_surj hb hbn, finrank_top] at hrk
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hrk
  rw [Module.natCard_eq_pow_finrank (K := F)]
  congr 1
  omega

theorem mod_inj_range {n x y : ℕ} (h1 : x < y + n) (h2 : y < x + n) (h : x % n = y % n) :
    x = y := by
  rcases le_total x y with hxy | hxy
  · have hm : (y - x) % n = 0 := Nat.sub_mod_eq_zero_of_mod_eq h.symm
    have : y - x = 0 := Nat.eq_zero_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero hm) (by omega)
    omega
  · have hm : (x - y) % n = 0 := Nat.sub_mod_eq_zero_of_mod_eq h
    have : x - y = 0 := Nat.eq_zero_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero hm) (by omega)
    omega

/-- Every nonzero codeword of `ker (parity b n)` has `b`-weight at least `2b`. -/
theorem weight_ge {b n : ℕ} (hb : 1 ≤ b) (hn : 2 * b ≤ n) (c : Fin n → F)
    (hc : parity (F := F) b n c = 0) (hc0 : c ≠ 0) : 2 * b ≤ bWeight b c := by
  classical
  by_contra hlt
  push Not at hlt
  have hnpos : 0 < n := by omega
  obtain ⟨Z, hZc, hmemZ⟩ : ∃ Z : Finset (Fin n), Z.card = bWeight b c ∧
      ∀ i : Fin n, i ∈ Z ↔ ∃ j, j < b ∧ c (cyc i j) ≠ 0 :=
    ⟨_, rfl, fun i => by simp⟩
  rw [← hZc] at hlt
  have hZc := hlt
  obtain ⟨i0, hi0⟩ : ∃ i0 : Fin n, i0 ∉ Z := by
    by_contra hall
    push Not at hall
    have hu : Z = univ := Finset.eq_univ_of_forall hall
    have := congrArg Finset.card hu
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  have hzero : ∀ j, j < b → c (cyc i0 j) = 0 := by
    intro j hj; by_contra h; exact hi0 ((hmemZ i0).2 ⟨j, hj, h⟩)
  let pos : ℕ → Fin n := fun m => ⟨((i0 : ℕ) + b + m) % n, Nat.mod_lt _ hnpos⟩
  have hpos_zero : ∀ m, n - b ≤ m → m < n → c (pos m) = 0 := by
    intro m h1 h2
    have h := hzero (m - (n - b)) (by omega)
    have he : pos m = cyc i0 (m - (n - b)) := by
      apply Fin.ext
      simp only [pos, cyc]
      rw [show (i0 : ℕ) + b + m = ((i0 : ℕ) + (m - (n - b))) + n by omega, Nat.add_mod_right]
    rw [he]; exact h
  have hpos_surj : ∀ p : Fin n, ∃ m, m < n ∧ pos m = p := by
    intro p
    refine ⟨((p : ℕ) + n + n - ((i0 : ℕ) + b)) % n, Nat.mod_lt _ hnpos, ?_⟩
    apply Fin.ext
    simp only [pos]
    rw [Nat.add_mod_mod, show (i0 : ℕ) + b + ((p : ℕ) + n + n - ((i0 : ℕ) + b)) = (p : ℕ) + n + n by
      have := i0.2; omega, Nat.add_mod_right, Nat.add_mod_right, Nat.mod_eq_of_lt p.2]
  obtain ⟨p0, hp0⟩ : ∃ p : Fin n, c p ≠ 0 := by
    by_contra h; push Not at h; exact hc0 (funext h)
  have hex : ∃ m, m < n ∧ c (pos m) ≠ 0 := by
    obtain ⟨m, hm, hmp⟩ := hpos_surj p0; exact ⟨m, hm, hmp ▸ hp0⟩
  have hm0 : Nat.find hex < n ∧ c (pos (Nat.find hex)) ≠ 0 := Nat.find_spec hex
  have hm0min : ∀ m, m < Nat.find hex → ¬ (m < n ∧ c (pos m) ≠ 0) :=
    fun m hm => Nat.find_min hex hm
  generalize hm0def : Nat.find hex = m0 at hm0 hm0min
  have hm0lt : m0 < n - b := by
    by_contra h; exact hm0.2 (hpos_zero m0 (by omega) hm0.1)
  have hwinZ : ∀ m u, c (pos m) ≠ 0 → u < b →
      (⟨((i0 : ℕ) + b + m + n - u) % n, Nat.mod_lt _ hnpos⟩ : Fin n) ∈ Z := by
    intro m u hcm hu
    rw [hmemZ]
    refine ⟨u, hu, ?_⟩
    have he : cyc (⟨((i0 : ℕ) + b + m + n - u) % n, Nat.mod_lt _ hnpos⟩ : Fin n) u = pos m := by
      apply Fin.ext
      simp only [cyc, pos]
      rw [Nat.mod_add_mod, show (i0 : ℕ) + b + m + n - u + u = ((i0 : ℕ) + b + m) + n by omega,
        Nat.add_mod_right]
    rw [he]; exact hcm
  have hsupp : ∀ m, m < n → c (pos m) ≠ 0 → m < m0 + b := by
    intro m1 hm1 hc1
    by_contra hge
    push Not at hge
    have hm1lt : m1 < n - b := by
      by_contra h; exact hc1 (hpos_zero m1 (by omega) hm1)
    let f : Fin (2 * b) → Fin n := fun u =>
      if (u : ℕ) < b then ⟨((i0 : ℕ) + b + m0 + n - u) % n, Nat.mod_lt _ hnpos⟩
      else ⟨((i0 : ℕ) + b + m1 + n - (u - b)) % n, Nat.mod_lt _ hnpos⟩
    have hfZ : ∀ u, f u ∈ Z := by
      intro u
      simp only [f]
      split_ifs with hu
      · exact hwinZ m0 u hm0.2 hu
      · exact hwinZ m1 (u - b) hc1 (by omega)
    have hfinj : Function.Injective f := by
      intro u v huv
      apply Fin.ext
      have hu2 := u.2
      have hv2 := v.2
      have hi0 := i0.2
      simp only [f] at huv
      split_ifs at huv with hu hv hv
      · have h := congrArg Fin.val huv
        simp only at h
        have := mod_inj_range (by omega) (by omega) h
        omega
      · have h := congrArg Fin.val huv
        simp only at h
        have := mod_inj_range (by omega) (by omega) h
        omega
      · have h := congrArg Fin.val huv
        simp only at h
        have := mod_inj_range (by omega) (by omega) h
        omega
      · have h := congrArg Fin.val huv
        simp only at h
        have := mod_inj_range (by omega) (by omega) h
        omega
    have hcard : (univ.image f).card ≤ Z.card :=
      Finset.card_le_card (by intro x hx; obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx; exact hfZ u)
    rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_fin] at hcard
    omega
  -- the window containing the support
  let s0 := ((i0 : ℕ) + b + m0) % n
  have hs0 : s0 < n := Nat.mod_lt _ hnpos
  let w : Fin b → Fin n := fun t => ⟨(s0 + t) % n, Nat.mod_lt _ hnpos⟩
  have hw_inj : Function.Injective w := by
    intro t₁ t₂ h
    have h' := congrArg Fin.val h
    simp only [w] at h'
    exact Fin.ext (by have := mod_inj_range (n := n) (x := s0 + t₁) (y := s0 + t₂) (by omega) (by omega) h'; omega)
  have hout : ∀ p : Fin n, p ∉ univ.image w → c p = 0 := by
    intro p hp
    by_contra hcp
    obtain ⟨m, hm, rfl⟩ := hpos_surj p
    have h1 : m0 ≤ m := by
      by_contra h; exact hm0min m (by omega) ⟨hm, hcp⟩
    have h2 := hsupp m hm hcp
    apply hp
    refine Finset.mem_image.mpr ⟨⟨m - m0, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    simp only [w, pos, s0]
    rw [Nat.mod_add_mod, show (i0 : ℕ) + b + m0 + (m - m0) = (i0 : ℕ) + b + m by omega]
  have hrel : ∑ t : Fin b, c (w t) • V (F := F) b n ((s0 + t) % n) = 0 := by
    rw [← hc, parity_apply]
    rw [← Finset.sum_subset (Finset.subset_univ (univ.image w)) (fun p _ hp => by rw [hout p hp, zero_smul]),
      Finset.sum_image (fun x _ y _ h => hw_inj h)]
  have hgood := (windows_good (F := F) b n hb (by omega)).2 s0 hs0
  have hall := Fintype.linearIndependent_iff.mp hgood (fun t => c (w t)) hrel
  have hp0 : pos m0 = w ⟨0, by omega⟩ := by
    apply Fin.ext; simp only [pos, w, s0, Nat.add_zero, Nat.mod_mod]
  exact hm0.2 (hp0 ▸ hall ⟨0, by omega⟩)

theorem V_b_eq_V_zero {b n : ℕ} (hb : 1 ≤ b) (hn : 2 * b ≤ n) :
    V (F := F) b n b = V (F := F) b n 0 := by
  have hbpos : 0 < b := by omega
  have hA := (windows_good (F := F) b n hb (by omega)).1
  funext k
  simp only [V]
  rw [hA 0 k hbpos k.2]
  by_cases hdiv : n % b = 0
  · rw [sv_dvd (by omega) hdiv, Nat.mod_self]
  · have h2 : 2 ≤ n / b := (Nat.le_div_iff_mul_le hbpos).mpr (by omega)
    have hN : 2 * b ≤ n / b * b := Nat.mul_le_mul_right b h2
    rw [sv_block (by omega) hdiv (by omega), Nat.mod_self]

/-- An explicit codeword of `b`-weight at most `2b`. -/
theorem weight_le {b n : ℕ} (hb : 1 ≤ b) (hn : 2 * b ≤ n) :
    bWeight b ((Pi.single (⟨0, by omega⟩ : Fin n) (1 : F) : Fin n → F) -
      (Pi.single (⟨b, by omega⟩ : Fin n) (1 : F) : Fin n → F)) ≤ 2 * b := by
  classical
  have hnpos : 0 < n := by omega
  set x : Fin n → F := (Pi.single (⟨0, by omega⟩ : Fin n) (1 : F) : Fin n → F) -
    (Pi.single (⟨b, by omega⟩ : Fin n) (1 : F) : Fin n → F) with hx
  obtain ⟨Z, hZc, hmemZ⟩ : ∃ Z : Finset (Fin n), Z.card = bWeight b x ∧
      ∀ i : Fin n, i ∈ Z ↔ ∃ j, j < b ∧ x (cyc i j) ≠ 0 :=
    ⟨_, rfl, fun i => by simp⟩
  rw [← hZc]
  let g : Fin (2 * b) → Fin n := fun u => ⟨(n - b + 1 + u) % n, Nat.mod_lt _ hnpos⟩
  have hsub : Z ⊆ univ.image g := by
    intro i hi
    obtain ⟨j, hj, hxj⟩ := (hmemZ i).1 hi
    have hcases : (cyc i j : ℕ) = 0 ∨ (cyc i j : ℕ) = b := by
      by_contra hne
      push Not at hne
      apply hxj
      have h0 : cyc i j ≠ (⟨0, by omega⟩ : Fin n) := fun h => hne.1 (congrArg Fin.val h)
      have h1 : cyc i j ≠ (⟨b, by omega⟩ : Fin n) := fun h => hne.2 (congrArg Fin.val h)
      simp [hx, h0, h1]
    have hi2 := i.2
    have hm := mod_two (x := (i : ℕ) + j) (n := n) (by omega)
    simp only [cyc] at hcases
    rw [hm] at hcases
    rw [Finset.mem_image]
    by_cases hlt : (i : ℕ) + j < n
    · rw [ite_pos' hlt] at hcases
      rcases hcases with h | h
      · refine ⟨⟨b - 1, by omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
        simp only [g]
        rw [show n - b + 1 + (b - 1) = n by omega, Nat.mod_self]; omega
      · refine ⟨⟨2 * b - 1 - j, by omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
        simp only [g]
        rw [show n - b + 1 + (2 * b - 1 - j) = (b - j) + n by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]; omega
    · rw [ite_neg' hlt] at hcases
      rcases hcases with h | h
      · refine ⟨⟨b - 1 - j, by omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
        simp only [g]
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      · exfalso; omega
  calc Z.card ≤ (univ.image g).card := Finset.card_le_card hsub
    _ ≤ (univ : Finset (Fin (2 * b))).card := Finset.card_image_le
    _ = 2 * b := by simp

/-- **Ding–Zhang–Ge Conjecture 2 (MathDB 334207)**, for every finite field `F = F_q`:
for every `b ≥ 2` and `n ≥ 2b` there is a linear MDS `(n, 2b)_q` `b`-symbol code. -/
theorem dzg_conjecture2_field [Finite F] (b n : ℕ) (hb : 2 ≤ b) (hn : 2 * b ≤ n) :
    ∃ C : Submodule F (Fin n → F), IsLinearMDSBSymbol b (2 * b) C := by
  have hb1 : 1 ≤ b := by omega
  set x : Fin n → F := (Pi.single (⟨0, by omega⟩ : Fin n) (1 : F) : Fin n → F) -
    (Pi.single (⟨b, by omega⟩ : Fin n) (1 : F) : Fin n → F) with hx
  have hxC : parity (F := F) b n x = 0 := by
    rw [hx, map_sub, parity_single, parity_single, V_b_eq_V_zero hb1 hn, sub_self]
  have hx0 : x ≠ 0 := by
    intro h
    have h0 := congrFun h ⟨0, by omega⟩
    have hne : (⟨0, by omega⟩ : Fin n) ≠ ⟨b, by omega⟩ := fun e => by
      have := congrArg Fin.val e; simp at this; omega
    simp [hx, hne] at h0
  refine ⟨LinearMap.ker (parity (F := F) b n), ⟨⟨x, hxC, 0, Submodule.zero_mem _, hx0, ?_⟩, ?_⟩, ?_⟩
  · rw [bDist_eq_bWeight, sub_zero]
    exact le_antisymm (weight_le hb1 hn) (weight_ge hb1 hn x hxC hx0)
  · intro y hy z hz hyz
    rw [bDist_eq_bWeight]
    have hy' : parity (F := F) b n y = 0 := hy
    have hz' : parity (F := F) b n z = 0 := hz
    exact weight_ge hb1 hn (y - z) (by rw [map_sub, hy', hz', sub_zero]) (sub_ne_zero.mpr hyz)
  · rw [card_ker hb1 (by omega)]
    congr 1
    omega

/-- **Ding–Zhang–Ge Conjecture 2 (MathDB 334207)**, literal form: for every prime power `q`,
every `b ≥ 2` and every `n ≥ 2b`, every finite field of order `q` carries a linear MDS
`(n, 2b)_q` `b`-symbol code, and such a field exists. -/
theorem dzg_conjecture2 (q : ℕ) (hq : IsPrimePow q) (b n : ℕ) (hb : 2 ≤ b) (hn : 2 * b ≤ n) :
    (∃ (K : Type) (_ : Field K), Nat.card K = q) ∧
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = q →
      ∃ C : Submodule K (Fin n → K), IsLinearMDSBSymbol b (2 * b) C := by
  refine ⟨?_, fun K _ _ _ => dzg_conjecture2_field b n hb hn⟩
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).mp hq
  have : Fact p.Prime := ⟨hp⟩
  exact ⟨GaloisField p k, inferInstance, GaloisField.card p k hk.ne'⟩

end BSym334207
