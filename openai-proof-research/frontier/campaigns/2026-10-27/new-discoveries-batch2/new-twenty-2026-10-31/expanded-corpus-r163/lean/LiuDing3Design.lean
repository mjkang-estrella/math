/-
  UNCOMPILED DRAFT — NOT A CERTIFICATE.
  Claude lane expanded-corpus-r163 is forbidden to run Lean/lake.  This file records the
  literal statement-correspondence and the lemma decomposition of the ordinary proof in
  CANDIDATE-336565.md.  Every `sorry` below is an explicit open proof obligation for the
  root / Sol formalization stage; names of Mathlib lemmas cited in comments are best guesses
  and must be checked against the pinned Mathlib (d13f23b7).

  Target: MathDB 336565 = Liu–Ding, arXiv:1707.02003v1, Conjecture 1:
    for q = 2^m, m ≥ 3, m ≢ 0 (mod 4), the orbit design (GF(q), GA₁(q)(B₂)) with
    B₂ = {u : Tr(u³ − u) = 1} is a 3-design.
-/
import Mathlib

open Finset

namespace LiuDing

/-- The field GF(2^m). -/
abbrev F (m : ℕ) := GaloisField 2 m

/-- Absolute trace GF(2^m) → GF(2) = ZMod 2. -/
noncomputable def Tr {m : ℕ} (x : F m) : ZMod 2 := Algebra.trace (ZMod 2) (F m) x

/-- Base block B₂ = {u ∈ GF(q) : Tr(u³ − u) = 1} (literal, no char-2 rewriting). -/
noncomputable def B₂ (m : ℕ) : Finset (F m) :=
  univ.filter (fun u => Tr (u ^ 3 - u) = 1)

/-- The orbit GA₁(q)(B₂) = {a·B₂ + b : a ≠ 0} as a *set* of blocks (source Corollary 2). -/
noncomputable def blocks (m : ℕ) : Finset (Finset (F m)) :=
  ((univ : Finset (F m × F m)).filter (fun p => p.1 ≠ 0)).image
    (fun p => (B₂ m).image (fun x => p.1 * x + p.2))

/-- Source §1 definition: 𝓑 is a set of k-subsets of P and every t-subset of P lies in
exactly λ blocks. -/
def IsTDesign {α : Type*} [DecidableEq α] (t : ℕ) (P : Finset α) (𝓑 : Finset (Finset α)) :
    Prop :=
  (∃ k : ℕ, ∀ C ∈ 𝓑, C ⊆ P ∧ C.card = k) ∧
  ∃ lam : ℕ, ∀ T ⊆ P, T.card = t → (𝓑.filter (fun C => T ⊆ C)).card = lam

/-- The literal conjecture. -/
def Conjecture1 : Prop :=
  ∀ m : ℕ, 3 ≤ m → m % 4 ≠ 0 → IsTDesign 3 (univ : Finset (F m)) (blocks m)

/-! ### Ingredients (open obligations) -/

section Ingredients
variable {m : ℕ}

/-- ±1 character of the trace. -/
noncomputable def ψ (z : ZMod 2) : ℤ := if z = 0 then 1 else -1

lemma ψ_add (a b : ZMod 2) : ψ (a + b) = ψ a * ψ b := by
  -- finite case split on ZMod 2
  fin_cases a <;> fin_cases b <;> simp [ψ] <;> decide

lemma char_two (x : F m) : x + x = 0 := by
  -- CharP (GaloisField 2 m) 2 ; `CharTwo.add_self_eq_zero`
  sorry

lemma Tr_add (x y : F m) : Tr (x + y) = Tr x + Tr y := by
  simp [Tr, map_add]

lemma Tr_sq (x : F m) : Tr (x ^ 2) = Tr x := by
  -- Frobenius invariance of the trace: trace (frobenius x) = trace x, e.g. via
  -- `Algebra.trace_eq_sum_automorphisms` / trace is invariant under AlgEquiv,
  -- with frobenius an AlgEquiv over ZMod 2 (`FiniteField.frobeniusAlgEquivOfAlgebraic`).
  sorry

/-- Orthogonality: Σ_x ψ(Tr(a x)) = q·[a = 0]. Uses `FiniteField.trace_to_zmod_nondegenerate`. -/
lemma sum_psi_Tr_mul (a : F m) :
    (∑ x : F m, ψ (Tr (a * x))) = if a = 0 then (Fintype.card (F m) : ℤ) else 0 := by
  sorry

/-- χ(x) = (−1)^{Q(x)} with Q(x) = Tr(x³ − x). -/
noncomputable def χ (x : F m) : ℤ := ψ (Tr (x ^ 3 - x))

/-- s = Σ χ. -/
noncomputable def s (m : ℕ) : ℤ := ∑ x : F m, χ x

/-- Step 2 (quadratic identity), char 2, u ≠ 1, e = (1+u) d, a = u/(1+u)^2:
Q(x)+Q(x+d)+Q(x+ud) = Q(x+e) + Tr(a e³). -/
lemma step2 (x d u : F m) (hu1 : u ≠ 1) :
    Tr (x ^ 3 - x) + Tr ((x + d) ^ 3 - (x + d)) + Tr ((x + u * d) ^ 3 - (x + u * d)) =
      Tr ((x + (1 + u) * d) ^ 3 - (x + (1 + u) * d)) +
        Tr (u / (1 + u) ^ 2 * ((1 + u) * d) ^ 3) := by
  -- pure ring identity in characteristic 2 (after clearing (1+u)^2 ≠ 0), then Tr_add
  sorry

/-- Triple sum T(u) = s · S(u/(1+u)²). -/
lemma triple_sum (u : F m) (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    (∑ x : F m, ∑ d : F m, χ x * χ (x + d) * χ (x + u * d)) =
      s m * ∑ e : F m, ψ (Tr (u / (1 + u) ^ 2 * e ^ 3)) := by
  -- reindex d ↦ e = (1+u) d (bijective since 1+u ≠ 0), apply step2 and ψ_add,
  -- then x ↦ x + e in the inner sum
  sorry

/-- Step 3: for odd m, cubing is a bijection, so S(a) = 0 for a ≠ 0. -/
lemma cube_sum_zero_of_odd (hodd : m % 2 = 1) (a : F m) (ha : a ≠ 0) :
    (∑ e : F m, ψ (Tr (a * e ^ 3))) = 0 := by
  -- gcd(3, 2^m - 1) = 1 for m odd; e ↦ e^3 bijective on F m; then sum_psi_Tr_mul
  sorry

/-- Step 4: for m ≡ 2 (mod 4), s = 0 (B₂ is balanced; reproves source Lemma 18). -/
lemma s_zero_of_two_mod_four (h : m % 4 = 2) : s m = 0 := by
  -- s^2 = q · Σ_{e^4 = e} ψ(Tr(e^3 + e)) via Tr_sq and sum_psi_Tr_mul; the four elements of
  -- GF(4) ⊆ GF(2^m) contribute 1 + 1 - 1 - 1 since Tr(ω) = m/2 mod 2 = 1
  sorry

/-- Step 0+1: blocks through a 3-set T, times |Stab|, equals N(u_T) − k, and
8 N(u) = q² − 3 q s + 3 s² − T(u). -/
lemma blocks_through_triple_const (hm : 3 ≤ m) (h4 : m % 4 ≠ 0) :
    ∃ lam : ℕ, ∀ T : Finset (F m), T.card = 3 →
      ((blocks m).filter (fun C => T ⊆ C)).card = lam := by
  -- fibre counting for p ↦ p.1 • B₂ + p.2 (fibres = cosets of the stabiliser, constant size);
  -- change of variables (a,b) ↦ (x,d); expansion of ∏ (1 - χ)/2; triple_sum;
  -- case m odd: cube_sum_zero_of_odd; case m ≡ 2 mod 4: s_zero_of_two_mod_four
  sorry

end Ingredients

/-- ENDPOINT (literal full-scope statement of Liu–Ding Conjecture 1). -/
theorem conjecture1_holds : Conjecture1 := by
  intro m hm h4
  refine ⟨⟨(B₂ m).card, ?_⟩, ?_⟩
  · intro C hC
    refine ⟨subset_univ _, ?_⟩
    -- C = B₂.image (a·x+b) with a ≠ 0, an injective map
    simp only [blocks, mem_image, mem_filter] at hC
    obtain ⟨p, ⟨-, hp⟩, rfl⟩ := hC
    exact card_image_of_injective _ (fun x y hxy => by
      have : p.1 * x = p.1 * y := add_right_cancel hxy
      exact mul_left_cancel₀ hp this)
  · obtain ⟨lam, hlam⟩ := blocks_through_triple_const (m := m) hm h4
    exact ⟨lam, fun T _ hT => hlam T hT⟩

end LiuDing
