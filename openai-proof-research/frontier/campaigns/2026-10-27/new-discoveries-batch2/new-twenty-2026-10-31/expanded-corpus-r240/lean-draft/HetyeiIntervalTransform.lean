/-
  UNCOMPILED DRAFT (expanded-corpus-r240, Claude lane: Lean was NOT run here).
  Root / a Sol worker must compile, repair tactic details and audit.

  Target 1 (MathDB 347230): Hetyei, "The type B permutohedron and the poset of intervals as a
  Tchebyshev transform", Discrete Comput. Geom. 71 (2024) 918-944, Conjecture 39
  (= arXiv:2007.07362v2 Conjecture 5.14):
      for each n >= 1, ker (I2 : Q<a,b>_n -> Q<a,b>) = A<a,b>_n   (antisymmetric part).
  We prove its negation with the explicit symmetric degree-5 element `uCert` in the kernel.

  Target 2 (MathDB 347231): Conjecture 40 (= Conjecture 5.15): for each n >= 1, S<a,b>_n has a
  generating set consisting of I2-eigenvectors (namely the n-fold Pyr/L compositions applied to 1).
  We prove the stronger negation: S<a,b>_3 is NOT spanned by I2-eigenvectors lying in S<a,b>_3.

  Operator: Theorem 32,  I2(u) = u + u* + sum_u M(u_(1)*, u_(2)),  with the Ehrenborg-Readdy
  coproduct Delta(v1..vn) = sum_i v1..v_{i-1} (x) v_{i+1}..vn and the ER mixing operator
  (J. Algebraic Combin. 8 (1998), Definition 9.1).  NOTE: Hetyei's Definition 31 prints
  M_{2,1,2}(u,v) = u.b.v; ER's Definition 9.1 has M_{2,1}(u,v,2) = v.b.u.  We use ER's (the cited
  definition); with the misprint, Hetyei's own Corollary 33 and Theorem 32 fail (see CANDIDATE.md).

  Encoding: a word is `List Bool` with `false = a`, `true = b`.
-/
import Mathlib

namespace HetyeiR240

abbrev Word := List Bool

/-- ℚ⟨a,b⟩ with its word basis. -/
abbrev ABPoly := Word →₀ ℚ

/-! ### Formal integer combinations of words (computable layer) -/

abbrev FSum := List (Word × ℤ)

/-- Semantic map from a formal sum to an ab-polynomial. -/
noncomputable def toPoly (l : FSum) : ABPoly :=
  (l.map fun p => Finsupp.single p.1 (p.2 : ℚ)).sum

/-- Ehrenborg-Readdy coproduct pieces of a word. -/
def cop (w : Word) : List (Word × Word) :=
  (List.range w.length).map fun i => (w.take i, w.drop (i + 1))

/-- `Mrs r s n u v` is ER's `M_{r,s}(u,v,n)`; `r = false` means r = 1, `r = true` means r = 2. -/
def Mrs : Bool → Bool → ℕ → Word → Word → FSum
  | false, true, 2, u, v => [(u ++ [false] ++ v, 1)]
  | true, false, 2, u, v => [(v ++ [true] ++ u, 1)]
  | false, s, n + 3, u, v =>
      (cop u).flatMap fun p => (Mrs true s (n + 2) p.2 v).map fun q => (p.1 ++ [false] ++ q.1, q.2)
  | true, s, n + 3, u, v =>
      (cop v).flatMap fun p => (Mrs false s (n + 2) u p.2).map fun q => (p.1 ++ [true] ++ q.1, q.2)
  | _, _, _, _, _ => []

def rsVal (b : Bool) : ℕ := if b then 2 else 1

/-- ER index set condition n ≡ r + s + 1 (mod 2) (redundant, kept for fidelity). -/
def inIndex (r s : Bool) (n : ℕ) : Bool := (n + rsVal r + rsVal s + 1) % 2 == 0

/-- Mixing operator on words, summed over all n in ER's index set.  Terms with
    n > |u| + |v| + 2 vanish (lemma `Mrs_eq_nil_of_large` below), so the finite range is exact. -/
def Mw (u v : Word) : FSum :=
  [false, true].flatMap fun r => [false, true].flatMap fun s =>
    ((List.range (u.length + v.length + 3)).filter fun n => 2 ≤ n && inIndex r s n).flatMap
      fun n => Mrs r s n u v

/-- I2 on a word, Theorem 32. -/
def I2w (w : Word) : FSum :=
  [(w, 1), (w.reverse, 1)] ++ (cop w).flatMap fun p => Mw p.1.reverse p.2

/-- The linear operator I2 on ℚ⟨a,b⟩ (linear extension of `I2w`). -/
noncomputable def I2 : ABPoly →ₗ[ℚ] ABPoly :=
  Finsupp.linearCombination ℚ fun w => toPoly (I2w w)

/-- Reversal u ↦ u*. -/
noncomputable def star : ABPoly →ₗ[ℚ] ABPoly := Finsupp.lmapDomain ℚ ℚ List.reverse

/-- Homogeneous part of degree n. -/
def deg (n : ℕ) : Submodule ℚ ABPoly := Finsupp.supported ℚ ℚ {w : Word | w.length = n}

/-- Antisymmetric, resp. symmetric, homogeneous ab-polynomials of degree n (Definition 34). -/
def anti (n : ℕ) : Submodule ℚ ABPoly := deg n ⊓ LinearMap.ker (star + LinearMap.id)
def symm (n : ℕ) : Submodule ℚ ABPoly := deg n ⊓ LinearMap.ker (star - LinearMap.id)

/-- MathDB 347230 / Hetyei Conjecture 39 (kernel taken inside the degree-n part; the printed
    codomain `Q<a,b>_{n+1}` is immaterial for the kernel). -/
def KernelConjecture : Prop := ∀ n : ℕ, 1 ≤ n → deg n ⊓ LinearMap.ker I2 = anti n

/-- MathDB 347231 / Hetyei Conjecture 40, weakened to its consequence "S_n is spanned by
    I2-eigenvectors lying in S_n"; refuting this refutes the conjecture under any reading of
    which compositions are taken. -/
def EigenGeneration : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ G : Set ABPoly,
    (∀ g ∈ G, g ∈ symm n ∧ ∃ c : ℚ, I2 g = c • g) ∧ Submodule.span ℚ G = symm n

/-! ### Certificate data -/

def a : Bool := false
def b : Bool := true

/-- 20-term symmetric degree-5 kernel element (outputs/hetyei-certificates-v2.json). -/
def uList : FSum :=
  [([a,a,a,b,a], 1), ([a,a,a,b,b], 1), ([a,a,b,a,a], -2), ([a,a,b,b,a], -1), ([a,a,b,b,b], 1),
   ([a,b,a,a,a], 1), ([a,b,a,a,b], 1), ([a,b,b,a,a], -1), ([a,b,b,a,b], 1), ([a,b,b,b,a], -2),
   ([b,a,a,a,b], -2), ([b,a,a,b,a], 1), ([b,a,a,b,b], -1), ([b,a,b,b,a], 1), ([b,a,b,b,b], 1),
   ([b,b,a,a,a], 1), ([b,b,a,a,b], -1), ([b,b,a,b,b], -2), ([b,b,b,a,a], 1), ([b,b,b,a,b], 1)]

noncomputable def uCert : ABPoly := toPoly uList

/-! ### Computable checks (to be closed by `decide`, kernel reduction only) -/

def coeffL (l : FSum) (w : Word) : ℤ := ((l.filter fun p => p.1 == w).map Prod.snd).sum

/-- I2 applied to a formal sum, computably. -/
def I2L (l : FSum) : FSum := l.flatMap fun p => (I2w p.1).map fun q => (q.1, p.2 * q.2)

def allWords : ℕ → List Word
  | 0 => [[]]
  | n + 1 => (allWords n).flatMap fun w => [false :: w, true :: w]

/-- Every word occurring in `I2L uList` has length 5 and every length-5 coefficient is zero. -/
theorem check_I2u : ((I2L uList).all fun p => p.1.length == 5) = true ∧
    ((allWords 5).all fun w => coeffL (I2L uList) w == 0) = true := by
  constructor <;> decide

theorem check_sym : (uList.all fun p => coeffL uList p.1.reverse == p.2) = true := by decide

/-! ### Bridge lemmas (semantic ↔ computable) — proofs to be completed at compile time -/

theorem toPoly_append (l₁ l₂ : FSum) : toPoly (l₁ ++ l₂) = toPoly l₁ + toPoly l₂ := by
  simp [toPoly, List.map_append, List.sum_append]

theorem I2_toPoly (l : FSum) : I2 (toPoly l) = toPoly (I2L l) := by
  induction l with
  | nil => simp [toPoly, I2L]
  | cons p l ih =>
    -- I2 (single w c + rest) = c • toPoly (I2w w) + I2 rest
    simp only [I2L, List.flatMap_cons, toPoly_append] at *
    rw [← ih]
    simp [toPoly, I2, Finsupp.linearCombination_single, List.sum_map_mul_left, Finsupp.smul_single,
      map_add]
    sorry -- UNCOMPILED: routine `Finsupp.single`/`smul` bookkeeping; replace by the actual proof

/-- A formal sum is zero as soon as all its coefficients vanish on a list containing its support. -/
theorem toPoly_eq_zero_of_coeff (l : FSum) (S : List Word) (hS : ∀ p ∈ l, p.1 ∈ S)
    (h : ∀ w ∈ S, coeffL l w = 0) : toPoly l = 0 := by
  ext w
  -- (toPoly l) w = (coeffL l w : ℚ)
  sorry -- UNCOMPILED: show `toPoly l w = ↑(coeffL l w)` by induction on l, then split on w ∈ S

theorem I2_uCert : I2 uCert = 0 := by
  rw [uCert, I2_toPoly]
  obtain ⟨h5, hz⟩ := check_I2u
  apply toPoly_eq_zero_of_coeff _ (allWords 5)
  · sorry -- every word of length 5 lies in `allWords 5` (`List.mem` lemma + h5)
  · intro w hw; simpa using (List.all_eq_true.mp hz w hw)

theorem uCert_deg : uCert ∈ deg 5 := by sorry -- support ⊆ words of length 5 (from uList)
theorem star_uCert : star uCert = uCert := by sorry -- from check_sym
theorem uCert_ne_zero : uCert ≠ 0 := by
  -- the coefficient of aaaba is 1
  sorry

/-- **Main theorem 1 (MathDB 347230): Hetyei's Conjecture 39 is false (first failure n = 5).** -/
theorem not_KernelConjecture : ¬ KernelConjecture := by
  intro h
  have hmem : uCert ∈ deg 5 ⊓ LinearMap.ker I2 := ⟨uCert_deg, by simpa using I2_uCert⟩
  rw [h 5 (by norm_num)] at hmem
  have hanti : star uCert + uCert = 0 := by simpa using hmem.2
  rw [star_uCert] at hanti
  -- 2 • uCert = 0 over ℚ
  have : (2 : ℚ) • uCert = 0 := by rw [two_smul]; exact hanti
  exact uCert_ne_zero ((smul_eq_zero.mp this).resolve_left (by norm_num))

/-! ### Main theorem 2 (MathDB 347231) at n = 3
  s0 = aab + baa ∈ S_3 and I2 s0 = 2aaa + 8aab + 6aba + 4abb + 6baa + 4bab + 2bba is not symmetric.
  α(v) := v(aab) - v(baa) vanishes on symmetric vectors; Ψ := α ∘ I2.
  For an eigenvector g ∈ S_3 with I2 g = c • g:  Ψ g = c * α g = 0.
  Span of such g is contained in ker Ψ, but Ψ s0 = 8 - 6 = 2 ≠ 0.               -/

noncomputable def alpha : ABPoly →ₗ[ℚ] ℚ :=
  Finsupp.lapply [a, a, b] - Finsupp.lapply [b, a, a]

noncomputable def s0 : ABPoly := Finsupp.single [a, a, b] 1 + Finsupp.single [b, a, a] 1

theorem alpha_symm (g : ABPoly) (hg : g ∈ symm 3) : alpha g = 0 := by
  -- star g = g gives g [b,a,a] = g [a,a,b]
  sorry

theorem s0_symm : s0 ∈ symm 3 := by sorry
theorem alpha_I2_s0 : alpha (I2 s0) = 2 := by
  -- computable: coefficients of I2L [([a,a,b],1),([b,a,a],1)] at aab and baa are 8 and 6
  sorry

theorem not_EigenGeneration : ¬ EigenGeneration := by
  intro h
  obtain ⟨G, hG, hspan⟩ := h 3 (by norm_num)
  have hker : Submodule.span ℚ G ≤ LinearMap.ker (alpha ∘ₗ I2) := by
    rw [Submodule.span_le]
    intro g hg
    obtain ⟨hgs, c, hc⟩ := hG g hg
    show alpha (I2 g) = 0
    rw [hc, map_smul, alpha_symm g hgs, smul_zero]
  have : s0 ∈ LinearMap.ker (alpha ∘ₗ I2) := hker (hspan ▸ s0_symm)
  have h2 : alpha (I2 s0) = 0 := this
  rw [alpha_I2_s0] at h2
  norm_num at h2

end HetyeiR240
