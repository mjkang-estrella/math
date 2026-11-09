/-
  UNCOMPILED DRAFT (expanded-corpus-r146, Claude lane, 2026-11-04).  Lean/lake were NOT run in this
  lane (Claude lane restriction).  `sorry` marks the remaining proof obligations listed in
  outputs/337352-proof.md §6; this file is a statement-correspondence and architecture draft, NOT a
  certificate.  Target: Lean 4.34.1 + mathlib d13f23b7 (root/Sol compile).

  MathDB 337352 = Cheon–Jung–Kitaev–Mojallal, Riordan graphs I (arXiv:1710.04604), Conjecture 2,
  family reading (R2), plus the exact per-k statement for k ≥ 4.
-/
import Mathlib

namespace Riordan337352

open SimpleGraph

/-- Binary A-sequence: `a : ℕ → ZMod 2` with `a 0 = 1`. -/
structure ASeq where
  a : ℕ → ZMod 2
  a0 : a 0 = 1

/-- Binary Bell matrix `B(g, z g)` from its A-sequence, Jung (arXiv:1901.11156) eq. (9):
  b 0 0 = 1;  b (i+1) 0 = Σ_{t ≤ i} a (t+1) * b i t;  b (i+1) (j+1) = Σ_{t ≤ i-j} a t * b i (j+t);
  entries above the diagonal are 0. -/
def bell (A : ASeq) : ℕ → ℕ → ZMod 2
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | i + 1, 0 => ∑ t ∈ Finset.range (i + 1), A.a (t + 1) * bell A i t
  | i + 1, j + 1 =>
      if j ≤ i then ∑ t ∈ Finset.range (i - j + 1), A.a t * bell A i (j + t) else 0
termination_by i _ => i

/-- Riordan graph `G_n(g, zg)` on vertices `1..n` (encoded as `Fin n`, vertex `v` ↔ label `v+1`):
  for labels `i > j ≥ 1`, `i ~ j ↔ b_{i-2, j-1} = 1` (CJKM eq. (4)). -/
def riordanGraph (A : ASeq) (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧
    (if (v : ℕ) < u then bell A ((u : ℕ) + 1 - 2) ((v : ℕ) + 1 - 1) = 1
     else bell A ((v : ℕ) + 1 - 2) ((u : ℕ) + 1 - 1) = 1)
  symm := by
    intro u v ⟨h, h'⟩
    refine ⟨Ne.symm h, ?_⟩
    rcases lt_trichotomy (u : ℕ) v with huv | huv | huv
    · simp [huv, not_lt.mpr huv.le] at h' ⊢; exact h'
    · exact absurd (Fin.ext huv) h
    · simp [huv, not_lt.mpr huv.le] at h' ⊢; exact h'
  loopless := fun _ h => h.1 rfl

/-- io-decomposable Bell type (CJKM Thm 4.6 = Jung Lemma 2.1): A-sequence (1,1,a2,a2,a4,a4,…). -/
def IoBell (A : ASeq) : Prop := A.a 1 = 1 ∧ ∀ m, A.a (2 * m + 1) = A.a (2 * m)

/-- Catalan graph: A-sequence all ones (A(z) = 1/(1-z)). -/
def catalanA : ASeq := ⟨fun _ => 1, rfl⟩

/-- Diameter as in CJKM Def. 4.21 (graphs here are connected; `SimpleGraph.diam` is the mathlib notion). -/
noncomputable def diam' {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := G.diam

/-! ### Main theorem (exact per-k statement for k ≥ 4) -/

/-- Obligation 4 (base case k = 4): finite, intended for kernel `decide` through a proved-sound
  BFS checker over the 2^7 io-prefixes (a_0..a_14). -/
theorem base_k4 (A : ASeq) (hio : IoBell A) (hd : diam' (riordanGraph A 16) = 4) :
    ∀ i ≤ 14, A.a i = 1 := by
  sorry

/-- Lemma A (neighbours of the last vertex N = 2^K): N ~ j ↔ j odd ∧ [w^{N-1-j}] A^{-1} = 1.
  Obligations 1–2 (generating-function bridge and Lagrange inversion mod 2). -/
theorem lemmaA (A : ASeq) (K j : ℕ) (hj1 : 1 ≤ j) (hjN : j < 2 ^ K) :
    bell A (2 ^ K - 2) (j - 1) = 1 ↔
      (j % 2 = 1 ∧ PowerSeries.coeff (ZMod 2) (2 ^ K - 1 - j)
          (PowerSeries.invOfUnit (PowerSeries.mk A.a) 1) = 1) := by
  sorry

/-- Lemma C (one zero beyond the all-ones prefix lowers the diameter), K ≥ 4.
  Uses Lemma B (closed form j = N-1-p) and the published structural facts (P1)–(P3)
  (obligation 3). -/
theorem lemmaC (A : ASeq) (hio : IoBell A) (K : ℕ) (hK : 4 ≤ K)
    (hpre : ∀ i < 2 ^ (K - 1), A.a i = 1)
    (hzero : ∃ p, 2 ^ (K - 1) ≤ p ∧ p ≤ 2 ^ K - 2 ∧ A.a p = 0) :
    diam' (riordanGraph A (2 ^ K)) ≤ K - 1 := by
  sorry

/-- (P4)+(P5) packaged: diam(G_{2^{k+1}}) = k+1 → diam(G_{2^k}) = k  (k ≥ 2). Obligation 3. -/
theorem diam_step (A : ASeq) (hio : IoBell A) (k : ℕ) (hk : 2 ≤ k)
    (hd : diam' (riordanGraph A (2 ^ (k + 1))) = k + 1) :
    diam' (riordanGraph A (2 ^ k)) = k := by
  sorry

/-- G_{2^k} depends only on a_0..a_{2^k-2} (obligation 1, routine). -/
theorem graph_congr (A B : ASeq) (n : ℕ) (h : ∀ i, i + 2 ≤ n → A.a i = B.a i) :
    riordanGraph A n = riordanGraph B n := by
  sorry

/-- **Main theorem.** For k ≥ 4, an io-decomposable Bell-type G_{2^k} of diameter k has
  all-ones A-prefix, hence equals CG_{2^k} as a labelled graph. -/
theorem catalan_unique (k : ℕ) (hk : 4 ≤ k) (A : ASeq) (hio : IoBell A)
    (hd : diam' (riordanGraph A (2 ^ k)) = k) : ∀ i, i ≤ 2 ^ k - 2 → A.a i = 1 := by
  induction k, hk using Nat.le_induction with
  | base => simpa using base_k4 A hio hd
  | succ k hk ih =>
    have hprev := ih (diam_step A hio k (by omega) hd)
    -- prefix a_0..a_{2^k-1} all ones (a_{2^k-1} = a_{2^k-2} by io-decomposability)
    have hpre : ∀ i < 2 ^ k, A.a i = 1 := by
      sorry
    by_contra hne
    push_neg at hne
    obtain ⟨p, hp, hpa⟩ := hne
    have hp' : 2 ^ k ≤ p := by
      by_contra h; exact hpa (hpre p (by omega))
    have hz : A.a p = 0 := by
      rcases (show A.a p = 0 ∨ A.a p = 1 by fin_cases (A.a p) <;> simp) with h | h
      · exact h
      · exact absurd h hpa
    have := lemmaC A hio (k + 1) (by omega) (by simpa using hpre)
      ⟨p, by simpa using hp', by simpa using hp, hz⟩
    omega

/-- Jung, Theorem 2.4 (published): diam(CG_{2^k}) = k.  Obligation 3. -/
theorem diam_catalan (k : ℕ) (hk : 1 ≤ k) : diam' (riordanGraph catalanA (2 ^ k)) = k := by
  sorry

/-- **Conjecture 2, family reading (R2).**  If an io-decomposable Bell-type A-sequence gives diameter
  k on 2^k vertices for every k ≥ 1, then A is the Catalan A-sequence; and the Catalan family does
  have diameter k for every k ≥ 1. -/
theorem conjecture2_family :
    (∀ k ≥ 1, diam' (riordanGraph catalanA (2 ^ k)) = k) ∧
    ∀ A : ASeq, IoBell A → (∀ k ≥ 1, diam' (riordanGraph A (2 ^ k)) = k) → ∀ i, A.a i = 1 := by
  refine ⟨fun k hk => diam_catalan k hk, fun A hio hall i => ?_⟩
  have h := catalan_unique (i + 4) (by omega) A hio (hall (i + 4) (by omega)) i
  apply h
  have : i + 4 ≤ 2 ^ (i + 4) := Nat.lt_two_pow_self.le.trans' (by omega)
  sorry -- arithmetic: i ≤ 2^(i+4) - 2

end Riordan337352
