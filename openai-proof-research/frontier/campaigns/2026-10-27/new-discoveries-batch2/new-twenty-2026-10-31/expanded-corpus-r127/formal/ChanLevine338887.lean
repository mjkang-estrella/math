/-
  UNCOMPILED DRAFT — NOT A CERTIFICATE.  Lane expanded-corpus-r127 was forbidden to run Lean.
  Contains `sorry` placeholders for the three analytic lemmas (marked PLACEHOLDER); the endpoint
  must not be counted until root / a Sol worker replaces them and replays strictly
  (-DwarningAsError=true, leanchecker, #print axioms ⊆ {propext, Classical.choice, Quot.sound}).

  MathDB 338887 = Chan–Levine, Abelian networks IV (arXiv:1804.03322), Conjecture 8.3.
  Semantic bridge (NOT formalised here; see outputs/338887-lean-plan.md):
    r(C_{n,m,i}) = recCount n m i, by the source's cycle test (Thm 7.4), Lemma 5.19 and §8.3
    (weight invariance + uniqueness of C_{n,m,i}).  Root must rule on whether this count
    formulation is an acceptable literal endpoint or whether the abelian-network semantics must
    be formalised as well.
-/
import Mathlib

open Finset BigOperators

namespace ChanLevine338887

variable {n : ℕ} [NeZero n]

/-- Rotor at vertex `k`: `true` = points to `k+1` (edge weight 0); `false` = points to `k-1`
(edge weight 1, the edge `(v_k, v_{k-1})` of the source). -/
abbrev Rotor (n : ℕ) := ZMod n → Bool

/-- Cycle test specialised to the bidirected cycle (n ≥ 3): every 2-cycle of the rotor digraph
(facing pair `k → k+1`, `k+1 → k`) contains a chip, and each of the two Hamiltonian rotor cycles
contains a chip. -/
def Recurrent (x : ZMod n → ℕ) (q : Rotor n) : Prop :=
  (∀ k : ZMod n, q k = true → q (k + 1) = false → (x k ≠ 0 ∨ x (k + 1) ≠ 0)) ∧
  ((∀ k, q k = true) → ∃ k, x k ≠ 0) ∧
  ((∀ k, q k = false) → ∃ k, x k ≠ 0)

instance (x : ZMod n → ℕ) (q : Rotor n) : Decidable (Recurrent x q) := by
  unfold Recurrent; infer_instance

/-- The source's weight `Σ_k k·x(v_k) + Σ_k wt(q(v_k)) mod n`. -/
def weight (x : ZMod n → ℕ) (q : Rotor n) : ZMod n :=
  (∑ k : ZMod n, k * (x k : ZMod n)) + ((univ.filter fun k => q k = false).card : ZMod n)

/-- Number of recurrent configurations with `m` chips and weight `i`
(chips bounded by `m`, which is no restriction since `Σ x = m`). -/
def recCount (n m : ℕ) [NeZero n] (i : ZMod n) : ℕ :=
  ((univ : Finset ((ZMod n → Fin (m + 1)) × Rotor n)).filter fun c =>
      (∑ k, (c.1 k : ℕ)) = m ∧ Recurrent (fun k => (c.1 k : ℕ)) c.2 ∧
        weight (fun k => (c.1 k : ℕ)) c.2 = i).card

/-! ### Step 1: rotation shifts the weight by `m` -/

/-- PLACEHOLDER-FREE TARGET (elementary): the rotation `ρ(x,q)(k) = (x(k-1), q(k-1))` is a bijection
of the counted set adding `m` to the weight. -/
theorem recCount_add_m (n m : ℕ) [NeZero n] (i : ZMod n) :
    recCount n m (i + m) = recCount n m i := by
  sorry -- PLACEHOLDER: Finset.card_bij with the rotation; weight computation
        -- Σ_k k·x(k-1) = Σ_j (j+1)·x(j) = Σ_j j·x(j) + Σ_j x(j).

/-! ### Step 2–6: evaluation at roots of unity depends only on the order -/

/-- `W_m(ω) = Σ_{recurrent, m chips} ω^{wt}` for `ω^n = 1`, written with the integer
representative `ZMod.val`. -/
noncomputable def W (n m : ℕ) [NeZero n] (ω : ℂ) : ℂ :=
  ∑ i : ZMod n, (recCount n m i : ℂ) * ω ^ i.val

/-- Lucas sequence attached to the period trace `p = 2 + q_e T` and determinant `(1-T)^2`,
as polynomials in `T = t^e`. -/
noncomputable def qe (e : ℕ) : ℤ := if e % 2 = 1 then 0 else if e % 4 = 0 then 2 else -2

noncomputable def lucas (e : ℕ) : ℕ → Polynomial ℤ
  | 0 => 2
  | 1 => Polynomial.C 2 + Polynomial.C (qe e) * Polynomial.X
  | (j + 2) => (Polynomial.C 2 + Polynomial.C (qe e) * Polynomial.X) * lucas e (j + 1)
               - (1 - Polynomial.X) ^ 2 * lucas e j

/-- The integer `w_{n,m}(e)`: coefficient of `T^{m/e}` in `lucas e (n/e) / (1-T)^{n/e} - 2`
when `e ∣ m`, and `0` otherwise. -/
noncomputable def w (n m e : ℕ) : ℤ :=
  if e ∣ m then
    (PowerSeries.coeff ℤ (m / e)
      ((lucas e (n / e) : PowerSeries ℤ) *
        (PowerSeries.invOfUnit ((1 - PowerSeries.X) ^ (n / e)) 1))) - (if m = 0 then 2 else 0)
  else 0

/-- Main analytic lemma (proof in outputs/338887-proof.md, Steps 2–6: inclusion–exclusion to a
matching sum, 2×2 domino transfer matrices `X_k = [[1+ζ, -ζ(1-tζ^k)], [1-tζ^k, 0]]`, period
`P = X_0⋯X_{e-1}` with `det P = (1-t^e)^2`, rotation + degree forcing `Tr P = 2 + q_e t^e`,
Cayley–Hamilton). -/
theorem W_primitive (n m e : ℕ) [NeZero n] (hn : 3 ≤ n) (he : e ∣ n) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ e) : W n m ζ = (w n m e : ℂ) := by
  sorry -- PLACEHOLDER (main formalisation effort; see plan)

/-! ### Fourier inversion and orbit lemma -/

/-- Unit invariance, from `W_primitive` (value depends only on the order of `ζ^k`, which is
unchanged by `k ↦ u k`) and injectivity of the discrete Fourier transform on `ZMod n`
(`ZMod.dft`, Mathlib.Analysis.Fourier.ZMod). -/
theorem recCount_mul_unit (n m : ℕ) [NeZero n] (hn : 3 ≤ n) (u : (ZMod n)ˣ) (i : ZMod n) :
    recCount n m (u * i) = recCount n m i := by
  sorry -- PLACEHOLDER: dft argument

/-- Elementary number theory: if `gcd(d, i) = gcd(d, j)` with `d = gcd(n, m)` then
`j = u*i + b*m` for a unit `u` of `ZMod n` and some `b`. -/
theorem orbit (n m : ℕ) [NeZero n] (i j : ZMod n)
    (h : Nat.gcd (Nat.gcd n m) i.val = Nat.gcd (Nat.gcd n m) j.val) :
    ∃ (u : (ZMod n)ˣ) (b : ℕ), j = u * i + (b * m : ℕ) := by
  sorry -- PLACEHOLDER: ZMod.unitsMap surjectivity (`ZMod.unitsMap_surjective`) + CRT bookkeeping

/-- **MathDB 338887 (Chan–Levine Conjecture 8.3), count form.** -/
theorem chan_levine_conjecture_8_3 (n m : ℕ) [NeZero n] (hn : 3 ≤ n) (hm : 1 ≤ m)
    (i j : ZMod n) (h : Nat.gcd (Nat.gcd n m) i.val = Nat.gcd (Nat.gcd n m) j.val) :
    recCount n m i = recCount n m j := by
  obtain ⟨u, b, rfl⟩ := orbit n m i j h
  have hb : ∀ b : ℕ, ∀ y : ZMod n, recCount n m (y + (b * m : ℕ)) = recCount n m y := by
    intro b
    induction b with
    | zero => intro y; simp
    | succ b ih =>
      intro y
      have : (y + ((b + 1) * m : ℕ) : ZMod n) = (y + (b * m : ℕ)) + (m : ZMod n) := by
        push_cast; ring
      rw [this, recCount_add_m, ih]
  rw [hb, recCount_mul_unit n m hn]

end ChanLevine338887
