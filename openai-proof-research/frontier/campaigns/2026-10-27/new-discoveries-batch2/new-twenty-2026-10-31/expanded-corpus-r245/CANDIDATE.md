# Candidate from expanded-corpus-r245 (Claude): MathDB 339077

**Status:** candidate only, with **high exclusion risk** (see "Credit risk" below). Nothing here is self-accepted. No Lean was run in this lane; the Lean below is an UNCOMPILED plan.

## 1. Target and provenance

- MathDB 339077, "The three-shifted q-Motzkin determinant conjecture". Raw line: `raw/338589…339171.jsonl` (`raw/339077.jsonl`), chunk `mathdb-normalized-chunk-0005.jsonl`, line 3488. Hashes: chunk sha256 `026158d6…be7c`, raw sha256 `d0c9447f…2857`, statement sha256 `3f91f3d9…bbe7` (all in `extracted.json`).
- Source: Se-jin Oh and Travis Scrimshaw, *Identities from representation theory*, arXiv:1805.00113 (v1 is the only arXiv version; Discrete Math. 342(9) (2019) 2493–2541). Appendix A, Conjecture A.3. Cached PDF `sources/source-077.body` (receipt `source-077.receipt.json`) and text `sources/source-077.txt`, offset about 224 700.
- The q-Motzkin numbers (Cigler's): M_0 = 1, M_{n+1} = M_n + Σ_{r=0}^{n-1} q^{r+1} M_r M_{n−r−1}, and t_n(q) = Σ_{k=0}^{⌊n/3⌋} q^{3k}.

**Printed A.3** (both in the source and in MathDB): "det[M_{i+j+3}(q)]_{i,j=0}^{n−1} = (−1)^{⌊n/3⌋} q^{c_n} f_n(q) for some c_n ∈ Z≥0 and g_n(q) ∈ Z≥0[q]. Moreover, if n ≡ 1 (mod 3) then g_n = (q+1)^2 t_n^2, and if n ≡ 2 (mod 3) then t_n divides g_n."

The printed text is internally garbled. f_n is inherited from Conjecture A.2, and g_n is never tied to the determinant. Two readings:

- **(L) Literal, with A.2's f_n.** This fails trivially at n = 1: det[M_3] = M_3 = (1+q)^2, while f_1 = (q+1). This is an inherited-notation misprint and is **not** claimed as a result.
- **(I) Intended:** det = (−1)^{⌊n/3⌋} q^{c_n} g_n(q) with g_n ∈ Z≥0[q], plus the two "Moreover" clauses about g_n. This is the reading the candidate refutes.

## 2. Result: the intended Conjecture A.3 is false at n = 5

**Theorem.** There are no c ∈ ℕ, g ∈ ℤ[q] and sign ε ∈ {±1} with det[M_{i+j+3}(q)]_{i,j=0}^{4} = ε q^c g(q) and t_5(q) = 1 + q^3 dividing g(q). In particular reading (I) fails at n = 5.

**Proof.** Let ev: ℤ[q] → ℤ be evaluation at q = −1. This is a ring homomorphism, so it commutes with the recursion and with determinants. Evaluating the recursion at q = −1 gives the integers

M_k(−1), k = 0..15: 1, 1, 0, 0, 1, 1, −1, −1, 3, 3, −6, −6, 15, 15, −36, −36.

Hence ev(det H_5) is the determinant of

```
[[ 0,  1,  1, -1, -1],
 [ 1,  1, -1, -1,  3],
 [ 1, -1, -1,  3,  3],
 [-1, -1,  3,  3, -6],
 [-1,  3,  3, -6, -6]]
```

which equals **2**. This was computed by exact rational elimination and, independently, by the 120-term Leibniz expansion (`claude-scripts/qmotz_minus1.py`). If det H_5 = ε q^c t_5 h, then ev(det H_5) = ε (−1)^c t_5(−1) h(−1) = 0, because t_5(−1) = 1 + (−1)^3 = 0. That contradicts 2. ∎

The proof needs no positivity, no sign convention and no particular value of c, so it refutes every reading in which g_n is the cofactor of det H_n. The same evaluation gives det H_11(−1) = 4 with t_11(−1) = 0, so n = 11 fails too.

**Exact data, diagnostic** (`claude-scripts/qmotz.py`, `outputs/claude-qmotz/qmotz-s3.json`). Determinants were computed by fraction-free Bareiss over ℤ[q] for n ≤ 7, and for 1 ≤ n ≤ 30 through the block identity det H^(r)_n = q^{n(n−1)(n−2)/3 + n(n−1)/2} det(B^r)_{[0,n)}, with B = K·diag(q^h) and K the 0/1 tridiagonal matrix. That identity was proved in `lanes/root-qmotzkin-adoption-r1/ADOPTION.md`, and the two methods agree for n ≤ 7. In addition:

- The shift-2, n = 3 value q^11(1 + q^2 + q^3) of the Omega A.2 certificate is reproduced, and M_k(1) = 1, 1, 2, 4, 9, 21, 51 (Motzkin numbers).
- For n = 5: det H_5 = −q^62 (1 + 2q + 2q^3 + 2q^4 + q^6 + 2q^7). The sign is (−1)^1 and the coefficients are nonnegative, but 1 + q^3 does not divide the cofactor: its remainder is 2q.
- For all n ≤ 30 the sign (−1)^{⌊n/3⌋} and the nonnegativity of g_n hold, and the n ≡ 1 clause g_n = (q+1)^2 t_n^2 holds.
- The n ≡ 2 clause holds exactly for n ≡ 2 (mod 6), i.e. n = 2, 8, 14, 20, 26, and fails for n ≡ 5 (mod 6), i.e. n = 5, 11, 17, 23, 29.

**Conjectural complete evaluation** (fitted, verified for n ≤ 27 by `claude-scripts/qmotz_closed.py`; not proved). Write x = q^3, t_m(x) = Σ_{k≤m} x^k, E_m(x) = Σ_{k≤⌊m/2⌋} x^{2k} and F_m(x) = Σ_{j≤2⌈m/2⌉} x^j. Then g_{3m+1} = (1+q)^2 t_m(x)^2 (the source's own claim), g_{3m+2} = t_m(x)^2 + 2q E_m(x) F_m(x), and g_{3m} = t_m(x)^2 + 2q^2 E_{m−1}(x) F_{m−1}(x). For odd m, t_m contains the factor (1+x) but E_m F_m does not vanish at x = −1. This explains the n ≡ 5 (mod 6) failures. A proof of this evaluation is the **remaining lemma** that would upgrade the finite refutation to a full resolution: sign, positivity, the n ≡ 1 formula and the exact divisibility pattern.

## 3. Prior-art screen (bounded)

- The Omega registry has `D5/S0/Certificates/OhScrimshawQMotzkinHankelRefutation.lean`, which refutes **A.2** (MathDB 339076) at n = 3 by evaluation at q = 1. It does not mention A.3. The current Omega `D5/S0/Certificates` listing at HEAD 1a9b3302 shows no A.3 file.
- Nothing relevant was found in Lean Pool (HEAD 01db1d70), the OpenAI/math preprint listing (HEAD 4eaee875), or GitHub repository search (three queries, all 0 results). See `outputs/registry-screen.json`.
- Literature checked:
  - Cigler–Krattenthaler arXiv:2003.01676: no mention of Oh–Scrimshaw (text in `sources/c-pdf-2003.01676.txt`).
  - Cigler arXiv:2204.09910: lossy text extraction found no mention.
  - Web searches (receipts not storable) found no erratum or later treatment.
- **Not checked:** the published Discrete Math. version. ScienceDirect is denied, so whether the journal version corrected A.3 is unknown, and this is a material gap.
- Campaign history: 339078 (A.4) has an uncredited prior lane (`lanes/pi-qmotzkin-even-positivity-r1`, root adoption `lanes/root-qmotzkin-adoption-r1`). 339076 was excluded by the Omega refutation. No prior campaign note on 339077 was found (`history-matches.txt`).

## 4. Credit risk (honest assessment)

- This refutes a numerically motivated clause at **its first nontrivial instance**: n = 2 is vacuous because t_2 = 1. The printed statement is already garbled (f_n versus g_n), and the sibling A.2 failed at n = 3. Root may well rule this a **smallest-parameter or misprint correction** (precedents 371607, 373480), or a source-data issue, which earns zero credit.
- What goes beyond a typo is the exact divisibility pattern, failing for every n ≡ 5 (mod 6) through n = 29, and the conjectural closed form. But the closed form is **unproved**.
- Lean cost is very low (one 5×5 integer determinant).

## 5. UNCOMPILED Lean plan (literal endpoint for reading (I))

```lean
import Mathlib
open Polynomial

/-- Cigler's q-Motzkin numbers, exactly as printed (same as the Omega A.2 file). -/
def qMotzkin {R : Type*} [CommRing R] (q : R) : ℕ → R
  | 0 => 1
  | n + 1 => qMotzkin q n +
      ∑ k : Fin n, q ^ (k.val + 1) * qMotzkin q k.val * qMotzkin q (n - k.val - 1)
decreasing_by all_goals omega

noncomputable def tPoly (n : ℕ) : ℤ[X] := ∑ k ∈ Finset.range (n / 3 + 1), X ^ (3 * k)

noncomputable def hankel3 (n : ℕ) : ℤ[X] :=
  Matrix.det (Matrix.of fun i j : Fin n => qMotzkin (X : ℤ[X]) (i.val + j.val + 3))

/-- Intended reading of Oh–Scrimshaw Conjecture A.3 (MathDB 339077). -/
def claimA3 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ c : ℕ, ∃ g : ℤ[X], (∀ i, 0 ≤ g.coeff i) ∧
    hankel3 n = (-1) ^ (n / 3) * X ^ c * g ∧
    (n % 3 = 1 → g = (X + 1) ^ 2 * tPoly n ^ 2) ∧
    (n % 3 = 2 → tPoly n ∣ g)

theorem not_claimA3 : ¬ claimA3 := by
  intro h
  obtain ⟨c, g, -, hdet, -, hdiv⟩ := h 5 (by norm_num)
  obtain ⟨u, rfl⟩ := hdiv (by norm_num)
  -- (1) eval at -1 commutes with the recursion: strong induction, as `hmap` in the Omega file
  have hmap : ∀ n, (qMotzkin (X : ℤ[X]) n).eval (-1) = qMotzkin (-1 : ℤ) n := by sorry -- PLAN
  -- (2) eval commutes with det: RingHom.map_det (Polynomial.evalRingHom (-1))
  have hev : (hankel3 5).eval (-1) =
      Matrix.det (Matrix.of fun i j : Fin 5 => qMotzkin (-1 : ℤ) (i.val + j.val + 3)) := by sorry -- PLAN
  -- (3) the integer values M_3..M_11 at -1 and the 5x5 determinant = 2
  --     (norm_num [qMotzkin, Fin.sum_univ_succ] then Matrix.det_succ_row_zero expansion, or decide)
  have hval : Matrix.det (Matrix.of fun i j : Fin 5 => qMotzkin (-1 : ℤ) (i.val + j.val + 3)) = 2 := by
    sorry -- PLAN
  -- (4) tPoly 5 evaluates to 1 + (-1)^3 = 0 at -1
  have ht : (tPoly 5).eval (-1) = 0 := by simp [tPoly, Finset.sum_range_succ]; norm_num
  have := congrArg (Polynomial.eval (-1 : ℤ)) hdet
  simp [Polynomial.eval_mul, ht] at this
  rw [hev, hval] at this
  norm_num at this
```

The `sorry` placeholders mark the plan steps for the Sol worker; they are **not** part of any endpoint. The sorry-free target is `not_claimA3`. Statement-correspondence notes for review:

1. The quantifier on c and g is existential per n. The "Moreover" clauses are conjoined, since the source asserts them together.
2. The literal reading (L) can be stated separately with A.2's `fPrinted` and refuted at n = 1 by evaluation at q = 1 (4 versus 2·1). This is offered only as a fidelity footnote.
3. The refutation uses only the n ≡ 2 clause, so it is insensitive to the sign convention and to the positivity clause.
