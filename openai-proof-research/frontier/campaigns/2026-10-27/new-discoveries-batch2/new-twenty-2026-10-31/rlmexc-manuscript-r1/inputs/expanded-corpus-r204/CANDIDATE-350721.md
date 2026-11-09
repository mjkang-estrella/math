# CANDIDATE 350721: the Alexandersson–Kebede cycle-length positivity conjecture is false for k = 3 and every n ≥ 8

Status: ordinary proof complete; exact finite certificates (n = 8, 9, 10, 11, 12) computed; Lean draft UNCOMPILED (Claude lane: no Lean run). No credit claimed; root and an independent reviewer decide.

## 1. Source and exact statement

* MathDB 350721, "Signed cycle-type restriction polynomiality conjecture" (raw line and hashes in `extracted.json`, `raw/350721.jsonl`).
* Source: P. Alexandersson and F. Getachew Kebede, *An involution on derangements preserving excedances and right-to-left minima*. arXiv:2105.08455 (v1, v2, v3; v3 TeX read, Section "A generalization", around TeX line 2032). Version of record: Australas. J. Combin. 86(3) (2023) 387–413 (PDF fetched from ajc-new.maths.uq.edu.au, sha256 7b39605e…; text at `sources/ajc/ajc_v86_p387.txt`, around line 1659).
* Definitions (source TeX lines 250–270, identical in the VoR):
  * EXCv(π) = {π(j) : π(j) > j};
  * RLMv(π) = {π(i) : π(i) < π(j) for all j > i};
  * inv(π) = number of inversions;
  * x_S = ∏_{s∈S} x_s.
* arXiv v3 / MathDB wording: for 1 ≤ k ≤ n, Σ_{π∈S_n, min type(π) ≥ k} (−1)^{inv π} x_{RLMv(π)} y_{EXCv(π)} ∈ ℕ[x, y].
* **Version of record (Conjecture 5.2.1):** for 2 ≤ k ≤ n,

  F_{n,k} := (−1)^{n−1} Σ_{π∈S_n, min type(π) ≥ k} (−1)^{inv π} x_{RLMv(π)} y_{EXCv(π)} ∈ ℕ[x_1..x_n, y_1..y_n].

  The VoR adds the sign (−1)^{n−1} and the range 2 ≤ k ≤ n, and remarks "the conjecture is not true for k = 1". The case k = 2 is the paper's main theorem.

The arXiv/MathDB wording is trivially false: at k = 1, n = 2 the sum is x_1x_2 − x_1y_2; and for even n and k = n every term is negative. Those failures are zero-credit wording defects that the VoR itself corrects. **This candidate refutes the corrected VoR statement**, which is the source's intended scope. For odd n (for example n = 9) the counterexample also refutes the arXiv/MathDB wording inside 2 ≤ k ≤ n, where no sign issue arises.

## 2. Result

**Theorem.** Let n ≥ 8, R = {1, n−4, n−2, n−1} and E = [n] \ R = {2, …, n−5} ∪ {n−3, n}. The coefficient of x_R y_E in Σ_{π∈S_n, min type(π) ≥ 3} (−1)^{inv π} x_{RLMv} y_{EXCv} equals (−1)^n. Hence the coefficient of x_R y_E in F_{n,3} is −1, so F_{n,3} ∉ ℕ[x, y]. Conjecture 5.2.1 therefore fails for k = 3 and every n ≥ 8.

Computation (exhaustive over S_n) shows the conjecture holds for every 2 ≤ k ≤ n when n ≤ 7 (`outputs/signed-rlm*.json`; n = 4, 5, 6, 7 printed in the lane log). So n = 8 is the first failure, just beyond the range in which the pattern holds.

* At n = 8, F_{8,3} has 256 positive and 2 negative coefficients (`outputs/signed-rlm2-n8.json`).
* At n = 9 the un-normalised sum has 707 positive and 15 negative coefficients (`outputs/signed-rlm3-n9.json`), so the MathDB wording also fails at (9,3).

## 3. Proof

Let π ∈ S_n with EXCv(π) = E and RLMv(π) = R. Every value v is either an excedance value (its position is < v) or not (its position is ≥ v). So:

* (P1) each v ∈ E sits at a position < v;
* (P2) each v ∈ R sits at a position ≥ v.

1. **π(n) = n−1.** Position n is always a right-to-left-minimum position, and RLM values increase from left to right, so π(n) = max R = n−1.
2. **π(i) = i+1 for 1 ≤ i ≤ n−6.** By (P1), value 2 sits at position 1. Inductively, if values 2, …, v−1 occupy positions 1, …, v−2, then value v (≤ n−5, in E) sits at a position < v, and the only free one is v−1.
3. **The tail.** Positions n−5, …, n−1 carry the values {1, n−4, n−3, n−2, n}, under these constraints:
   * by (P1), pos(n−3) ∈ {n−5, n−4};
   * by (P2), pos(n−2) ∈ {n−2, n−1} and pos(n−4) ≥ n−4;
   * n−4 is an RLM, so 1 precedes it;
   * n−2 is an RLM, so if pos(n−2) = n−2 then π(n−1) = n;
   * n−3 is not an RLM, so 1 or n−4 follows it.

   The values 2, …, n−5 are not RLMs because 1 follows them, and n is not an RLM because n−1 follows it. A direct case split (pos(n−2) = n−1 gives 6 words; pos(n−2) = n−2 gives 2) yields exactly the following tails, listed as (π(n−5), …, π(n−1)):

   | name | tail | cycle type | number of cycles |
   |---|---|---|---|
   | A1 | (n−3, 1, n−4, n, n−2) | (n−3, 3) | 2 |
   | A2 | (n−3, 1, n, n−4, n−2) | (n) | 1 |
   | A3 | (n−3, n, 1, n−4, n−2) | (n−4, 4) | 2 |
   | A4 | (1, n−3, n−4, n, n−2) | (n−5, 3, 2) | 3 |
   | A5 | (1, n−3, n, n−4, n−2) | (n−5, 5) | 2 |
   | A6 | (n, n−3, 1, n−4, n−2) | (n) | 1 |
   | B1 | (1, n−3, n−4, n−2, n) | contains a fixed point (n−2) | – |
   | B2 | (n−3, 1, n−4, n−2, n) | contains a fixed point (n−2) | – |

   Conversely, each of these 8 permutations has EXCv = E and RLMv = R (direct check). Cycle types: with c = n−5, the chain 1 → 2 → … → c continues through the tail. For example, A1 has the cycle (1 2 … c, c+2, c+1) of length n−3 and the cycle (c+3, c+5, c+4).
4. **Coefficient.** For n ≥ 8, the permutations with all cycles of length ≥ 3 are A1, A2, A3, A5, A6. Note n−5 ≥ 3 and n−4 ≥ 4, while A4 has a 2-cycle and B1, B2 have fixed points. Since (−1)^{inv π} = sgn π = (−1)^{n − cyc(π)}, the coefficient is (−1)^n(1 − 1 + 1 + 1 − 1) = (−1)^n, and its normalisation is (−1)^{n−1}(−1)^n = −1. ∎

Checks:
* The 8-element set and the coefficient were confirmed by exhaustive enumeration of S_8 and S_9 (`outputs/signed-rlm-cert-n8.json`, `-n9.json`).
* A pruned DFS gives the same 8 permutations and coefficient −1 for n = 10, 11, 12 (`outputs/signed-rlm-family-n1{0,1,2}.json`).
* As a further check, the k = 4 coefficient computed from the table is 0 for n ≥ 9, which matches the computation.

## 4. Prior art and novelty screen (bounded)

* Every arXiv version was read: the conjecture is present in v3 TeX (1 ≤ k ≤ n, no sign) and in the VoR (2 ≤ k ≤ n, sign). It was not withdrawn.
* Citing and nearby work checked, with no resolution found:
  * Pei–Zeng, arXiv:2206.11236 v2 (Adv. Appl. Math. 152), TeX read: it treats only derangement refinements and the "open problems" about d_{n,k}, not cycle-length restrictions;
  * Dey–Mahato, arXiv:2407.21755 (TeX grep);
  * Adams et al., FindStat CSP, arXiv:2402.16251 (bib only);
  * the FPSAC 2022 abstract;
  * web searches (3 queries, logged in SUMMARY).
* Registries: Lean Pool HEAD 01db1d70 tree and projects.yml, Omega HEAD 21d47954 (Problems, D5 and Reg trees), and the OpenAI/math HEAD file list have no derangement, RLM or excedance hits for this source. Omega has only unrelated derangement-ratio files. GitHub repository search "derangements excedances right-to-left minima" returned 0 results. See `outputs/registry-screen.json`.
* The counterexample is not a source formula evaluation and not a modification of a printed example. The source prints only the n = 3 single-cycle polynomial.

## 5. Honest credit risks

* The conjecture is a "further ideas" remark, so significance is moderate. On the other hand, it is in the refereed VoR, it was explicitly corrected there, and the failure is an infinite family beginning just past n = 7.
* A reviewer may ask whether the authors' computer data (not reported) covered n = 8. No such data is printed in either version.
* The MathDB wording is trivially false at k = 1. The candidate must be judged against the VoR statement, which is the source's scope.

## 6. Lean plan (UNCOMPILED; root or a Sol worker compiles)

The endpoint is the negation of the VoR statement, instantiated at n = 8, k = 3:

```lean
-- UNCOMPILED DRAFT (Claude lane; not run).  Mathlib pinned d13f23b7.
import Mathlib

open Equiv Finset

/-- excedance values of a permutation of `Fin n` (1-based statement: π(j) > j  ⇔  (π j).val > j.val) -/
def excv {n : ℕ} (π : Perm (Fin n)) : Finset (Fin n) := univ.filter fun v => (π.symm v).val < v.val
/-- right-to-left minima values -/
def rlmv {n : ℕ} (π : Perm (Fin n)) : Finset (Fin n) :=
  univ.filter fun v => ∀ j : Fin n, (π.symm v) < j → v < π j
/-- all cycles of length ≥ k  (cycleType entries; fixed points counted as length 1) -/
def minCycleGe {n : ℕ} (k : ℕ) (π : Perm (Fin n)) : Prop :=
  (∀ a ∈ π.cycleType, k ≤ a) ∧ (k ≤ 1 ∨ π.support = univ)

/-- the signed sum of the conjecture, as an MvPolynomial over ℤ in variables `Sum.inl i` (x_i) and `Sum.inr i` (y_i). -/
noncomputable def AKsum (n k : ℕ) : MvPolynomial (Fin n ⊕ Fin n) ℤ :=
  ∑ π ∈ univ.filter (fun π : Perm (Fin n) => minCycleGe k π),
    (((Perm.sign π : ℤˣ) : ℤ)) •
      ((∏ i ∈ rlmv π, MvPolynomial.X (Sum.inl i)) * ∏ i ∈ excv π, MvPolynomial.X (Sum.inr i))

/-- VoR Conjecture 5.2.1 (Alexandersson–Kebede, AJC 86(3) 2023). -/
def AKConj : Prop := ∀ n k : ℕ, 2 ≤ k → k ≤ n →
  ∀ m, 0 ≤ ((-1 : ℤ) ^ (n - 1) • AKsum n k).coeff m

theorem AKConj_false : ¬ AKConj := by
  intro h
  -- n = 8, k = 3, m = x_{1,4,6,7} y_{2,3,5,8}  (0-based: x_{0,3,5,6} y_{1,2,4,7})
  have hm := h 8 3 (by norm_num) (by norm_num) monoX8   -- monoX8 : the Finsupp of that monomial
  -- coeff_AKsum_8_3 : (AKsum 8 3).coeff monoX8 = 1   (proof plan: steps 1-4 below; lemma `tail8`
  --   shows the contributing set is {A1,A2,A3,A5,A6} with signs +,-,+,+,-)
  rw [smul_coeff_eq, coeff_AKsum_8_3] at hm   -- names of the planned lemmas, not existing Mathlib lemmas
  norm_num at hm
```

Proof steps for the formal worker:

1. **Monomial lemma.** The monomial x_{rlmv π} y_{excv π} equals m iff rlmv π = R and excv π = E. Use `MvPolynomial.coeff_X_prod`-style lemmas, or `Finsupp` equality of indicator sums, since each variable appears with exponent at most 1.
2. **`sign = (−1)^inv`.** Use `Equiv.Perm.sign` directly. The statement already uses sign, which is equal to (−1)^{inv}, so this needs a bridge lemma `Perm.sign_eq_neg_one_pow_inv` or the Mathlib inversion lemma. Statement fidelity requires this equality.
3. **Characterisation lemma `tail8`.** For π ∈ Perm (Fin 8), rlmv π = R ∧ excv π = E ↔ π ∈ {A1, …, A6, B1, B2}. Recommended proof: either follow §3 (steps 1–3) with `fin_cases` on the 5 tail positions, or use kernel `decide` over the 8 positions restricted by (P1) and (P2). The latter is a small search: π(0), π(1), π(7) are forced, leaving 5 values on 5 slots, at most 120 cases. Avoid `decide` over all 8! = 40320 permutations unless it is measured cheap. No native_decide.
4. **Cycle types.** Compute the cycle types of the 8 explicit permutations (`decide` on `cycleType` of a literal is fine), select A1, A2, A3, A5, A6, and sum their signs: 1.

Semantic bridges to audit:
* 1-based versus 0-based indexing (values and positions shift by one, which leaves the excedance and RLM conditions unchanged);
* `minCycleGe` must count fixed points as cycles of length 1. Mathlib's `cycleType` omits fixed points, hence the support clause;
* the multiset/set reading of EXCv (it is a set, since π is injective).

The general-n theorem (§2) is optional for the endpoint. The single instance n = 8, k = 3 already gives the negation of the VoR conjecture.
