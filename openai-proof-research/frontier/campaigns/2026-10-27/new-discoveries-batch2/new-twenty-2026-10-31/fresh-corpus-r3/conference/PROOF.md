# MathDB 324342: refutation of the conference-matrix MDS conjecture

## Source statement

The source is Etzion, Vardy and Yaakobi, "Coding for the Lee and Manhattan metrics with weighing matrices". The statement is the same in all three versions checked:

- arXiv:1210.5725v1 (21 Oct 2012), Conjecture 5. sha256 `13eb2cac…`
- arXiv:1210.5725v2 (11 Dec 2012), p. 6, Conjecture 5. sha256 `6afe6b96…`
- ISIT 2013 version (Yaakobi's homepage PDF), Conjecture 1. sha256 `923a4a1a…`

The published version, IEEE Trans. IT 59(10):6712–6723 (2013), sits behind a paywall and was not read.

Verbatim (v2):

> **Conjecture 5.** If C is a code of length p + 1 constructed from a generator matrix which is a conference matrix then C is an MDS code of dimension (p+1)/2 and minimum Hamming distance (p+3)/2.
>
> Conjecture 5 was verified to be true up to n = 23, where the conference matrices are based on the Paley's construction from quadratic residues modulo p.

The context is Theorem 4: "If W is a conference matrix of order n = p + 1, where p is a prime, then its rank over Z_p (also F_p) is (p+1)/2." The code C is therefore the Z_p = F_p row space of W.

The definitions come from Section I of the source:

- A weighing matrix W_{n,w} is n×n over {0,1,−1}, has exactly w nonzero entries in each row and each column, and satisfies W·Wᵀ = w·I_n.
- A conference matrix is a weighing matrix with w = n − 1.

The MathDB literal record (chunk 0002, line 3371) matches this, with p prime.

## Result

**Theorem (refutation).** Let p = 19. The 20×20 matrix W below is a conference matrix in the source's sense. It is also skew-symmetric with zero diagonal, so it is a conference matrix in every standard sense. Its F₁₉ row code C has the following properties:

1. dim C = 10 = (p+1)/2. This agrees with the source's Theorem 4.
2. C contains a nonzero word of Hamming weight 9.
3. Exhaustively, the minimum distance d(C) is exactly 9.

So C is a [20,10,9]₁₉ code. Conjecture 5 requires d = (p+3)/2 = 11 and MDS, so both fail.

### The matrix

W = H − I, where H is the Goethals–Seidel skew-Hadamard array built from circulants of order 5:

- A from first row (1, 1, 1, −1, −1). A − I is skew.
- B from (1, 1, 1, 1, −1).
- C from (1, 1, 1, 1, −1).
- D from (1, 1, −1, 1, −1).

The array is

    H = [[A, BR, CR, DR], [−BR, A, DᵀR, −CᵀR], [−CR, −DᵀR, A, BᵀR], [−DR, CᵀR, −BᵀR, A]]

where R is the back-diagonal permutation matrix. The rows are listed in `cex20_certificate_w9.json`, and verbatim in `lean/ConferenceMDSCounterexample.lean`.

The four sequences have periodic autocorrelations summing to 0 at every nonzero shift. Hence HHᵀ = 20I, and therefore WWᵀ = 19I with exactly one zero (the diagonal entry) in each row and column.

### The witness

Take row coefficients x = (5, 7, 13, 9, 0, 15, 14, 2, 8, 18, 0, …, 0) ∈ F₁₉²⁰. Then

    xᵀW ≡ (0,0,0,0,0,15,0,0,10,1,18,0,9,0,18,14,5,15,0,0)  (mod 19)

This word has Hamming weight 9. Checking it by hand is just 20 dot products mod 19.

### Exact parameters (computational, ordinary)

These are from `exact_distance.py` and `exhaustive_mds.py`:

- Of the C(20,10) column 10-subsets of the reduced generator matrix, 8160 are singular.
- Of the C(20,11) 11-subsets, exactly 180 have rank < 10. Each has a 1-dimensional left null space, and every word it produces has weight 9.
- Any word of weight ≤ 8 would vanish on some 12-set, and hence on one of these 180 rank-deficient 11-sets. All words there have weight 9, so no word of weight ≤ 8 exists. Hence d = 9.

This exact value is checked by computer. Lean proves only d ≤ 9, which is all the refutation needs.

## Context theorem: the conjecture is true for Paley matrices (ordinary proof)

This explains why the authors' verification "up to n = 23 … based on Paley's construction" could not detect the failure.

**Setup.** Let p be an odd prime, m = (p−1)/2, χ the Legendre symbol, and ε = χ(−1). The Paley conference matrix is indexed by {∞} ∪ F_p:

- W_{∞∞} = 0
- W_{∞x} = 1
- W_{y∞} = ε
- W_{yx} = χ(x−y)

**Claim.** Its F_p row code is a doubly extended Reed–Solomon code, up to scaling the ∞ column by ε. In particular it is MDS with parameters [p+1, (p+1)/2, (p+3)/2].

**Proof.**

1. By Euler's criterion, χ(a) ≡ a^m (mod p) for every a ∈ F_p, including a = 0.
2. So row y evaluates (x−y)^m at the points x ∈ F_p, and has ∞-entry ε. The monic polynomial (x−y)^m has x^m-coefficient 1.
3. Row ∞ evaluates the constant 1, and has ∞-entry 0. Here m ≥ 1, so the x^m-coefficient of 1 is 0.
4. Scale the ∞ coordinate by ε, which is a monomial equivalence. Every row then lies in E = {(f(x))_{x∈F_p}, [x^m]f) : deg f ≤ m}.
5. dim E = m+1, because m < p makes evaluation injective.
6. Let f ≠ 0 with deg f ≤ m.
   - If [x^m]f ≠ 0, then f has at most m roots, so the weight is at least (p−m) + 1.
   - Otherwise deg f ≤ m−1, so f has at most m−1 roots and the weight is at least p−m+1.
   - Either way the weight is at least m+2 = (p+3)/2. So E is MDS.
7. By the source's Theorem 4, or directly, the row code has dimension (p+1)/2 = dim E. For the direct argument: the binomial coefficients C(m,k) are nonzero mod p, and the Vandermonde system in y shows that the (x−y)^m span all polynomials of degree ≤ m. Hence C(W) = E. ∎

Signed permutations of rows and columns preserve Hamming weights. So every conference matrix equivalent to a Paley matrix gives an MDS code.

**Corollary.** The order-20 counterexample is not equivalent to the Paley matrix of order 20. The conjecture holds exactly on the Paley-equivalent class and fails beyond it, already at the first order (20) where a Goethals–Seidel matrix is available.

**Status of this part.** The Paley statement is a short Reed–Solomon observation and may well be folklore. It is not claimed as a discovery and is not formalized.

## Computational survey (bounded, single process; logs in this directory)

- **Paley p = 5, 7, 11, 13, 17, 19, 23.** Random low-weight search finds nothing below (p+3)/2. Exhaustive check for p = 11 and 19: 0 singular k-subsets.
- **Order 12 (p = 11).** All 432 Goethals–Seidel skew conference matrices give MDS codes (0 singular 6-subsets). See `exhaustive_mds_m3.json`.
- **Order 20 (p = 19).** 12,000 Goethals–Seidel matrices were generated. Of these, 2,767 were tested exhaustively before the run hit its 30-minute background limit; it was deliberately not restarted. All 2,767 are non-MDS, each with exactly 8,160 singular 10-subsets. See `exhaustive_m5.log`, which is a partial log.

## Lean endpoint

- **File:** `lean/ConferenceMDSCounterexample.lean`. It is generated by `gen_lean.py` from `cex20_certificate_w9.json` and `rank_certificate.json`.
- **Definitions in the file:**
  - `IsWeighingMatrix` and `IsConferenceMatrix`, per the source definition.
  - `rowCode p W`: the ZMod p span of the cast rows.
  - `minDistance`: sInf of `hammingDist x y` over distinct codewords x ≠ y.
  - `IsMDS`: d = n − finrank + 1.
  - `Conjecture5 := ∀ p, p.Prime → ∀ W : Matrix (Fin (p+1)) (Fin (p+1)) ℤ, IsConferenceMatrix W → IsMDS (rowCode p W) ∧ finrank (rowCode p W) = (p+1)/2 ∧ minDistance (rowCode p W) = (p+3)/2`.
- **Theorems:**
  - `conjecture5_false : ¬ Conjecture5`.
  - `counterexample : Nat.Prime 19 ∧ IsConferenceMatrix W20 ∧ minDistance (rowCode 19 W20) < (19+3)/2`.
  - `counterexample_full : IsConferenceMatrix W20 ∧ finrank = (19+1)/2 ∧ minDistance ≤ 9 ∧ ¬ IsMDS`.
- **Proof structure:**
  - All finite facts are checked by `decide +kernel`: entries, row and column supports, the Gram identity WWᵀ = 19I, the codeword combination, its weight, the 10×10 minor inverse pair, and the 20 row expressions in terms of rows 0–9.
  - Linear independence comes from `Matrix.linearIndependent_rows_of_isUnit` together with `LinearIndependent.of_comp` along the coordinate projection.
  - The dimension follows from `finrank_span_eq_card`.
- **Toolchain:**
  - Lean 4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52).
  - Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612, prebuilt packages of `campaigns/2026-10-14/formal`, used read-only through `lean/leanpath.txt`.
- **Audit:**
  - `#print axioms` for all three theorems gives [propext, Classical.choice, Quot.sound].
  - Forbidden-token scan is empty (`lean/clean-rebuild/forbidden-scan.txt`).
  - Fresh extracted rebuild with `env -i`: rc 0, about 7.5 s.
  - `leanchecker` replay: rc 0.
  - Hashes are in `lean/clean-rebuild/SHA256SUMS`. Lean source sha256 is `1b355df883f60ef67a9922c12aa209005a460699566c7b139157ad0aca0adf21`.
- **Replay:**

      cd lean/clean-rebuild
      env -i HOME=$HOME PATH=/usr/bin:/bin LEAN_PATH="$(cat ../leanpath.txt)" \
        /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean ConferenceMDSCounterexample.lean

### Fidelity points for the independent reviewer

1. **Reading of "constructed from a generator matrix which is a conference matrix".** We take C to be the F_p row space of the conference matrix W of order p+1. This is the reading forced by the source's Theorem 4 (rank over Z_p) and by the phrase "dimension (p+1)/2". Our W also meets the zero-diagonal, symmetric/skew normal forms.
2. **Universality.** The conjecture is stated for any conference matrix. The Paley-only verification is the authors' evidence, not a hypothesis. Under a Paley-only reading the statement is true by the Reed–Solomon argument above; that is a different and easy claim.
3. **Minimum distance.** It is defined literally as the least distance between distinct codewords. The refutation uses only d ≤ 9 < 11, and is independent of how MDS is defined, because the conjunction also asserts d = (p+3)/2.

## Prior art and registry checks (bounded; receipts in `../registry/receipts.json` and `../sources/receipts.json`)

- **arXiv versions.** v1 and v2 both keep the conjecture. The ISIT'13 version keeps it as Conjecture 1, with the same Paley-only verification remark.
- **Citing papers.** The Semantic Scholar citation list for arXiv:1210.5725 (14 entries) was fetched at about 04:45Z on 2026-11-01. It contains lattice and DNA coding papers; none is about MDS codes from conference matrices. The paper-metadata request returned 429 and was not retried.
- **Web search.** Searches combined conference matrix, MDS, Paley, skew-Hadamard, GF(19), and Etzion–Vardy–Yaakobi. They found related work on self-dual codes from weighing matrices (Arasu–Gulliver 2001; arXiv:1311.2637; skew Hadamard designs over GF(5)), but no resolution of this conjecture.
- **Live MathDB page.** Returned 200 on 2026-11-01, showing 0 solutions and "Nothing recorded yet".
- **openai/math.** Head 4eaee87548250b2682affda7d05d947c05554bae is unchanged. Its recursive tree is truncated at 55,173 entries; no path matched conference, MDS, weighing or Paley-code terms. The local preprints-tree had no relevant manuscript.
- **Palomar revision 651.** The queries `conference+matrix+MDS`, `324342` and `Etzion` each returned a body byte-identical to the earlier `Hoge` receipt (empty entries). The `q` parameter therefore appears to be ignored, so these results are uninformative and not evidence of absence.
- **What this does not show.** Absence from these sources does not certify worldwide priority. Not checked: the IEEE published body, and codes/Hadamard theses not indexed online.

## Limitations and what this is not

- **Significance** has not been reviewed independently. A single finite counterexample to a 2012–2013 conjecture that the authors tested only on Paley matrices may be judged modest. The structural point is that the conjecture holds precisely on Paley-type matrices (by Reed–Solomon) and fails for the first available non-Paley skew matrix.
- **Equivalence classes.** No classification of all order-20 conference-matrix classes was attempted.
