# Preliminary adversarial review — parent-euler-turan (Sokal 1804.04498v3 Conjecture 3.3 / MathDB 338918)

Reviewer: pi-euler-turan-preliminary-review (independent, solo). Scope: preliminary
source/math/bounded-novelty/substantive-eligibility review of the FROZEN state at commit
`2ca1e4b0ba` (25 hashed files). This is NOT a final-paper or full-formal review; no
credit, tally, or count changes made. Accepted campaign tally 23/30 and candidate
credit 0 are unchanged by this review.

## Frozen-state integrity

- All 25 hashes in `preliminary-review-hashes.json` verified on my own copy
  (recomputed sha256, 25/25 match) AND against the frozen git objects of `2ca1e4b0ba`
  (PROOF.md and STATUS.md spot-checked byte-identical).
- **Post-freeze drift observed:** between 04:41 and 04:50 (after the 04:39:51 freeze
  commit) the parent added 7 NEW untracked files to `parent-euler-turan/formal/`
  (AffineDerivative.lean, BilateralSeries.lean, CombinedError.lean, CotBoundary.lean,
  EulerCoefficient.lean, EulerGenerator.lean, OddError.lean, plus .oleans). These are
  OUTSIDE the frozen hash manifest, OUTSIDE my lane, and were NOT reviewed. The review
  below covers only the frozen 3-module / 18-declaration state. If the parent intends
  these as part of the candidate, they need a new freeze and a fresh review.

## GATE VERDICTS

### SOURCE — PASS (with one recorded access limit)

- Fresh fetch of arXiv 1804.04498: v3 is latest (13 Sep 2018); journal ref
  Expositiones Mathematicae 38, 1–26 (2020). Fresh arXiv v3 PDF, the UCL accepted copy
  (`discovery.ucl.ac.uk/10059424/1/1804.04498v3.pdf`), and the parent's saved PDF are
  byte-identical (sha256 `e9dac140f379feff11dcf345df7dda2eb8c8d33db6f5e66d38a04463ffc34632`).
- I personally rendered p14 to PNG (`review-evidence/my-p14-14.png`, 150 dpi) and
  visually inspected it: **Conjecture 3.3** reads verbatim "Define Ên = En/n!. Then
  for all n ≥ 0 and j, k ≥ 1, we have (−1)^{n−1}[Ên Ên+j+k − Ên+j Ên+k] > 0. (3.14)"
  followed by "I do not know how to prove (3.14), but I have verified it for n, j, k ≤ 900."
  The source's exponent n−1 ≡ n+1 (mod 2); the campaign's (−1)^{n+1} is the same sign.
- Euler numbers are defined in the source by sec t + tan t = Σ En t^n/n! (eq. 1.3),
  sequence 1,1,1,2,5,16,… (A000111, all positive). The campaign's normalization
  a_n = 2(2/π)^{n+1} b_n matches the source's partial-fraction bodies (3.3) and (3.4)
  exactly; I re-derived both directions symbolically:
  - (3.3): E_{2m}/(2m)! = 2^{2m+2}π^{−(2m+1)} β(2m+1) = 2(2/π)^{2m+1} β(2m+1). ✓
  - (3.4): E_{2m+1}/(2m+1)! = 2^{2m+3}π^{−(2m+2)} λ(2m+2) = 2(2/π)^{2m+2} λ(2m+2). ✓
  Both are classical (source credits them to [5, p. 11]); correctly credited, not counted.
- Conditional n=0 pairing checked: the source's symmetric Σ_{k=−N}^{N} (3.3) at n=0
  equals exactly 2× the ordered half-line alternating series (summands pair
  k ↔ −k−1 identically for every N), which converges by Leibniz to β(1)=π/4; the
  paired c_0 = 1 − π/4 ≈ 0.2140 series is a positive-term series. No ambiguity.
- Limit: the typeset published Expo. Math. 38(2020) 1–26 body was not separately read
  (ScienceDirect 403). The UCL accepted copy (byte-identical to arXiv v3) is the
  operative text; footnotes 9–10 of v3 are visible in the PDF. Low residual risk.

### MATH — PASS (independently re-derived; finite checks are not the proof)

I verified every step myself, not by trusting the parent's text:

1. Normalization: confirmed numerically at 60-digit Decimal precision for n=0..11
   (residuals at n=0,1 equal exactly the 20,000-term series truncation tails; π entered
   at 16 digits). Also cross-checked exact values a_2=1/2, a_3=1/3, a_4=5/24.
2. c_n definitions: for even n, c_n = Σ_{r≥0}[(4r+3)^{−s} − (4r+5)^{−s}] = 1 − β(s)
   (s=n+1); for odd n, c_n = λ(s) − 1. Both verified.
3. 0 < c_n < 1 and contraction: verified with rigorous rational tail bounds for
   n = 0..10 (c < 1 and c_{n+2} ≤ c_n/3 both hold with tails). Odd case is ≤ /9
   (termwise (2r+3)^{−2}), even case uses the exact identity.
4. Exact paired identity: I re-derived
   (A²+AB+B²)(A^s−B^s) − (A^{s+2}−B^{s+2}) = AB(A+B)(A^{s−1}−B^{s−1}) by hand AND
   symbolically in sympy for s=1..6 (residual 0); the termwise bound
   A^{s+2}−B^{s+2} ≤ (A²+AB+B²)(A^s−B^s) holds with the expansion coefficient argument;
   A²+AB+B² ≤ 1/3 for A,B ≤ 1/3; s=1 (n=0) gives equality — contraction holds at n=0.
5. Sign criterion: I independently conjugated by ε_n = (−1)^{n+1} and obtained exactly
   the parent's L + ε_n(−1)^{j+k}X with L = a + (−1)^{j+k}d − (−1)^j b − (−1)^k c.
   All four parity cases re-verified by hand:
   - odd/odd: L−X = a(1−d)+d+b+c+bc > 0; L+X = b(1−c)+c+a+d+ad > 0. ✓
   - even/even: b,c ≤ a/3; L−X ≥ a/3 > 0; L+X ≥ a/3 − a²/9 > 0 (a<1). ✓
   - mixed (j odd, k even; symmetric): c ≤ a/3, d ≤ b/3; L±X ≥ (2/3)(a+b) − ab/3 > 0
     since ab < a. ✓
   Only 0 < c < 1 and the even-shift contraction are used; the parity of j,k ≥ 1
   guarantees the needed +2 shifts. Correct.
6. Independent exact-rational finite check: I constructed a_n from the ODE
   E' = (1+E²)/2 (NOT the parent's combinatorial recurrence — independent generator)
   and found 0 violations in n ≤ 24, j,k ≤ 24 (14,400 checks). This is evidence only;
   the proof is the analytic argument above.
7. Frozen Lean (18 declarations: AlternatingCriterion 2, ErrorCriterion 7,
   ErrorSeries 9): statements match my derivation lemma-for-lemdir; I found no
   `sorry`/`axiom` in the frozen sources. The telescoping trick in
   `evenError_summable_bound` (evenTerm k ≤ u k − u (k+1) with u k = (4k+3)^{−(n+1)})
   is valid ((4k+5)^{−s} ≥ (4k+7)^{−s}).
   **I could NOT recompile:** no lean/elan/lake in my environment. The .oleans exist
   and the parent reports a clean compile; compilation re-verification is an
   open obligation for the final review.

Known special cases correctly uncredited: even n with j,k even = strict log-concavity
of the even subsequence (Pólya frequency, source p14 explicitly cites the strictly
positive minors result); odd n with j,k odd = strict log-convexity of the odd
subsequence (Stieltjes moment, source eq. 3.5). The mixed-parity cases are the new
content and are covered.

### BOUNDED NOVELTY — PASS (bounded; no subsuming theorem or earlier resolution found)

Read actual bodies:
- Han 1906.00103 (Hankel CFs/determinants of Euler numbers): Theorems 1.1/1.2 concern
  the UNNORMALIZED mixed sequence (E_0,E_1,…) with H_{4k+2}=0; no normalized-minor
  sign theorem. Does not subsume.
- Han 2607.08279 (dilated Hankel): §7 Proposition 7.1 gives dilated Hankel determinant
  product formulas for UNNORMALIZED moment families with EGF 1/cos^{s+1} + ∫dy/cos^{t+1};
  different objects (moments, dilated determinant det(a_{2i+j}) with columns from 0),
  not the arbitrary-offset 2×2 minors of Ên = En/n!. Only §7, abstract, and intro read;
  the other ~26 sections were not read (limit; scope of the paper does not intersect
  the conjecture's statement).
- Sokal 2206.15434: continued-fraction algorithm; Euler/secant appear only as
  classical examples (Example 9.10, J-fraction of secant power polynomials). No
  conjecture-3.3 content.
- Pan–Zeng 1910.01747: (p,q)-Eulerian polynomials; cites 1804.04498 in the bibliography
  only; its "open problem of Han" is the γ_{n,k}(p,q)/(p+q)^k divisibility problem,
  unrelated.

12 OpenAlex citers reviewed at title/venue level (citers.json); none targets this
inequality. Public registries: count-ex-machina (github.com/suvrit/count-ex-machina,
arXiv 2608.29595) lists 14 counterexample cases — none concerns Euler numbers or this
conjecture; trureturing atlas is a module-dependency library with no 338918/Euler entry.
Targeted web searches on the exact statement found no earlier proof, disproof, or
subsuming theorem. MathDB record 338918 live-fetched: status open, all activity arrays
empty, lean_formalization_count 0 — treated as a pointer, NOT as a novelty certificate.

Limits: MathSciNet/zbMATH unavailable; Olteanu 2021 (Symmetry 13:986) full body 403-
unread (title/venue/abstract suggest a general Markov moment-problem survey; residual
risk low but nonzero); JCTA 2025 citer body unread; remaining 8 citers' bodies unread;
published-typeset Expo. Math. body unread. No worldwide-priority claim is made or
certifiable.

### SUBSTANTIVE ELIGIBILITY — PASS (preliminary)

The result is a complete resolution of the exact source question (all n ≥ 0, j,k ≥ 1),
not a special case, reformalization, or normalization fix. The proof is elementary but
complete and correct; the source explicitly poses it as open beyond n,j,k ≤ 900
finite checks. Under the ledger counting standard ("substantive new mathematical
result addressing an exact unresolved source question; exclude special-case counts and
wording/normalization fixes") this qualifies for PRELIMINARY eligibility. Whether the
elementary character of the argument affects acceptance is a parent-policy call, not
mine; the standard as written does not require difficulty.

### FORMAL — NOT ASSESSED (explicitly partial)

No literal Euler-object bridge exists in the frozen state: `corrected` is an abstract
sequence 1 + (−1)^{n+1}c_n with hypotheses (0<c<1, c_{n+2} ≤ c_n/3) that are never
instantiated from actual Euler numbers; the odd-error series is not formalized; the
source normalization (3.3)/(3.4) is not proved in Lean. The parent's STATUS.md states
this accurately. NO full formal PASS is claimed or implied by this review. The
post-freeze files suggest the parent is building the bridge (EulerGenerator,
CotBoundary, EulerCoefficient); these are unreviewed and unhashed.

## Decisive findings

1. Mathematical argument is correct (all steps independently re-derived). No errors found.
2. Source fidelity confirmed by direct visual inspection of p14 and byte-identical
   fresh arXiv/UCL fetches.
3. No prior resolution or subsuming theorem found within the bounded screen.
4. Post-freeze drift: 7 new untracked formal files appeared in the parent lane during
   this review; they are outside the frozen manifest and this review's scope.
5. Lean compilation could not be independently re-verified (no toolchain here).

## Recommended next steps (for the parent, not binding)

- Re-freeze if the new formal modules are to be part of the candidate; then a full
  five-gate review including literal Euler-bridge Lean with no new axioms, odd-error
  series, and an axiom audit is required before any acceptance.
- Read (or record inaccessibility of) the published Expo. Math. typeset body,
  Olteanu 2021, and the JCTA 2025 citer body before any acceptance decision.
