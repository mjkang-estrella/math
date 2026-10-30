# Independent adversarial review: second three outcomes

Reviewed the canonical `outcomes/scaled-tepper`, `outcomes/monochromatic-box`, and `outcomes/shuffle-spectrum` files on October 25, 2026 (America/Los_Angeles). This review owns only this file. No other files, build directories, Git state, or publication state were changed.

## Verdicts

| Outcome | Verdict | Accepted mathematical outcome | Factual boundary |
| --- | --- | --- | --- |
| MathDB354537 — scaled-tepper | **PASS** | Full scaled identity for arbitrary real polynomials and every positive integer step; the certificate additionally permits every nonzero real step. | Elementary consequence of the source's unit-step theorem; no demonstrated new-to-literature priority. |
| MathDB317856 — monochromatic-box | **PASS** | Positive semidefiniteness of the literal source matrix for every nonnegative integer size, with a fully proved general incidence factorization. | **Known-result formalization: the conjecture was resolved in 2017.** It must not be described as a previously open problem solved by this campaign. |
| MathDB369281 — shuffle-spectrum | **PASS** | The four-card position matrix of the actual bottom-drawn top/bottom shuffle does not have eigenvalue 1/16 over the complex numbers, refuting the printed ceiling endpoint. | An index-range correction as printed, not a general corrected spectrum theorem or a priority claim. |

No mathematical FAIL or HOLD finding remains for these three declared outcomes. These are three distinct outcomes, not 24 outcomes merely because there are 24 local declarations. This review does not decide campaign accounting rules or impose any additional novelty requirement.

## Review method and independent compilation

I read `openai-proof-research/AGENTS.md`, `sources/upstream.json`, and the relevant catalogue search results. The recorded OpenAI math revision is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. None of these three proofs needs an additional theorem from that repository. Their external manuscript dependencies are identified below.

For each outcome I read the complete canonical Lean source and `main.tex`, together with `source.json`, `primary-reference.json`, `outcome.json`, and README. I checked the actual primary-source statements, rather than treating the MathDB `open` fields as reliable current research status. I also inspected the relevant installed mathlib definitions/theorems for forward differences, positive semidefiniteness, and eigenvalues.

I independently compiled each complete canonical Lean source through stdin, appending `#check` and `#print axioms` for every local definition and theorem. The invocation used `lean -DwarningAsError=true --stdin`, with `LEAN_PATH` containing only the installed dependency library directories, not the outcome's precompiled modules. There was no local source import, `.olean` output option, or write to an existing build directory. All three invocations exited 0.

- Compiler: Lean 4.34.1, compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`.
- The campaign records mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612` in `pins.json`. I used the installed dependency artifacts; I did not rebuild mathlib or use Git to re-verify dependency revisions.
- All **3 + 9 + 12 = 24** declarations were covered by the independent axiom audit. Every report was contained in `{propext, Classical.choice, Quot.sound}`. `ShuffleSpectrum.shuffle` used only `propext`; the remaining reports used the three standard axioms.
- The canonical files contain no `sorry`, `admit`, new `axiom`, `unsafe` proof, or `native_decide`. The shuffle enumeration uses kernel-checked `decide`.

PDF rendering, visual QA, source bundling, and archive validation remain with the parent as assigned. The PASS verdicts concern mathematical content, formal coverage, and source interpretation, not those unperformed packaging checks.

## 1. Scaled Tepper — PASS

### Source and full statement

[Bayat–Teimoori Faal, arXiv:2205.04237v1](https://arxiv.org/html/2205.04237v1), Theorem 4.3, equation (12), gives the unit-step identity for arbitrary real polynomials. Conjecture 4.5, equation (13), asks for the corresponding positive-integer-step identity. The canonical `source.json` accurately captures those parameters. Its `status: open` is historical source metadata, not evidence of current worldwide priority.

The reviewed result is, for every real polynomial P with degree n and leading coefficient a_n, every real x, and every positive integer l,

    sum_{k=0}^n (-1)^k choose(n,k) P(x-l*k) = a_n * l^n * n!.

The stronger paper theorem allows every nonzero real l. The affine substitution R(t)=P(l*t), evaluated at x/l in the unit-step identity, is valid for precisely that range of l and preserves degree while multiplying the leading coefficient by l^n. Thus the paper's source-based proof is complete.

### Certificate coverage and adversarial checks

All three declarations were read and independently compiled: `sign_identity`, `scaled_identity`, and `mathdb354537` in namespace `ScaledTepper`.

`scaled_identity` quantifies over an actual arbitrary `P : ℝ[X]`, not monomials, bounded-degree examples, or an assumed family of evaluation identities. Its only extra hypothesis is the stated `l ≠ 0`. It composes P with the concrete polynomial `C (-l) * X + C x`; it proves the resulting natural degree and leading coefficient and then applies `Polynomial.fwdDiff_iter_degree_eq_factorial` and `fwdDiff_iter_eq_sum_shift`. The parity lemma has exactly the needed hypothesis k ≤ n, obtained from membership in `range (n+1)`. The two sign cancellations and the equality of the affine evaluations are proved in the file.

`mathdb354537` explicitly quantifies over arbitrary P, natural n and l, real x, `0 < l`, and `P.natDegree = n`. It concludes the literal required sum with `P.leadingCoeff`, l^n, and n!, so no polynomial class or step size is omitted. Natural degree agrees with degree for every nonzero polynomial. The zero polynomial is additionally admitted at natural degree zero and both sides vanish; constants are covered as well. These conventions do not weaken the source claim.

The finite-difference library result is a proved general polynomial theorem, not an axiom asserting this conjecture. No unproved recurrence, degree formula, or scaled identity appears as a theorem premise. The paper and code agree on the stronger nonzero-real-step result. This is a complete source-corollary proof and local formalization; no assertion that this observation is new to the literature is warranted or made in the paper.

## 2. Monochromatic box — PASS, known-result formalization

### Source and prior resolution

[Cooper–Fenner–Purewal, arXiv:0810.3019v1](https://arxiv.org/html/0810.3019v1), Definition 7.2, defines the two binomial-entry matrix; Conjecture 7.4 asks for positive semidefiniteness for r ≥ 3. [Cooper–Forst, arXiv:1704.01644v2](https://arxiv.org/html/1704.01644v2), Corollary 3, already proves positivity for every r ≥ 0. Proposition 4 gives the general intersection-incidence Gram argument. The archived MathDB `open` status is therefore outdated. The canonical paper explicitly acknowledges the 2017 resolution, and `outcome.json` correctly labels this known-result verification. No new solution of an open problem is claimed.

### Full matrix, proof, and formal coverage

All nine declarations were read and independently compiled: `commonFiber`, `boxMatrix`, `incidence`, `feature_count`, `gram_identity`, `boxMatrix_posSemidef`, `sourceMatrix`, `sourceMatrix_eq_boxMatrix`, and `mathdb317856` in namespace `MonochromaticBox`.

The source matrix is represented on the full function type `Fin r → Fin 2`, whose elements are all binary colorings. Its entries are literally the sum of the two choose-two common-color-fiber cardinalities. Changing colors 1,2 to 0,1 and using functions rather than an arbitrary enumeration only relabels the source's indices.

For arbitrary finite ground and color types and any natural k, `incidence` indexes features by a color and a finite subset. It is one exactly when that subset has cardinality k and the coloring is constant with the specified color there. Wrong-size subsets contribute zero. `feature_count` proves the product of two indicators counts exactly the k-subsets of their common fiber; it reduces to `Finset.card_powersetCard`, rather than assuming the counting formula. `gram_identity` sums this identity over colors and proves `M = B * B.conjTranspose`.

The final positivity step is the standard `Matrix.posSemidef_self_mul_conjTranspose`. I checked that mathlib's `PosSemidef` includes Hermitian symmetry and nonnegative quadratic forms, rather than only entrywise positivity. Its finitely supported formulation covers all vectors on these finite index sets. Over ℝ the conjugate transpose is the ordinary transpose. The finite-type and decidable-equality instances are representation requirements, not hidden mathematical restrictions.

`sourceMatrix_eq_boxMatrix` proves the connection back to the literal two-summand matrix. `mathdb317856` then proves its positive semidefiniteness for every r : ℕ; in particular it covers every r ≥ 3. The general statement also handles k=0, k larger than the ground-set size, and empty finite types without exceptional assumptions. The paper proves the same general claim. No spectral formula from either source is needed or asserted as part of this outcome.

## 3. Shuffle spectrum — PASS, printed endpoint only

### Source interpretation

[Clay, arXiv:2507.10294v1](https://arxiv.org/html/2507.10294v1), Definition 2.2, specifies bottom-drawn cards with fair top/bottom insertion. Theorem 1.1 gives

    M[i,j] = (choose(i-1,j-1) + choose(i-1,n-j)) / 2^i

for one-based indices. Conjecture 2 prints nonzero eigenvalues 2^(-2i) through i=ceil((n-1)/2), inclusive. At n=4 this is ceil(3/2)=2, so it explicitly predicts 1/16. The note targets that text, irrespective of other endpoint variants or intended corrections.

### Actual process, all choices, and exact matrix

All twelve declarations were read and independently compiled: `shuffle`, `countMatrix`, `counts_table`, `enumeratedProbability`, `positionMatrix`, `four_cards`, `enumeration_matches_formula`, `no_sixteenth_vector`, `no_sixteenth_eigenvalue`, `no_sixteenth_in_actual_shuffle`, `SpectrumConjecture`, and `not_spectrum_conjecture` in namespace `ShuffleSpectrum`.

`shuffle` processes the fixed list `[3,2,1,0]`, corresponding to drawing cards 4,3,2,1 from the bottom. A true choice prepends the card and a false choice appends it. Thus this is the stated physical model. `countMatrix` counts final card positions over **all functions `Fin 4 → Bool`**, with no sampled outcomes or filtering of the experiment itself. I independently checked in Lean that this function space has cardinality 16. The first placement is on an empty pile, so its two choices give the same deck; retaining both choices correctly preserves their equal probability.

I also independently enumerated all sixteen bit patterns using Python integer counts. The resulting count matrix was exactly

    [[8,0,0,8], [4,4,4,4], [2,6,6,2], [2,6,6,2]].

Division by 16 is the fair-coin probability matrix. `counts_table` proves these counts by kernel reduction. `four_cards` independently evaluates the zero-based binomial formula, and `enumeration_matches_formula` proves equality of the enumerated probability matrix and that formula. The zero-based conversion is exact: the second lower binomial index is `n-1-j`, and the denominator exponent is `i+1`. The result is not about an unrelated hand-selected matrix or a surrogate transition model.

### Eigenvalue exclusion and completeness

`no_sixteenth_vector` proves that every **complex** vector satisfying Mv=(1/16)v is zero. The four component equations are derived from that equality; none is assumed independently. Subtracting the last two gives c=d. Eliminating b then gives 2a+3d=0, while the first equation is 7a+8d=0; these force d=0 and hence all four coordinates vanish. The paper's equivalent calculation is correct. As a separate exact-arithmetic check, elimination gives `det(16M-I)=45`, which also excludes 1/16 over ℂ.

`no_sixteenth_eigenvalue` uses mathlib's `HasEigenvalue` and extracts a nonzero eigenvector, contradicting the proved zero-vector conclusion. `no_sixteenth_in_actual_shuffle` transfers the exclusion to the enumerated process. No diagonalizability, spectral list, characteristic-polynomial factorization, or eigenvalue assertion is assumed.

`SpectrumConjecture` expresses equality of the nonzero-eigenvalue set with the printed list, using the natural-number bound `n/2`. For positive integer n, this is exactly ceil((n-1)/2). I additionally compiled an exact real-ceiling check at n=4. The formalization restricts the universal statement to n ≥ 3; refuting it at n=4 also refutes an unrestricted source statement. `not_spectrum_conjecture` explicitly chooses i=2 and n=4, obtains the predicted eigenvalue, and contradicts its exclusion. Thus the conclusion does not depend on proving an endpoint-translation lemma for arbitrary n.

The complete declared outcome is this concrete counterexample. Neither code nor paper proves a replacement endpoint or the full spectrum for general n, and neither is needed to refute the printed statement. The neighboring quadratic-eigenvector conjecture is outside this result.

## Exact reviewed hashes

The following SHA-256 values are for the canonical files, not the copies in `build/`:

| Outcome | File | SHA-256 |
| --- | --- | --- |
| scaled-tepper | `formal/Tepper.lean` | `c74b87b6b92867aa27949b0a112a67e2387aca9234dc75bb509d3cb2b481eb64` |
| scaled-tepper | `main.tex` | `ea1cfbc399ce9ff98a1ea10e77ea0163a15cc1cc861c14bbc3e8c73a0eaea13a` |
| monochromatic-box | `formal/Monochromatic.lean` | `4a6f81ccf53f2c493645d5775230e688772f7ea5679feeedf21cdef5c04891d2` |
| monochromatic-box | `main.tex` | `1a529779fbb244f22966202ba0ffb9a151cf07210b6cc1904e23a002b7f4f6d8` |
| shuffle-spectrum | `formal/ShuffleSpectrum.lean` | `1defdfad48060b2d617af37e254be61c1df970e67b023d40348d17aaff92c01a` |
| shuffle-spectrum | `main.tex` | `94d66902c97811c7a2735a9fedc389232a5706e3fb69415ac28e64b03e35dcba` |

I independently hashed the available primary HTML snapshots and confirmed agreement with the canonical `primary-reference.json` records:

| Primary source | Snapshot SHA-256 |
| --- | --- |
| `2205.04237v1.html` | `041d3578f6252f82866bf1d84cac804f799cb28c0870a7d57888ebbe417afec2` |
| `0810.3019v1.html` | `9003ed6dc9b765d10881b4dc1b40315a2af2875d9d02e5a1919caac629365e0f` |
| `1704.01644v2.html` | `fb0ceebfc87073bc3eebf85fc00554a39b34d0b0e46ea7a71a4485986cc546be` |
| shuffle `build/primary.html` (`2507.10294v1`) | `711998f7ee7147d3074a2eb91e7d5b7561aa59af9055bf42812c0ce1358ce147` |

The first three snapshots reside in the sibling `twenty-proof-discrete-lane` source directories. I also read the version-specific arXiv pages linked above to verify the named statements. This review does not infer provenance or literature novelty merely from a matching content hash.
