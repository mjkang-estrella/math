# Independent review of i05-crossfield, round 2

Date: 2026-10-08. Candidate: [i05-crossfield.md](../iterations/i05-crossfield.md). This is a fresh independent proof and novelty/significance review, not a continuation of the discovery task. No accepted result number is assigned.

**Mathematics: PASS. Novelty: exact literature priority UNVERIFIED. Nonroutine/substantial-contribution gate: DEMOTE. Corpus-enabled objective: NOT MET.**

Theorem G, including all integer lengths, arbitrary fixed integer polynomial maps, equal degrees, coincident maps, nonmixing Gaussian actions, and inputs in `L^{2k}`, follows from the displayed argument. The finite-degree weighted `L²` variation estimate and its stated partial-pairing factor are valid. Section 7's optional limit identification also passes. No additional mathematical lemma or stronger hypothesis is needed to close these claims.

The important new review finding is **positive prior-art evidence for the main mechanism**, not a missing search hit. Gaussian decoupling for arbitrary Banach-valued homogeneous chaos is already an explicit classical theorem; taking the target Banach space to be a finite variation sequence space gives the candidate's central Wick estimate directly. I give the specialization below. Wick contraction expansion and the spectral treatment of contractions then recover the ordinary-product estimate. Consequently I recommend retaining this as a correct classical-decoupling application/research record, **not counting it as the requested second substantial contribution**. This recommendation does not assert that a prior paper explicitly states the full ergodic theorem in exactly these quantifiers.

## 1. Scope, integrity, and actual sources

I read `AGENTS.md`, `sources/upstream.json`, `sources/CONTENTS.md`, the complete nontruncated `sources/preprints-tree.json`, `frontier/iterations/README.md`, and the candidate. The accepted OpenAI revision is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Its statements are premises here; I do not audit their truth.

All 107 discovery manuscript files match their recorded SHA-256 values and Git blob hashes, and all 107 blobs match the complete pinned tree. I additionally retrieved six dynamics contract files independently from immutable raw URLs; all six match the discovery copies. This is integrity evidence, not a proof review of 107 manuscripts. The records are [upstream-verification.json](../sources/i05_crossfield_r2/upstream-verification.json) and [manifest.json](../sources/i05_crossfield_r2/manifest.json). Initial input hashes are in [inputs.json](../sources/i05_crossfield_r2/inputs.json). The shared iteration README changed during the review; I re-read its current objective and cross-field status. The candidate and all other hashed inputs remained unchanged. This concurrent index update does not change the verdict.

Principal primary literature actually retrieved and read:

- **Mirek–Trojan**, [arXiv:1405.5566v1](https://arxiv.org/pdf/1405.5566v1), pp. 1–3, especially Theorem B and the definition (1.1). SHA-256 `70ee971cb08478c1ed60908c5b0c11247452ad454d0201e464f933ddd7c8952a`.
- **Maas**, [arXiv:0801.2899v2](https://arxiv.org/pdf/0801.2899v2), §2.1, Theorem 2.1 and Remark 2.2. SHA-256 `0aba2eadd5b96428a43fe661f392b6db70438db0b2f1f8bd49b25fbf42769cec`. Also checked the [author-hosted manuscript](https://www.janmaas.org/papers/MallCalc.pdf), with the same theorem, SHA-256 `05b26938faa94d87c441dc16fb6f71e563fe203fb87b9476962e1668b1bd88b0`. The author version has the clear multiplicity-factorial notation. The relevant decoupling result applies to **arbitrary Banach spaces**, not only UMD spaces.
- **de la Peña–Montgomery-Smith–Szulga**, [arXiv:math/9406214v2](https://arxiv.org/pdf/math/9406214v2), §§1–2, including (1.4), (2.1), and Theorem 2.1. This documents the older conditional-expectation/decoupling mechanism. Its diagonal-free hypothesis must be respected; for the general Wick tensors I use Maas's symmetric Hermite-chaos statement instead.
- **de la Rue**, [2004 HDR](https://delarue.perso.math.cnrs.fr/Publis/PDF/introhdr.pdf), §§2.2, 4.1–4.2, 7; SHA-256 `11b1668a7ff2623472e5ca8f5f6d8ac87919dbf11228122e01b2c984e28d3626`. Also the [1994 Gaussian-systems thesis](https://delarue.perso.math.cnrs.fr/Publis/PDF/these.pdf), contents and introduction pp. 1–6; SHA-256 `df472ec6bfeda598fa8ef68ed3f2fbbdb221a2453cc45402638b1d1104db0f51`.
- **Assani**, [2005 primary paper](https://www.impan.pl/shop/en/publication/transaction/download/product/87352), pp. 251–254 and Theorems 6–7; **Xiao**, [arXiv:2206.02197v2](https://arxiv.org/pdf/2206.02197v2), Theorems 1.2–1.4 and Corollary 1.5; **Kosz–Mirek–Peluse–Wan–Wright**, [arXiv:2411.09478v4](https://arxiv.org/html/2411.09478v4), the distinct-degree theorem and problem statements; **Austin**, [2024 manuscript](https://wrap.warwick.ac.uk/id/eprint/189124/1/WRAP-non-convergence-some-non-commuting-double-ergodic-averages-2024.pdf), opening theorem and Gaussian construction scope. Independently downloaded hashes are recorded in the manifest.

Additional hashes, URLs, PDF-validity checks, and unsuccessful downloads are in [manifest-extra.json](../sources/i05_crossfield_r2/manifest-extra.json), [manifest-older.json](../sources/i05_crossfield_r2/manifest-older.json), and [manifest-authorpage.json](../sources/i05_crossfield_r2/manifest-authorpage.json). A nominal `.pdf` response that was actually HTML was **not** treated as a downloaded paper.

The relevant accepted contract is family 145's `build/sections/01-introduction.tex`, `thm:main`, [immutable primary source](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Rokhlins-multiple-mixing-problem-for-one-transformation-September-23-2026/build/sections/01-introduction.tex), SHA-256 `88914bccc2fac68b930898a6a5587287ad07d0be7fbec9423931f8f71ddea35a`, Git blob `49fd4d05cdb48edec0d6e09f4044fe01e340c2a4`. It gives convergence for every fixed tuple of sets as the minimum ordered gap tends to infinity; it supplies no rate. The six-download manifest also records family 154's introduction, `inputs.tex` (`lem:triple-convergence`), `selected.tex` (`prop:selected-law`), the triple companion's transfer section, and the fourfold companion introduction. Their linear statements do not imply square sampling simply by restriction.

## 2. Prior-art finding: the Wick estimate is a standard Gaussian decoupling specialization

The older literature check preceded the detailed proof audit. It establishes the following reduction, which should be included in any future presentation of the candidate.

Fix a finite horizon `M` and `r>2`. Let

\[
 E_M=\mathbb C^M/\{\text{constant sequences}\},\qquad
 \|[z]\|_{E_M}=V_r(z_N:1\le N\le M).
\]

This is a finite-dimensional Banach space, viewed as real if necessary. Thus there is no infinite-dimensional measurability issue, no UMD assumption, and no need for a vector-valued extension of Mirek–Trojan.

For `s≥1` put `v_i(n)=U^{P_i(n)}h_i` and form the `E_M`-valued symmetric tensor whose `N`th coordinate is

\[
 K_N=\frac1N\sum_{n\le N}e(Q(n))
       \operatorname{Sym}(v_1(n)\otimes\cdots\otimes v_s(n)).
\]

For fixed `M`, all its vectors lie in a finite-dimensional subspace of `H`. Its coupled Gaussian realization, with the conventional Wick normalization, is the vector of weighted Wick averages. Its independent-copy realization is the average over permutations `π` of the vectors

\[
 \left(\frac1N\sum_{n\le N}e(Q(n))
       \prod_{i=1}^s W_i(v_{\pi(i)}(n))\right)_{N\le M}.
\]

Maas's symmetric case in Theorem 2.1, at `p=2`, compares the `L²(E_M)` norm of the coupled realization to that of this decoupled realization, with a constant depending only on `s`. His normalization can introduce an `s!` factor, which is absorbed into that degree-only constant. This is the **symmetric/Hermite** case, so repeated basis indices are allowed. Applying only a diagonal-free monomial theorem would be insufficient.

Each permuted independent-copy realization is an ordinary **single-function** polynomial average on independent Gaussian copies and a circle. Mirek–Trojan therefore bounds its `L²(E_M)` norm by `C_{s,d,L,r}∏||h_i||`. Triangle inequality handles the permutation average. The resulting Wick variation bound is uniform in `M`, in the phase, and in the Gaussian action; let `M→∞` by monotone convergence. This proves the qualitative content of (5.6) using explicit pre-existing theorems. The candidate's elementary conditioning argument gives the particular valid one-sided factor `s^{s/2}` instead.

For ordinary products, apply the familiar Wick product expansion. A contraction is a Fourier–Stieltjes coefficient of the common commuting orthogonal action at a polynomial time difference. Its product is an integral of polynomial phases against a finite complex measure. The coefficient-uniform Wick bound just obtained can be integrated against total variation. Sum the finitely many partial pairings. This gives (4.3) with a degree-dependent constant; the candidate's conditioning calculation specifies the displayed pairing factor. Finally use its maximal/density closure for Theorem G.

This is a **short explicit classical-corollary derivation**, not merely the observation that all mathematical proofs use older ingredients. The particular obstruction described as the new bridge—transferring control from independent copies to the coupled Gaussian diagonal—is precisely what Banach-valued Gaussian chaos decoupling already does. No rate of Gaussian mixing or special spectral assumption needs to be invented. The remaining contraction argument uses spectral calculus and uniformity already present in the imported polynomial theorem.

The formula for `B_D` is correct, but no sharpness or improvement over existing decoupling constants is claimed or demonstrated. Furthermore `C_{D,d,L,r}` itself is allowed to depend on `D`; displaying `B_D` separately does not establish an independently significant optimal-degree estimate.

**Conclusion of this comparison:** demote the proposed nonroutine-mechanism claim. I have established that the result is a standard decoupling application of classical theorems available by the time of Mirek–Trojan. I have **not** established that a named earlier paper already printed the complete Theorem G. Those are distinct conclusions.

## 3. Exact imported analytic theorem: PASS

Mirek–Trojan define averages of one function along an integer polynomial map in commuting invertible measure-preserving transformations, with the map zero at the origin. Their Theorem B gives an all-positive-integer `L^p` variation estimate for

\[
 1<p<\infty,\qquad r>\max\{p,p/(p-1)\},
\]

and explicitly states independence from polynomial coefficients. At `p=2` this is exactly every `r>2`. The dimension and degree are fixed structural parameters. The input is neither a multiple-function theorem nor a bound only on dyadic lengths. The candidate uses the theorem within this range; no `r=2` endpoint is asserted.

For each copy, absorb `P_i(0)` into `h_i` using an orthogonal operator. On `s` copies there are `sd` commuting generators. Adjoining `L` commuting rotations of one circle realizes `Q(n)-Q(0)`. The product observable has `L²` norm exactly `∏||h_i||` by independence. The circle factor has modulus one, so variation of the lifted average is the same for every circle point. Coefficient uniformity therefore includes the phase coefficients; there is no restriction of a generic conull set to a chosen circle point.

For fixed `D,d,L`, finitely many copy counts `0≤s≤D` suffice, so taking the maximum of their constants gives the candidate's common constant. Constant maps, negative coefficients, and constant phases cause no exception. In the `s=0` case the circle alone realizes the scalar exponential average. The maximal estimate follows by adding the `N=1` term to any finite-`r` variation bound, and then passing to the supremum.

## 4. Gaussian conditioning and variation: PASS

For `s` independent isonormal copies, the orthogonal projection of the `i`th coordinate of `H^s` onto its diagonal subspace is `1/s` times the sum of the coordinates. Hence, relative to `W_0=s^{-1/2}ΣW_i`,

\[
 \mathbb E[W_i(v_i)\mid\sigma(W_0)]=s^{-1/2}W_0(v_i),
\]

\[
 \operatorname{Cov}(W_i(v_i),W_j(v_j)\mid\sigma(W_0))
   =\delta_{ij}\langle v_i,v_j\rangle-s^{-1}\langle v_i,v_j\rangle.
\]

The residual Gaussian family is independent of the diagonal family. This remains valid for the full conditioning sigma algebra in infinite-dimensional `H`: project onto the closed diagonal Gaussian subspace; separability supplies a countable generating family. It is not necessary to assume independence merely from pairwise orthogonality of arbitrary non-Gaussian variables.

The candidate's conditional exponential formula is correct. Its extra factor `exp(½Σt_i²||v_i||²)` contributes no nonconstant squarefree monomial. Taking the `t_1…t_s` coefficient therefore gives exactly

\[
 \mathbb E\left[\prod_iW_i(v_i)\mid\sigma(W_0)\right]
    =s^{-s/2}:\!\prod_iW_0(v_i)\!:.
\]

For example `s=2` gives `(W_0(v_1)W_0(v_2)-⟨v_1,v_2⟩)/2`. Omitting either the contraction or the denominator would be wrong. The independent moment-integration tests below distinguish both.

For each fixed finite increasing index set, conditional Jensen/Minkowski in its finite-dimensional `ℓ^r` space bounds the norm of the conditional increments by the conditional expectation of their norm. Bound that norm by the full variation, then take the supremum over the countably many index sets. This proves (5.1) on a common conull set. Conditional Jensen in `L²` proves its norm consequence. Gaussian products are integrable, and the variation being conditioned has finite `L²` norm from the preceding step.

The conditioning sigma algebra need **not** be invariant under the separate-copy transformations. The proof applies conditional expectation to an already constructed sequence; it does not invoke an ergodic theorem on that sigma algebra. Finally, the countable collection of `W_0`-polynomials has the same joint law as the corresponding collection of `W`-polynomials. This transfers the variation norm to the original Gaussian system. No restriction of a product-measure conull set to a diagonal is present.

## 5. All contractions and spectral integration: PASS

The ordinary-product expansion sums over all partial pairings, including the empty pairing, full pairings for even degree, and pairings within a single original observable. It is valid without distinctness or orthogonality assumptions on the vectors. Its coefficients are positive covariance products; the negative signs belong inside Wick products. The number of pairings of size `a` is

\[
 \binom D{2a}(2a-1)!!=\frac{D!}{2^a a!(D-2a)!}.
\]

For every contraction, orthogonality and commutativity give

\[
 \langle U^{P_a(n)}h_a,U^{P_b(n)}h_b\rangle
  =\langle h_a,U^{P_b(n)-P_a(n)}h_b\rangle.
\]

The complexifications of the commuting orthogonal operators are commuting unitaries; their joint projection-valued measure on `T^d` supplies the displayed complex scalar measure, with a consistent inner-product/Fourier convention. The elementary spectral-partition Cauchy–Schwarz argument in the candidate proves the necessary total-variation bound. Positivity of an off-diagonal scalar spectral measure is neither true in general nor required.

Here is a precise way to handle null sets in the integration step. For a partial pairing let `ν` be its product complex measure and let `Z_N(θ,x)` be the weighted unpaired Wick average. For finite `M`, finite-dimensional Minkowski, followed by `L²` Minkowski, gives

\[
 \left\|V_r\left(\int Z_N(\theta,\cdot)\,d\nu(\theta):N\le M\right)\right\|_2
 \le\int\|V_r(Z_N(\theta,\cdot):N\le M)\|_2\,d|\nu|(\theta).
\]

The parameter dependence is measurable: after choosing the countably many Gaussian representatives involved, every finite average is a finite sum with continuous phase factors on a measurable choice of angular representatives. Variation is a countable supremum. One must not require the phase polynomial itself to be a globally continuous real lift on the torus; its exponential, and a measurable lift, suffice. The uniform weighted Wick bound makes the right side finite. Monotone convergence as `M→∞` finishes the argument. No intersection of uncountably many phase-dependent conull sets is taken.

The product total variation is bounded by the product of the contraction norm bounds. Multiplying this with the unpaired-vector bound leaves `∏_{i=1}^D||h_i||` in every term. The remaining Wick degree is `D-2a`, with factor `b_{D-2a}`. Fully paired terms reduce to the `s=0` scalar phase estimate, including spectral atoms and coincident polynomials. Summing gives exactly (4.3)–(4.4). Zero vectors give the zero average and require no division.

This is where commutativity is essential. Austin's noncommuting Gaussian examples are consequently a useful scope check, not a counterexample to Theorem G.

## 6. All-length convergence and closure: PASS

A complex sequence of finite `r`-variation and finite first term is bounded and Cauchy. If it were not Cauchy, successive disjoint tail pairs would exhibit an arbitrary number of jumps of a fixed positive size. The variation supremum would diverge. This argument uses the supremum over **all** increasing subsequences, not the sum of adjacent increments.

For polynomial observables, expand the product of the observables at their assigned times into finitely many coordinate monomials. The same time map may occur many times. Each nonconstant term is covered by (4.3), and constant terms are harmless. Intersect only finitely or countably many null sets as required.

The Gaussian-polynomial density argument is valid in `L^{2k}`. Conditional expectations onto the first finitely many basis coordinates converge in that norm because `σ(W)=F`. On a finite-dimensional Gaussian law, a putative `L^q` annihilator of polynomials (`q=(2k)/(2k-1)>1`) has an entire Gaussian-weighted Laplace transform. Hölder controls all exponential moments and derivatives on compact complex sets. The vanishing moments force the transform to vanish; Fourier uniqueness then annihilates the underlying finite signed/complex measure. Hahn–Banach yields density. A finite basis handles finite-dimensional `H`; `H={0}` leaves only constants modulo null sets.

For completeness the norm calculation in (6.1) is

\[
 \left\|\prod_j (M_j|u_j|^k)^{1/k}\right\|_2
 \le\prod_j\|M_j|u_j|^k\|_2^{1/k}
 \le\prod_j C_j^{1/k}\|u_j\|_{2k}.
\]

The first pointwise inequality is Hölder in the finite time sum. The displayed norm inequality is Hölder in space. Each `|u_j|^k` lies in `L²`, exactly as needed. This works for unbounded polynomial approximants; uniform `L∞` approximation is unnecessary.

Telescoping the multilinear difference and choosing bounded `L^{2k}` norms for the approximating sequences proves (6.2). The tail oscillation of the target is bounded by twice the maximal approximation error for each approximant on their common conull convergence set. Taking its `L²` norm and then the approximation limit shows zero oscillation. The same maximal inequality ensures a finite limit. Countably many sampled orbit times cause no representative problem for `L^{2k}` functions. This proves precisely Theorem G; it supplies no variation bound uniform in Gaussian degree for arbitrary observables.

## 7. Optional mixing limit and the actual corpus dependency: PASS, but not a new dependency for the Gaussian class

The accepted family 145 statement, extended from sets to fixed bounded functions by simple-function approximation, supplies a uniform separation threshold for each fixed tuple. Sorting `2k` times and taking a maximum over the finitely many assignments of the functions to their sorted positions is legitimate. With at least one centered function the product of the `2k` means is zero. Conjugates in `⟨z_n,z_m⟩` cause no change.

Here is an explicit version of the collision estimate. For `n>√R` and fixed `i,j≥1`, the positive real `m` satisfying `|in²-jm²|<R` lie in an interval of length

\[
 \frac{\sqrt{in^2+R}-\sqrt{in^2-R}}{\sqrt j}
 =\frac{2R}{\sqrt j(\sqrt{in^2+R}+\sqrt{in^2-R})}
 \le\frac{2R}{n}.
\]

There are at most `1+2R/n` integer possibilities. Within either tuple, distinct times are more than `R` apart once the corresponding index exceeds `√R`. Therefore the number of bad pairs in `[1,N]^2` is at most

\[
 2\lfloor\sqrt R\rfloor N+k^2N+2k^2R H_N,
\]

where `H_N≤1+log N`. This implies the candidate's bound. It correctly allows exact resonances such as `in²=jm²`; those contribute the `O_k(N)` term rather than being incorrectly ruled out.

For fixed `ε`, take its separation threshold `R`, then let `N→∞`. The good-pair correlations are at most `ε` and the bad-pair proportion vanishes. Hence the centered average tends to zero in `L²`. Theorem G already supplies its a.e. limit, and uniqueness of a limit in probability identifies it as zero. Centering all factors gives the claimed product-of-means limit for bounded inputs. This argument by itself does not prove pointwise convergence.

There is an even stronger dependency qualification than merely saying that §7 is optional. **For mixing Gaussian systems, all-orders mixing is already elementary from Gaussian covariance structure.** Mixing gives vanishing matrix coefficients between any two fixed first-chaos vectors. For finite coordinate blocks at pairwise diverging times, the off-block covariances tend to zero; the joint Gaussian characteristic function then tends to that of independent blocks. This gives correlation convergence for bounded continuous cylinder functions. Approximate arbitrary bounded observables in `L¹` by uniformly bounded such functions; a telescoping product and invariance bound the approximation errors uniformly in the times. Thus the same all-orders mixing conclusion in this Gaussian class needs no accepted corpus theorem. The optional citation to family 145 is valid, but is not essential even for the proposed Gaussian limit corollary.

## 8. Older dynamics comparisons and limits of novelty evidence

The search record is [search-log.json](../sources/i05_crossfield_r2/search-log.json). I did not infer worldwide novelty from the absence of an exact hit.

- **Gaussian dynamics is not automatically the K-system case.** De la Rue's thesis introduction and HDR §2.2 explicitly discuss singular-spectrum zero-entropy Gaussian systems and Gaussian–Kronecker examples. Thus Xiao's Pinsker reduction is not a one-line proof of all of Theorem G merely because the system is Gaussian. Conversely, the positive-entropy/Bernoulli portion is not a new target case just because it has Gaussian coordinates.
- **Weak disjointness is a different, stronger rectangular-good-set property.** De la Rue's HDR §7 explains its implication for linear double averages and states the relative-factor and universal-system results. Its hypotheses do not automatically hold for an arbitrary common Gaussian action. Polynomial-time sampling does not follow just by translating the linear parameter. I inspected the author-hosted primary account, not merely catalogue descriptions.
- **Retrieval limitation:** the full Lesigne–Rittaud–de la Rue 2003 PDF still was not obtained. HAL returned a non-PDF challenge page; another file URL failed. The publisher abstract, author publication page, author-uploaded indexed extracts, and de la Rue's HDR account were available. I do not claim a full-paper theorem-by-theorem clearance. The Kwapień 1987 PDF endpoint likewise returned non-PDF content; its theorem was not cited as directly read. Maas supplies the needed actual statement.
- **Assani 2005** discusses linear double averages and spectral/Wiener–Wintner assumptions, including Gaussian examples with specified rate behavior. The inspected results do not state arbitrary-polynomial convergence for every Gaussian action. They also do not make the newly located Banach-valued decoupling comparison disappear.
- **Kosz–Mirek–Peluse–Wan–Wright v4** permits distinct polynomial degrees in arbitrary systems. It does not include `n²,2n²,3n²` through that hypothesis. Its general-system advance and the present Gaussian-class application have different scopes; the former's importance is not a certificate of novelty or importance of every subclass corollary.
- **Austin** excludes dropping commutativity, even in Gaussian constructions. The candidate respects the required common first chaos and commutativity.

No verified MathDB importance ranking for this Gaussian specialization was obtained. No ranking is assigned. The primary polynomial-averaging literature provides the named-problem context, not the missing project acceptance evidence.

## 9. Independent tests and reproducibility

[check.py](../experiments/i05_crossfield_r2/check.py) is a new standard-library-only script; it does not import or copy the discovery checker. Its deterministic output is [check.json](../experiments/i05_crossfield_r2/check.json).

1. **24 exact Gaussian projection cases:** degrees 1–8, with mixed vectors in dimensions 1–2. The left side is computed by expanding affine forms in independent Gaussian residual coordinates and integrating individual monomials using their exact moments. Residual coordinates have variance `s`, making the scaled projection rational. This differs from simply comparing two versions of the same squarefree generating-function recurrence. The right side is independently enumerated Wick pairings. Singular/repeated directions, negative inner products, and the degree-two nonzero conditional contraction are included.
2. **312 exact spectral-coefficient cases:** rational rotations in two real two-dimensional blocks, positive and negative polynomial time differences, generally nonreal off-diagonal spectral weights. The complex spectral formula agrees exactly with direct rotation matrix coefficients. The tested total-variation ratio is at most `0.999686451`.
3. **40 exact ordinary-product expansions** in degrees 1–8, including all full and partial pairings. Pairing counts are `1,2,4,10,26,76,232,764` and agree with the displayed factorial formula.
4. **90 cases each of conditional and complex-measure variation inequalities**, with complex-valued sequences and `r=2.01,3,4`. Variation is computed by exhaustive increasing-subsequence enumeration on nine times. Largest tested ratios are `0.824792805` and `0.757507956`, respectively.
5. **72 collision rectangles and 24,219 individual collision counts** check the explicit §7 bounds, with `k≤5`, `N≤80`, and separation thresholds through `1000`. Exact resonances and thresholds larger than the sampled square range are included.

These checks falsify plausible normalization, sign, complex-measure, and collision-count mistakes; they are not proofs of infinite-dimensional convergence or novelty. Reproduce with:

```bash
python frontier/experiments/i05_crossfield_r2/check.py
```

The final [artifact-hashes.json](../sources/i05_crossfield_r2/artifact-hashes.json) records the review and supporting artifact hashes. Only this review and the two assigned `i05_crossfield_r2/` directories were written. No agents, commits, staging, shared-index edits, or changes to other projects were made.

## 10. Recommendation to the parent

**Accept the mathematical proof verdict; do not promote this to a second substantial accepted finding on the present record.** There is no missing analytic lemma to repair. The precise issue is the novelty/significance/dependency classification:

- The Gaussian variation transfer is supplied by known Banach-valued chaos decoupling, with standard Wick/spectral handling of contractions.
- The full statement might be an unrecorded application; exact published priority remains unverified. It must not be advertised as a demonstrated new-to-literature theorem.
- The explicit combinatorial factor has no demonstrated sharpness or other independent significance.
- Neither the convergence theorem nor its mixing Gaussian limit needs the accepted OpenAI corpus.

The genuinely missing lemma for the original **general mixing** polynomial objective remains a diagonal oscillation/variation mechanism beyond Gaussian chaos, or another comparably substantive corpus-enabled estimate. All-orders mixing plus the collision count gives norm convergence, not the required all-length pointwise conclusion. The current correct Gaussian argument does not supply that missing mechanism for general systems. Further work should address such a new estimate or choose a fresh target, rather than increase the finding count on the strength of this classical application.
