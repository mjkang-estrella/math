# Iteration 05: cross-field screening and a Gaussian polynomial-averaging candidate

Date: 2026-10-08. Research record for independent review, not an accepted finding.

**Verdict.** This pass gives a complete proposed proof of polynomial multiple pointwise convergence for commuting **Gaussian** actions, together with an explicit finite-degree Gaussian variation estimate. The proof is in §§4–6. It includes equal-degree polynomial configurations, such as `n², 2n², 3n²`, without a mixing-rate assumption. This is the promising positive result to review. Neither worldwide novelty nor the user's substantial-contribution gate has been certified. No new accepted-finding number is assigned, and no claim is made that the general mixing-system polynomial problem is solved.

The argument was found while trying to bridge accepted families 145 and 154, but its final Gaussian proof uses a classical single-function polynomial variation theorem, not those accepted results. This distinction is essential: it must not be advertised as a new consequence that needs the OpenAI corpus. The nonautomatic candidate step is a Gaussian conditional-expectation construction followed by control of every contraction term; a product-space theorem alone cannot be restricted to the diagonal.

## 1. Scope, sources and exclusions

The immutable OpenAI revision is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. All its theorem statements are accepted under the user's premise; none of their proofs is being audited here. New deductions below are proved separately.

Read the project instructions, `sources/upstream.json`, the 372-family catalogue, complete `sources/preprints-tree.json`, `SCREENING.md`, frontier README/OUTCOME, iteration README, and the earlier cross-field findings/review. The catalogue scan covered all family headings and the relevant full entries; it was not a reading of all 372 manuscript proofs. R006 is already accepted as substantial. R005/R007, primitive-root arithmetic, ordinary bounded-multiplier ISP families, the earlier sunflower/Kakeya route, and the stalled Mumford/K3 construction were not reopened.

Retrieved 107 TeX/Bib source files for the nine relevant manuscripts and companions using the complete preprints tree. Each matches its pinned Git blob identifier; SHA-256 values and immutable raw URLs are in [upstream-manifest.json](../sources/i05_crossfield/upstream-manifest.json). Primary literature downloads, including failed retrievals, are recorded in [literature-manifest.json](../sources/i05_crossfield/literature-manifest.json). The final input/source integrity check is [validation.json](../sources/i05_crossfield/validation.json). Only this report and the assigned `sources/i05_crossfield/` and `experiments/i05_crossfield/` directories were written. No agents, commits, staging or shared-index edits.

## 2. Three genuinely different bridges screened before selection

| Bridge and named target | Actual accepted statements and companion check | Prior-art or mathematical obstruction | Disposition |
|---|---|---|---|
| **Combinatorics/spectral geometry:** strong thin trees (174) + prescribed-size Ramanujan graphs (178), aiming at spectral thin trees or Bilu–Linial signings | Strong thin-tree `thm:main` gives cut thinness `C/k` for finite loopless k-edge-connected multigraphs. The algorithmic companion already supplies construction (`thm:tt-algorithm`). Ramanujan `thm:main` supplies simple d-regular graphs on all sufficiently large even orders, with all nontrivial eigenvalues strictly inside `±2√(d−1)`; `cor:target-size` already handles approximate prescribed size. Its introduction expressly excludes solving arbitrary-graph Bilu–Linial signings. | Spectral thin trees in expanders already follow from an effective-resistance bound and the MSS/Harvey–Olver theorem recorded as Theorem 1.5 in Anari–Oveis Gharan. Indeed `R_eff(e) ≤ 2/λ₂(L_G)`, so a d-regular Ramanujan graph gives `O(1/(d−2√(d−1)))` spectral thinness. No new estimate is involved. Arbitrary cut thinness does not imply spectral thinness. | **Reject:** routine/prior-art implication. Neither an arbitrary signing nor a new thin-tree theorem was obtained. |
| **Geometry/analysis/probability:** sharp entropy/simplex (101) + subgaussian log-Sobolev (093), aiming at full KLS | Entropy `intro:entropy` gives `h(f) ≥ m + ½ log det Cov(f)`, with affine products of exponentials as the equality class. LSI `thm:main` needs a *linear subgaussian* parameter a, and gives `Ent(f²) ≤ C a² ∫|Df|²`. Its `cor:intro-transport` already gives quadratic transport–entropy. | Covariance/entropy control does not provide the missing subgaussian hypothesis. For `X = Exp(1)−1`, `E X=0`, `Var X=1`, `h(X)=1`, while `E exp(X²/a²)=∞` for every finite a. The sharp entropy equality example itself blocks that proposed transfer. | **Reject:** no KLS advance. The one-dimensional example refutes only the proposed hypothesis upgrade; it is not a counterexample to KLS. Transport and bounded-perturbation corollaries are already routine or recorded elsewhere. |
| **Dynamics/harmonic analysis:** mixing of all orders (145) + linear multiple pointwise convergence (154) + polynomial single-function averaging, aiming at the polynomial multiple pointwise problem | Rokhlin `thm:main` gives every finite mixing order, without a rate. Multiple averages `thm:main` gives consecutive *linear* iterates, with triple/fourfold companions checked. More strongly, its `inputs.tex`, `lem:triple-convergence`, already gives all-systems triples at distinct positive linear slopes. | The squares configuration is not covered by merely restricting a linear average to a subsequence. The 2026 distinct-degree polynomial theorem does not cover equal degrees; Pinsker/K-system results impose a different structural reduction. For general mixing systems, the pointwise polynomial bridge remains absent. | **Selected for deeper work:** Gaussian conditioning supplies a proposed new variation estimate and a complete special-class convergence proof. General mixing case remains unresolved. |

The first rejection is based on the primary [Anari–Oveis Gharan manuscript, Theorem 1.5](https://arxiv.org/pdf/1411.4613v4), not on an inference that absence of a search result establishes novelty. The second rejection follows directly from the displayed source hypotheses and the elementary divergent integral

\[
\int_{-1}^{\infty}\exp(x^2/a^2-x-1)\,dx=\infty.
\]

For named importance, the primary polynomial-convergence literature states the Bergelson/Furstenberg–Bergelson–Leibman pointwise problem. I did not obtain a verified MathDB importance classification for the Gaussian specialization and assign it **no MathDB ranking**. The [MathDB “Log-Sobolev KLS conjecture” page](https://mathdb.com/p/363364/log-sobolev-kls-conjecture) concerns the already-covered subgaussian direction; it is not evidence that this pass solved full KLS.

## 3. Selected target, stronger companions, and literature screen

The motivating case is

\[
\frac1N\sum_{n=1}^N f_1(T^{n^2}x)f_2(T^{2n^2}x)f_3(T^{3n^2}x).
\tag{3.1}
\]

Accepted family 154 is not a black box for (3.1). In its `selected.tex`, `prop:selected-law`, invariance comes from translating a **linear** parameter and telescoping endpoint terms. Translating `n²` by one does not preserve the sampled times. Taking a product system gives almost-everywhere convergence for product measure, whose conull set may miss the diagonal completely. Neither mistake is used below.

The source checks included all three pointwise companions. In particular, `inputs.tex`, `lem:triple-convergence` of the multiple-averages manuscript already proves positive-linear-slope triples for every standard invertible system, using `prop:smooth-input` and the triple companion's `transfer.tex`, `prop:tr-oscillation`. Thus an all-systems **linear** triple would be a duplicate even though the companion's headline theorem assumes mixing.

The main external input is [Mirek–Trojan, arXiv:1405.5566v1, Theorems A and B, pp. 1–2](https://arxiv.org/pdf/1405.5566v1), published in *American Journal of Mathematics* 138(6), 2016. For a fixed number of commuting invertible probability-preserving transformations and an integer polynomial mapping P with P(0)=0, their single-function averages have an `L²` r-variation bound for every r>2. Constants depend on the polynomial dimensions and degree, not on its coefficients or the particular system. Theorem A also gives a.e. convergence. Only this single-function theorem is imported. Constant polynomial terms can be absorbed into the observable. A corresponding maximal bound follows by adding the first average to the variation seminorm.

Other primary comparisons, checked before or during selection and checked again against the final scope:

- [Kosz–Mirek–Peluse–Wan–Wright, arXiv:2411.09478v4](https://arxiv.org/html/2411.09478v4): polynomial multiple pointwise convergence for commuting transformations under a **distinct-degree** hypothesis. This does not cover (3.1). Its introduction supplies named-problem context, not a proof of novelty for the present special class.
- [Xiao, arXiv:2206.02197v2, Theorems 1.2–1.3 and Corollary 1.5](https://arxiv.org/pdf/2206.02197v2): pointwise convergence reduces to the Pinsker factor; in particular K-systems are covered. The present proof does not require trivial Pinsker factor or a spectral decay rate. This comparison does not assert that no earlier theorem covers any given Gaussian example.
- [Bourgain, 1989, Theorem 1](https://www.numdam.org/item/PMIHES_1989__69__5_0.pdf): single-transformation polynomial pointwise convergence and maximal estimates. This already suffices for the decoupled common-polynomial case, but the proof below uses Mirek–Trojan for arbitrary polynomial maps.
- [Assani, 2005, pp. 251–252 and Theorems 6–7](https://www.impan.pl/shop/en/publication/transaction/download/product/87352): linear bilinear averages, spectral/relative spectral conditions, and particular Gaussian Wiener–Wintner examples. The inspected statements do not assert the arbitrary-polynomial, arbitrary-Gaussian-action conclusion below. This is a limited comparator, not an exhaustive reading of Assani's monograph and all cited work.
- [Austin, *Non-convergence of some non-commuting double ergodic averages*, theorem on pp. 2–3](https://wrap.warwick.ac.uk/id/eprint/189124/1/WRAP-non-convergence-some-non-commuting-double-ergodic-averages-2024.pdf): even Gaussian transformations can have divergent double averages when commutativity is absent. This is consistent with, and an important scope check on, the proposed theorem.
- Lesigne–Rittaud–de la Rue's weak-disjointness paper was located and its definition/context checked through primary indexed text and de la Rue's author-hosted joining notes. A local full-paper download failed. This remains a literature-search limitation, not a clearance of that entire literature.

Post-proof queries explicitly combined “Gaussian actions/systems”, “polynomial multiple ergodic averages”, “pointwise convergence”, “Wick”, “decoupling”, and “variation”. No exact duplicate was established by these searches. **No conclusion about worldwide priority follows from that fact.** Search engines repeatedly returned Gaussian-integer arithmetic and Gaussian limit distributions, which are not this topic. A review should specifically check older Gaussian ergodic theory and Gaussian decoupling sources; the ingredients themselves are classical.

## 4. Exact proposed theorem

Let H be a separable real Hilbert space and let

\[
W:H\longrightarrow L^2(\Omega,\mathcal F,\mu)
\]

be an isonormal Gaussian family: it is real-linear, centered, jointly Gaussian, and `E[W(h)W(g)]=⟨h,g⟩`. Assume `σ(W)=F` modulo null sets on a standard probability space. Let `U₁,…,U_d` be commuting orthogonal operators on H, inducing commuting invertible probability-preserving transformations `T₁,…,T_d` with

\[
W(h)\circ T^a=W(U^a h),\qquad a\in\mathbb Z^d.
\tag{4.1}
\]

This is a **Gaussian action**. Merely realizing a probability space as a space with Gaussian coordinates is not sufficient: the action must preserve this common first Gaussian chaos as in (4.1).

**Theorem G (proposed complete proof).** For every k≥1, every fixed integer-coefficient polynomial maps `P₁,…,P_k: Z→Z^d`, and every fixed `f₁,…,f_k∈L^{2k}(μ)`, the averages

\[
A_N(\mathbf f)(x)=\frac1N\sum_{n=1}^N
 \prod_{j=1}^k f_j(T^{P_j(n)}x)
\tag{4.2}
\]

converge to a finite limit for μ-almost every x as N tends through **all** positive integers. In particular this holds for bounded observables. Polynomials may have equal degrees, equal values, negative coefficients, or constant terms. No mixing, ergodicity or spectral regularity is required. The exceptional set may depend on the fixed maps and functions.

The quantitative core is the following statement. For any D≥1, degree bound L≥1, r>2, `h₁,…,h_D∈H`, maps `P_i∈(Z[n])^d` of degree at most L, and real polynomial Q of degree at most L, put

\[
B_N=\frac1N\sum_{n=1}^N e(Q(n))
      \prod_{i=1}^D W(U^{P_i(n)}h_i),\qquad e(t)=e^{2\pi it}.
\]

For `V_r(b_N)=sup_{N₀<⋯<N_m}(Σ_{j=1}^m|b_{N_j}−b_{N_{j−1}}|^r)^{1/r}`,

\[
\|V_r(B_N:N\ge1)\|_2
 \le C_{D,d,L,r}\,\mathcal B_D\prod_{i=1}^D\|h_i\|_H,
\tag{4.3}
\]

where one admissible combinatorial factor is

\[
\mathcal B_D=\sum_{a=0}^{\lfloor D/2\rfloor}
 \frac{D!}{2^a a!(D-2a)!}\,b_{D-2a},
 \qquad b_s=s^{s/2}\ (s\ge1),\quad b_0=1.
\tag{4.4}
\]

Here `C_{D,d,L,r}` may be chosen as the maximum of finitely many constants from the stated single-function variation theorem for at most `dD+L` commuting transformations, at degree at most L. In particular it is independent of the coefficients, H, the Gaussian action, and the vectors. No claim is made that the D-dependence is sharp. No variation estimate for arbitrary bounded observables with a uniform Gaussian-degree-free constant is asserted.

## 5. Proof of the Gaussian variation estimate

### 5.1. Conditional expectation contracts variation

For any sub-σ-algebra G and any sequence `Z_N` for which the right side is integrable, conditional Minkowski for each finite increasing sequence of indices gives

\[
V_r(\mathbb E[Z_N\mid\mathcal G]:N\ge1)
 \le \mathbb E[V_r(Z_N:N\ge1)\mid\mathcal G]
\quad\text{a.e.}
\tag{5.1}
\]

There are only countably many finite index sequences, so their null sets can be united. Conditional Jensen then gives an L² contraction bound. The same Minkowski argument permits integrating a measurable sequence against a finite complex measure, using its total variation. One can first use finite variation suprema and then monotone convergence, so no uncountable supremum is being interchanged with integration.

### 5.2. An exact Gaussian conditioning construction

Take s independent copies `W₁,…,W_s` of W and define

\[
W_0=s^{-1/2}\sum_{i=1}^sW_i,\qquad\mathcal G=\sigma(W_0).
\]

Then W₀ is another isonormal family with the same law as W. For arbitrary `v₁,…,v_s∈H`,

\[
\mathbb E\!\left[\prod_{i=1}^sW_i(v_i)\mid\mathcal G\right]
 =s^{-s/2}:\!\prod_{i=1}^sW_0(v_i)\!:\, .
\tag{5.2}
\]

Colons mean Wick product. To prove (5.2), define the Wick product as the coefficient of `t₁⋯t_s` in

\[
\exp\!\left(W_0\!\left(\sum_i t_i v_i\right)
               -\frac12\left\|\sum_i t_i v_i\right\|^2\right).
\tag{5.3}
\]

The conditional Gaussian means of `W_i(v_i)` are `W₀(v_i)/√s`; conditional covariances are `δ_{ij}⟨v_i,v_j⟩−⟨v_i,v_j⟩/s`. This follows by orthogonal projection onto the diagonal copy of H in `H^s`; the residual is independent of W₀ because it is jointly Gaussian and orthogonal to it. Consequently the conditional moment-generating function is

\[
\exp\!\left(\frac12\sum_i t_i^2\|v_i\|^2\right)
\exp\!\left(W_0\!\left(\sum_i\frac{t_i}{\sqrt s}v_i\right)
       -\frac12\left\|\sum_i\frac{t_i}{\sqrt s}v_i\right\|^2\right).
\tag{5.4}
\]

The first exponential has no nonconstant squarefree monomial. Extracting `t₁⋯t_s` proves (5.2), including its normalization and all negative contraction signs. Gaussian exponential moments justify differentiation; alternatively this is a finite polynomial identity in Gaussian moments.

### 5.3. Weighted Wick averages

Set

\[
D_N=\frac1N\sum_{n=1}^N e(Q(n))
       \prod_{i=1}^s W_i(U^{P_i(n)}h_i).
\]

This is a *single-function* polynomial average on independent copies of the Gaussian system, with an auxiliary circle. On copy i let the d generators act only on that copy. If `Q(n)=β₀+Σ_{ℓ=1}^L β_ℓn^ℓ`, adjoin circle rotations `z↦z+β_ℓ`. All these transformations commute. Apply the single-function theorem to

\[
F(\omega_1,\ldots,\omega_s,z)=e(z)\prod_iW_i(h_i).
\]

Its iterated average is `e(z−β₀)D_N`, and `||F||₂=∏||h_i||` by independence. Constant terms in P_i are absorbed into h_i. The source theorem therefore yields

\[
\|V_r(D_N)\|_{L^2(\Omega^s)}
 \le C_{s,d,L,r}\prod_i\|h_i\|.
\tag{5.5}
\]

The circle factor has modulus one, so the L² variation is the same for every z. No assertion at a special point is deduced by restricting a generic product-measure conull set.

Using (5.2) for each integer n and then (5.1) proves

\[
\left\|V_r\!\left(\frac1N\sum_{n\le N}e(Q(n))
 :\!\prod_{i=1}^sW(U^{P_i(n)}h_i)\!:\right)\right\|_2
 \le C_{s,d,L,r}s^{s/2}\prod_i\|h_i\|.
\tag{5.6}
\]

The law of the entire countable sequence of W₀-polynomials agrees with that of the W-polynomials. Invariance of `σ(W₀)` under the separate-copy transformations is **not** required: (5.1) is an inequality for arbitrary conditioning. For s=0 the Wick product is 1; the same circle argument bounds the variation of the scalar averages of `e(Q(n))`, with constant `C_{0,d,L,r}`.

### 5.4. Every ordinary-product contraction is controlled

The exact Wick expansion is

\[
\prod_{i=1}^D W(v_i)
 =\sum_{\pi}
   \left(\prod_{(a,b)\in\pi}\langle v_a,v_b\rangle\right)
   :\!\prod_{i\notin V(\pi)}W(v_i)\!:\, ,
\tag{5.7}
\]

where π runs through all partial pairings of `{1,…,D}`. It follows by multiplying (5.3) by `exp(½||Σt_iv_i||²)` and comparing the squarefree coefficient; diagonal quadratic terms do not contribute. This proves the expansion rather than assuming that contraction terms vanish.

For `v_i(n)=U^{P_i(n)}h_i`, commutativity and orthogonality give

\[
c_{ab}(n)=\langle h_a,U^{P_b(n)-P_a(n)}h_b\rangle.
\]

The joint spectral resolution of the commuting unitaries on the complexification of H supplies a finite complex measure σ_ab on `T^d` such that

\[
c_{ab}(n)=\int_{\mathbb T^d}
 e\bigl((P_b(n)-P_a(n))\cdot\theta\bigr)\,d\sigma_{ab}(\theta),
\qquad\|\sigma_{ab}\|_{\rm TV}\le\|h_a\|\|h_b\|.
\tag{5.8}
\]

For completeness the total-variation bound follows on a finite spectral partition `{E_j}` by
`Σ|⟨E_jh_a,E_jh_b⟩| ≤ (Σ||E_jh_a||²)^{1/2}(Σ||E_jh_b||²)^{1/2}`; then take the supremum over partitions. Choose the Fourier convention matching the displayed matrix coefficient; conjugating the measures under the opposite convention changes no estimate.

For a fixed partial pairing π, the product of the c_ab(n) is thus the integral of a polynomial phase against `⊗_{(a,b)∈π}σ_ab`. Multiplying by `e(Q(n))` leaves a real polynomial phase of degree at most L. Apply (5.6) to the unpaired coordinates and integrate using total variation and Minkowski. The result is

\[
\|V_r(\text{averaged term for }\pi)\|_2
 \le C_{D,d,L,r}\,b_{D-2|\pi|}\prod_{i=1}^D\|h_i\|.
\tag{5.9}
\]

Measurability follows because the finite averages depend continuously on the spectral parameters and variation is a countable supremum. The bound (5.6) is uniform in the phase coefficients. Hence Fubini/Minkowski uses finite total-variation measures and a finite L² bound; a phase-independent conull set is **not** assumed. Fully paired terms are covered by the s=0 case, including coincident polynomials and spectral atoms. Sum (5.9) over the `D!/(2^a a!(D−2a)!)` pairings of size a. This proves (4.3).

## 6. Proof of pointwise convergence for general observables

Finite r-variation implies convergence of a complex sequence whenever its first term is finite: a non-Cauchy sequence gives arbitrarily many disjoint jumps of some fixed positive size and hence infinite variation. Thus (4.3) gives convergence whenever every f_j is a finite polynomial in finitely many Gaussian coordinates. Expand their product into finitely many terms; each is covered by (4.3) after assigning to every coordinate the polynomial map of the original factor containing it. Constant terms cause no difficulty.

Here is the needed closure argument, with its integrability exponent explicit. Write

\[
M_jg=\sup_{N\ge1}\frac1N\sum_{n=1}^N
 |g(T^{P_j(n)}\cdot)|.
\]

The single-function polynomial maximal bound gives `||M_jg||₂ ≤ C_j||g||₂`. Hölder in the finite n-sum and then Hölder in x give

\[
\sup_N|A_N(\mathbf u)|\le\prod_{j=1}^k
          (M_j(|u_j|^k))^{1/k},
\quad
\left\|\sup_N|A_N(\mathbf u)|\right\|_2
 \le C\prod_{j=1}^k\|u_j\|_{2k}.
\tag{6.1}
\]

Finite Gaussian polynomials are dense in `L^{2k}(μ)`. One justification is to condition on the first m coordinates of an orthonormal basis of H, then use martingale convergence in `L^{2k}`. Polynomials are dense for each finite-dimensional standard Gaussian law: if an `L^q` function, `q=(2k)/(2k−1)>1`, annihilates all polynomials, its Gaussian-weighted Laplace transform is entire (Hölder and Gaussian exponential moments), all derivatives at zero vanish, and Fourier uniqueness forces the function to vanish. Hahn–Banach gives the claimed density. Finite-dimensional and degenerate H are included by choosing a basis of H itself.

Choose polynomial `g_j^{(m)}→f_j` in `L^{2k}` with uniformly bounded `L^{2k}` norms. Telescoping the k-linear average, applying (6.1) to each difference term, shows

\[
\left\|\sup_N|A_N(\mathbf f)-A_N(\mathbf g^{(m)})|\right\|_2\to0.
\tag{6.2}
\]

On the intersection of the countably many conull polynomial-convergence sets, the tail oscillation O(f) of `A_N(f)` is at most twice the supremum in (6.2), for every m. It follows that `||O(f)||₂=0`. Formula (6.1) also bounds the supremum, so the limit is finite. This proves Theorem G. For the bounded case there is additionally convergence in every finite L^p by dominated convergence. No uniform rate follows.

## 7. The motivating mixing case: a limit identification using accepted family 145

There is an actual optional dependency on the accepted corpus if one wants a short identification of the limit in (3.1), or in its k-factor version with iterates `j n²`, on a **mixing Gaussian** system. Theorem G already gives the a.e. limit. Family 145 then identifies it as `∏_j∫f_j dμ`, as follows.

After expanding centered functions it suffices to consider bounded `g₁,…,g_k`, all of norm at most 1, with at least one of mean zero, and
`z_n=∏_j g_j∘T^{j n²}`. The accepted all-orders mixing statement for sets extends to this fixed tuple of functions and their conjugates by finite simple-function approximation. For every ε>0 there is an R such that the correlation of the 2k functions at **pairwise R-separated times** has modulus at most ε. Sort the times and use the accepted ordered-gap statement; there are only finitely many permutations, and the product of means is zero.

For n,m>√R, times inside each individual k-tuple are R-separated. A cross-collision has `|i n²−j m²|<R` for some `1≤i,j≤k`. For each fixed n and i,j, possible positive m lie in an interval of length at most `C_k R/n` (subtract the square roots of the interval endpoints; for n>√R the lower radicand is nonnegative). Hence there are at most `C_k(1+R/n)` integer m. The proportion of bad pairs in `[1,N]²` is at most

\[
C_k\left(\frac{\sqrt R+1}{N}+
             \frac{R\log(2N)}{N^2}\right).
\]

On good pairs the correlation is at most ε, and on bad pairs it is at most 1. Therefore `||N⁻¹Σz_n||₂²` has limsup at most ε. Let ε→0. This proves convergence in L² to zero, so the already established a.e. limit is zero. Summing the centered expansion identifies the limit for arbitrary bounded f_j.

This norm argument is an auxiliary deduction, **not** the pointwise breakthrough: by itself it gives no a.e. convergence on all N. Nor is higher-order mixing claimed to be new for Gaussian systems. The proposed contribution is the variation/conditioning argument in §5.

## 8. Finite falsification checks and vulnerable steps

The dependency-free script [check.py](../experiments/i05_crossfield/check.py) produces [check.json](../experiments/i05_crossfield/check.json). It checks:

1. The conditional Gaussian moment identity, with the precise `s^{−s/2}` scaling handled by scaled variables, in degrees 1–8 using exact rational Gram matrices. The conditional moment-generating function is computed in the squarefree polynomial quotient and compared with Wick recursion.
2. The full ordinary-product expansion in degrees 1–8, symbolically in distinct coordinate variables with rational Gram entries. The numbers of partial-pairing terms are `1, 2, 4, 10, 26, 76, 232, 764`; all signed terms cancel to the ordinary product.
3. A cyclic Gaussian action on five coordinates, at polynomial times `n², 2n², 3n²`. A fixed rational coordinate evaluation gives exact average `17/10` at N=`5,10,25,50,100`. This tests repeated-time and nonmixing cases and illustrates that an arbitrary nonmixing limit is not asserted to equal a product of means.
4. Conditional Minkowski for finite r=4 variation on 300 finite probability arrays, each with 15 time indices and five atoms. Dynamic programming maximizes over every increasing subsequence, not merely consecutive increments. The largest tested ratio of variation after averaging to averaged variation is `0.728808241`.

These are finite algebra/normalization tests. They do not prove an infinite-dimensional theorem or establish novelty. The initial script required unavailable SymPy; it was replaced by exact `Fraction` polynomial arithmetic using only the Python standard library. No package installation was needed.

The review should focus on these potential failure points:

- **Source input:** Mirek–Trojan is a single-function, commuting-action, all-length r-variation statement on L²; check precisely Theorem B at p=2, r>2. Confusing it with a multiple-function theorem would be circular.
- **Conditioning:** (5.2) is a Wick product, not the ordinary product. The negative conditional covariance terms and `s^{−s/2}` are indispensable. The conditional σ-algebra need not be invariant.
- **Contractions:** orthogonality and **commutativity** are used in (5.8). Noncommuting Gaussian transformations can fail even norm convergence. The proof does not cover them.
- **Spectral integration:** use total variation of complex spectral measures, include fully paired terms, and use the uniform phase bound before integrating. Never assert a common exceptional set for uncountably many phases without this argument.
- **Approximation:** polynomial approximants need not be uniformly bounded; the `L^{2k}` maximal estimate is what makes closure valid. A bare L² approximation for each input would not justify (6.2) when k>1.
- **Scope:** every T_j must preserve one common Gaussian first chaos. Arbitrary measure-preserving transformations on a nonatomic Gaussian probability space do not qualify.
- **Contribution status:** Gaussian conditioning, Wick expansion, joint spectral calculus, and the imported variation theorem are classical ingredients. The estimate assembled here must survive a fresh proof review and a serious older-literature novelty check before it can count as the requested independent contribution.

## 9. Remaining bridge and final disposition

For a general mixing transformation T, (3.1) remains unresolved **in this work**. The precise missing point is a replacement for (5.2)–(5.9): a mechanism controlling the diagonal multiple averages at equal-degree polynomial times by quantities with finite oscillation/variation. Higher-order mixing without a rate supplies the L² argument of §7, but not that control. Selected linear laws, subsequence restriction, Pinsker reduction by itself, and product-space convergence do not provide it.

The result submitted for fresh review is Theorem G and the Gaussian variation estimate (4.3), with (3.1) as a concrete motivating case. The proof is complete as written and makes a nontrivial special-class assertion; no unresolved analytic lemma is hidden inside it beyond the explicitly cited classical variation theorem and standard joint spectral theorem. That is a **proposed proof**, not independent certification. A reviewer finding it to be a standard known Gaussian consequence should reject its novelty gate even if every displayed deduction is correct.

Accordingly: three distinct bridges were screened; two were rejected early; the dynamics bridge produced a positive candidate with an explicit construction and estimate. This pass does **not yet establish** that the user's request for another genuinely new substantial theorem after R006 has been fulfilled. The obstruction records alone do not count as success. Worldwide priority, substantiality and acceptance are left open for the parent's fresh independent review.
