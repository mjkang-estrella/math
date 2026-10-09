# Arithmetic round 3: fixed-progression PD and a positive-proportion primitive-root candidate

Date: 2026-10-08. Pin: `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

**Status: new proof submitted for independent review, not an integrated finding.** Under the stipulated accepted manuscript contracts, the argument below derives the full Poisson–Dirichlet law for `p−1` in every fixed reduced progression. It consequently derives a positive **lower** relative density of primitive-root primes for each admissible integer base. It does not prove existence of a natural density, the Artin constant formula, effective thresholds, or any uniformity in a modulus growing with `x`. The proof uses the manuscript's general graph pairing contract, not conditioning of its marginal PD theorem. The genuinely new step is §3, which inserts two physical endpoint residues and then averages a shared dilation label. All other changes to extraction are itemized in §5.

Read: `AGENTS.md`, `sources/upstream.json`, relevant catalogue entries in `sources/CONTENTS.md`, `frontier/iterations/README.md`, the full round 1 arithmetic report and round 2 review, and the source contracts identified below. No upstream truth audit, further agent, commit, staging, or shared-index/prior-report edit was performed.

## 1. Statements, dependencies, and the gap being closed

Let `q_1(p) ≥ q_2(p) ≥ ...` be the prime factors of `p−1`, with multiplicity and padding by 1, and put `V_j(p)=log q_j(p)/log(p−1)` for `p≥3`. Let `(L_j)` have PD(1). Write `N(x)=π(2x)−π(x)`.

**Theorem AP (candidate deduction).** For every fixed integer `M≥1`, every integer `b` with `(b,M)=1`, every fixed `k≥1`, and every bounded continuous real function `H` on `[0,1]^k`,

\[
 \frac{1}{\pi(X;M,b)}
 \sum_{\substack{3\le p\le X\\p\equiv b\pmod M}}
 H(V_1(p),\ldots,V_k(p))\longrightarrow
 \mathbb E H(L_1,\ldots,L_k).
 \tag{AP}
\]

The limit is through all real `X→∞`; omission of `p=2` in the numerator is harmless. Equivalently in a dyad, the numerator divided by `N(x)` tends to `E H/φ(M)`. Every parameter `M,b,k,H` is fixed before the limit. In particular, for every fixed `0<θ<1/2`,

\[
 \frac{\#\{x<p\le2x:p\equiv b\ (M),\ P^+(p-1)>x^{1-\theta}\}}
 {N(x)}\longrightarrow\frac{-\log(1-\theta)}{\varphi(M)}.
 \tag{R}
\]

**Theorem A+ (candidate deduction).** For every integer `a` with `|a|≥2` that is not a positive integer square, there exist constants `c_a>0` and `x_a` such that for every real `x≥x_a`,

\[
 \#\{x<p\le2x:p\nmid a,\ \operatorname{ord}_p(a)=p-1\}
 \ge c_a N(x).
 \tag{A+}
\]

Consequently the cumulative relative lower density is positive. Negative squares and odd perfect powers are included. Neither theorem requires a new unproved distributional hypothesis beyond the accepted pinned corpus and its classical inputs.

The round 2 repair is used exactly: retain a union of small-prime-avoiding classes of mass `w(Y) ≍_a 1/log Y`; get reservoir mass `c(θ)w(Y)`; subtract a **global** Kummer tail `O_a(1/Y)`; choose `Y` and hence the modulus once, then take `x→∞`. This avoids both rejected moves: a single exponentially sparse class, and treating a prescribed nonidentity cyclotomic Frobenius as complete splitting in a compositum.

Marginal PD alone cannot prove (AP): an abstract PD partition can be coupled with an equidistributed finite label so that a small PD event avoids one label completely. Equal label frequencies and the correct marginal partition law survive. Our proof adds genuine joint information from lower-level analytic contracts.

## 2. Exact manuscript contracts and companion checks

The source directory is `frontier/sources/i03_arithmetic_progressions/`. Its `manifest.json` records complete pinned raw URLs, SHA-256 and Git blob hashes for all 59 inherited manuscript files, independently checked against the untruncated `sources/preprints-tree.json`, plus the separately fetched pinned PD bibliography and external primary sources. `collect.py` reproduces those checks. The source prefixes below mean:

- **D**: `preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/`.
- **S**: `preprints/Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/build/`.
- **P**: `preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/build/`.
- **T**: `preprints/Simultaneous-primitive-roots-a-conditional-lower-bound-for-prime-bases-October-4-2026/build/`.
- **E**: `preprints/Prime-Predecessors-with-an-Even-Number-of-Prime-Factors-September-17-2026/build/`.

For example the exact URL of the principal analytic source is
[the pinned two-sided correlation section](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/sections/06-correlations.tex).

For the four interfaces closest to the new proof, the SHA-256 hashes are:

- D `sections/06-correlations.tex`: `09d0d46506b82c0cc8c0f04d5c4ff39abe9b6699b7ab04078e73f759d6c46f1d` (Git blob `142bd62088b1471bc321c183129d4000a1476821`).
- D `sections/07-extraction.tex`: `975713ca85a0318b26b17886afae993052bf3525bb020b3498f5cbf04c835f49`.
- S `sections/02-transference.tex`: `c506e0d2f6323aa70916f69e76123492e0fbdafc00aa1a7e8578f36ebae09265`.
- P `sections/08-type-ii.tex`: `97b1d9b0456a5951a25bbd9ee297da2c275a9c63e202aef139ad63e2c834794e`.

### 2.1 What is accepted, and what is not silently extended

D `sections/02-preliminaries.tex`, `lem:prime-estimates`, includes fixed-modulus Siegel–Walfisz with arbitrary logarithmic precision, reciprocal prime sums, Mertens products, and PNT. `lem:moment-bounds` gives coefficient-independent Dirichlet mean squares and fixed divisor moments. `lem:long-prime` and `lem:log-phase` allow character/rational moduli bounded by any fixed power of `log x`; the latter allows nonunit residue classes. The actual proofs and ranges are in D `sections/09-long-prime-appendix.tex`.

D `sections/03-determinant.tex`, `thm:type-II`, requires an invariant `F(ph)=F(h)` at every inert band prime and has a specific untwisted prime-minus-rough coefficient. It therefore cannot immediately absorb a progression indicator into `F`. D `sections/05-major-arcs.tex`, `maj:long-coefficient`, bounds that coefficient against **every** Dirichlet character of logarithmic modulus, including principal and imprimitive characters. P `sections/08-type-ii.tex`, `lem:marked-coefficient-transfer`, explicitly states the more general scalar-coefficient criterion: rough support, bounded coefficients, and those scalar bounds imply the same marked estimate. We use this accepted criterion in §4; no new determinant/memory estimate is postulated.

D `sections/06-correlations.tex`, `thm:two-sided`, requires `G(n)=G(n_*)`, where `n_*` removes all active prime powers. An indicator `1_{n≡b (M)}` generally violates this: for `M=3,b=1,n=1` and active prime `5`, its values at `n` and `5n` differ. The theorem itself does **not** supply a progression version.

The broader contracts in that same section are decisive:

1. `prop:graph-transfer` bounds physical pairings for any first vector independent of its selected mark lists, with the stated supremum and norm bounds. Dependence on the integer position is permitted. S `sections/02-transference.tex`, `thm:transference`, `cor:transference-pairing`, and `lem:physical-schur` give the original statements. In particular, multiplying a first vector by a residue indicator in its **position** preserves mark independence. No invariance under prime multiplication is required by this pairing corollary.
2. `prop:ideal-family` supplies the raw pattern and comparison patterns. In a small group **all `J` padding labels are shared**. In a big group at most a fixed number of probe labels are freed. The kernels do not depend on any shared labels. Their total supremum mass is a fixed log power, independent of the later fixed padding choice `J`.
3. `cor:stripping-normalization` and `cor:stripped` identify precisely the divisor shift after shared labels are removed: `n=D_R w`, `n'=D_R(w+D_C)`. The factor `1/n` changes the shared-label sum into the probability measure `∏ dp/(V_gp)`. The cutoff becomes `Ψ(w/(xD_C))`, which is independent of `D_R`. This exact cancellation, not an informal fixed-shift analogy, is used below.
4. The comparison Fourier multiplier estimate `cor:bilinear-multiplier` allows arbitrary bounded separate tests on the two free products. Its minor-arc conclusion uses only their squared coefficient norms.
5. The first comparison endpoint has the form `cor:U-form`. Its local energy bound `cor:arc-energy-target` is proved using `lem:local-mellin`, `lem:divisor-model`, `cor:low-main-term`, `cor:SM`, `cor:long-prime-saving` and `cor:constant-high`. These estimates are uniform at rational denominators up to any prescribed fixed log power. We explain precisely in §3.4 why fixed periodic restrictions preserve this bound.

We accept these statements and use their exact interfaces; we do not re-audit their underlying moment or long-prime proofs.

### 2.2 Companion limits and duplication

S's final lifted-shift theorem imposes its own invariant convolutional endpoint form, and proves thin smooth-predecessor reservoirs. It is not (AP). Its **general pairing corollary**, rather than its restricted final correlation theorem, permits the new physical residues.

T `sections/04-marked-family.tex`, `lem:twisted-rough-type-ii`, already multiplies scalar coefficients by a fixed character, enlarging modulus `k` to `lcm(k,M)`. It then uses `eq:product-progression`. This is prior art **inside the corpus** for §4's character argument. T's constructed family also requires an odd squarefree modulus and `(b(b−1),M)=1` for its particular prime-cofactor construction. Those hypotheses are not imposed in our §3: the source residue of the graph can be a nonunit. T's final count is of order `x/log²x`.

E `sections/03-shifted.tex`, `sh:correlation`, allows the same real completely multiplicative parity sign at both endpoints; that sign cancels on a shared product. It does not state arbitrary AP conditioning. Neither a single Dirichlet twist on the whole second endpoint nor a one-endpoint residue insertion has that cancellation property. E is not a duplicate of the two-residue calculation below.

P `sections/01a-reduction.tex`, `alg:quadratic-progression`, and `sections/07-splitting.tex`, `spl:field-bounds`, `spl:smooth-estimate`, supply the arithmetic part of §7. The broader all-`q` inequality was already derived correctly in round 2 and is restated with quantifiers there.

## 3. New analytic lemma: restrict both physical endpoints before stripping

This section closes the previously missing estimate. It does not assume (AP).

### 3.1 Restricted two-sided statement

Use all notation and hypotheses of D `thm:two-sided`: fixed `d,ε`, distinct long prime slots with lower endpoints at least `x^ε` and product of upper endpoints at most `x^(1−ε)`; a fixed inert marking array `𝒲`; `F_x(w)=𝒲(w)(f_x(w)−C_x)`; active small groups in `[exp(L^.27),exp(L^.36)]`, big groups in `[exp(L^.39),exp(L^.46)]`, disjoint with harmonic masses in a fixed positive compact interval and each kind numbering between fixed positive multiples of `log L`; fixed damping `0<q_0<1`; and an invariant core `G(n)=G(n_*)`, `|G(n)|≤L^C τ(n_*)^C`. Big groups remain full prime intervals as in D.

**Add the following condition, sufficient for the extraction:** at least one small group is a full interval of primes. Its harmonic mass still has the same positive lower bound. All active sets selected in D §7 have this property, because all their candidate small groups are full intervals `[exp(y),exp(2y))`.

**Lemma RC.** For each fixed integer modulus `M≥1`, every residue `r mod M` (no unit assumption), every fixed smooth compactly supported `Ψ:(0,∞)→C`, and every fixed `A>0`,

\[
 \sum_{\substack{w\ge1\\w\equiv r\pmod M}}
 \frac{\Psi(w/x)}w F_x(w)G(w+1)W_1(w)W_1(w+1)
 \ll_{M,A,\mathrm{fixed\ data}}L^{-A}.
 \tag{RC}
\]

The bound is uniform over the admissible slots, active sets and cores with those fixed bounds. Constants and thresholds can depend on the inert arrays and `M`. In particular this claim does not quantify over a growing modulus. `M=1` is the source theorem; assume `M≥2` below.

### 3.2 Mixing of one shared prime label

For a full small prime interval `𝒫_g` as above and its probability law `μ_g(p)=1/(V_gp)`, for every fixed `B>0`,

\[
 \sup_{t\in(\mathbb Z/M\mathbb Z)^\times}
 \left|\sum_{p\in\mathcal P_g,\ p\equiv t\ (M)}\mu_g(p)
       -\frac1{\varphi(M)}\right|\ll_{M,B}L^{-B}.
 \tag{mix}
\]

Proof: partial summation of `lem:prime-estimates`, with its arbitrarily large fixed accuracy at the actual prime scale, gives an error `O((log P_min)^(1−A_0))` for the harmonic interval sum. Here `log P_min≥L^.27`; choose `A_0>1+B/.27`. The main term in each class is `1/φ(M)` times the total main term. Dividing by `V_g≥v_->0` proves (mix), after increasing accuracy. This is valid uniformly for those intervals, not only for a special band. No growing-modulus PNT is needed.

In every comparison pattern all `J` padding slots of this small group are shared, and `J≥1` is fixed. Temporarily remove the shared-label collision bans exactly as in D `cor:shared-collision`. Condition on all shared labels except one in this group and on every unshared/free label. Multiplication by the remaining shared product permutes the units modulo `M`. Thus (mix) makes `D_R mod M` uniform with error `O_{M,B}(L^−B)`, **uniformly in that conditioning**. Restoring collisions has the source's `L^{O(J)} exp(−cL^.27)` error. The point is a uniform conditional bound in the independent-label model, not a claim of independence after arithmetic restrictions.

### 3.3 Physical pairing and the exact residue identity

Take the source's physical endpoint vectors, including their extra half-damping, and multiply the first by `1_{n≡r (M)}` and the second by `1_{n'≡r+1 (M)}`. These are position-dependent, mark-independent multipliers of modulus at most one. The supremum and physical `L²` bounds `cor:list-norm` are unchanged. The exponent in those bounds is independent of `J` and the probe count. Therefore `prop:graph-transfer` and `prop:ideal-family`, with the same Mellin separation of `Ψ(n/(xD))/n`, bound the modified **whole residual pairing** by any desired fixed negative log power. No individual signed comparison has been bounded by positivity here.

In a pattern strip the shared product: `n=D_Rw`, `n'=D_R(w+D_C)`. The invariant cores and marks strip as in the source. The new multiplier is exactly

\[
 \mathbf1_{D_Rw\equiv r\ (M)}
 \mathbf1_{D_R(w+D_C)\equiv r+1\ (M)}.
 \tag{physical-residues}
\]

Every active prime exceeds `M` for sufficiently large `x`, so both `D_R` and `D_C` are units modulo `M`. For any unit `d`, **every** `r,w mod M`,

\[
 \frac1{\varphi(M)}\sum_{t\in(\mathbb Z/M\mathbb Z)^\times}
 \mathbf1_{tw\equiv r}\mathbf1_{t(w+d)\equiv r+1}
 =\frac1{\varphi(M)}\mathbf1_{w\equiv rd\ (M)}.
 \tag{orbit}
\]

Indeed subtracting the two congruences forces `td≡1`, hence the unique `t=d^−1`; the first is then precisely `w≡rd`. This proof never divides by `w`, `r`, or `r+1`.

Average (physical-residues) over shared labels using (mix). After summing the other labels and integer positions, its error remains `O_A(L^−A)`: the kernels have total supremum mass `L^{C_1}`, both remaining marked factors have fixed log-power bounds, and `G` has a fixed divisor-power bound. On each `w≍xD_C` range, the corresponding absolute harmonic sum is `L^{O(1)}` by a fixed divisor moment. Choose the accuracy `B` in (mix) after these fixed exponents and `A`. Collision errors remain negligible under the residue multipliers since their absolute values are at most one. Insertion and removal of physical dyadic partitions do not change (orbit); after their sum the cutoff is exactly `Ψ(w/(xD_C))` and has no `D_R` dependence.

The raw pattern has `D_C=1`, so its contribution is exactly `1/φ(M)` times the left-hand side of (RC), up to the stated negligible errors. Each comparison is `1/φ(M)` times the source expression `cor:stripped`, with the extra condition

\[
 w\equiv rD_C\pmod M.
 \tag{comparison-residue}
\]

This is why two endpoint restrictions are needed. Restricting only `n` would average over its multiplicative orbit and lose the desired class. For example at `M=5,r=2,w=1` the one-endpoint averaged indicator is `1/4`, whereas `1_{w≡r}=0`.

### 3.4 Comparison cancellation with the new residue condition

Expand the source comparison kernels into separated tests on two free products `D_A,D_B`, so `D_C=D_AD_B`. They have scales `U_1,U_2`, with `H'=U_1U_2`, `Y=xH'`, and each `U_i≥exp(L^.39−O(1))`. Split each free product into its `φ(M)` possible unit classes `α,β`. Then (comparison-residue) is simply `w≡rαβ (M)`.

For each such pair, the separate tests on `D_A,D_B` are multiplied by their residue indicators. They still have modulus at most one. The source bilinear multiplier proof uses arbitrary such tests and their coefficient `L²` norms, so its bound is unchanged. The second endpoint is unchanged. The first endpoint becomes

`𝒰_s(w)=1_{w≡s (M)} 𝒰(w)`, where `s=rαβ` and `𝒰` has the exact source form `cor:U-form`.

Here is a direct proof that this modification preserves the required local energy, rather than an assertion that twists are harmless. With `e(t)=exp(2πit)` and the source Fourier convention,

\[
 \widehat{\mathcal U_s}(\xi)
 =\frac1M\sum_{j=0}^{M-1}e(-js/M)
                 \widehat{\mathcal U}(\xi+j/M).
 \tag{Fourier}
\]

Consequently for an arc at `h/k`,

\[
 \int_{|\beta|\le H^{-1}}
       |\widehat{\mathcal U_s}(h/k+\beta)|^2d\beta
 \le\frac1M\sum_{j<M}
 \int_{|\beta|\le H^{-1}}
       |\widehat{\mathcal U}(h/k+j/M+\beta)|^2d\beta.
 \tag{energy}
\]

Every shifted center has reduced denominator at most `Mk`. If the multiplier major arcs use denominator bound `L^C`, then `Mk≤L^{C+1}` eventually. Apply the **already proved** endpoint-energy estimate with that larger fixed exponent. Its arc width can be chosen `L^{C+1}/H'`, which contains the old width `1/H=L^C/H'`; its time cutoff is `xL^{C+2}` instead of `xL^{C+1}`, still within the arbitrary fixed-log-power range of `cor:SM`. The necessary inequalities remain `H≫LP_s` and `H=x^{o(1)}`, since `H'≥exp(2L^.39−O(1))` and the small mark is at most `exp(L^.36)`. Thus every summand in (energy) is `O_{A'}(YL^−A')` for arbitrary fixed `A'`. The factor `M` is fixed. Residues `s` need not be units.

For completeness the input here truly is local energy, not just the final unconditioned correlation: D's low-frequency proof `cor:low-main-term` sums **all** classes modulo the rational denominator and its main term is independent of the long tuple except for `1/l`. Its high-frequency proof explicitly retains residue restrictions, using character orthogonality only for the prime factors that are units, and `lem:log-phase` on arbitrary classes for the constant term. Hence increasing the fixed denominator exponent uses the original stated ranges. No new assertion at a frequency or modulus outside those ranges is made.

Parseval and the unchanged second-endpoint energy handle multiplier minor arcs, exactly as in D; (energy) handles the major arcs. Each comparison therefore saves every prescribed log power after all fixed pattern costs. Summing the finite `φ(M)^2` residue splits, subtracting comparisons from the transferred residual estimate, and multiplying by the fixed `φ(M)` proves (RC).

**Parameter order:** fix `M`, slot data, inert arrays, active-group bounds, core bound, `Ψ`, and target `A`; choose the transfer precision and residual family; choose sufficiently large fixed `J`; choose shared-label mixing precision and endpoint-energy precision to exceed the resulting fixed polynomial costs; then let `x→∞`. No `J`, `M`, number of inert arrays, or analytic accuracy in this new argument depends on the tending variable. This is the fixed padding parameter of the two-sided graph, distinct from the growing determinant parameter internal to the accepted one-sided Type II proof.

## 4. Fixed character twists in the one-sided prime replacement

Here we use an existing broader contract, P `lem:marked-coefficient-transfer`, rather than claim a new memory argument.

Fix a Dirichlet character `χ_0 mod M`, with zero extension on nonunits, and set on the permitted `m` interval

\[
 \alpha_m=\chi_0(m)m^{iv}
 \left(\mathbf1_{m\ {
m prime}}
 -\frac{\mathbf1_{P^-(m)>W}}{V(W)\log m}\right),
 \qquad |v|\le L^C.
\]

For any test character `χ mod k`, `k≤L^{A_0}`, the product `χ_0χ` is a possibly imprimitive character modulo `lcm(M,k)≤L^{A_0+1}` for sufficiently large `x`. Both zero extensions agree: a nonunit for either modulus is a nonunit for the least common multiple. D `maj:long-coefficient`, applied with exponent `A_0+1`, gives the scalar criterion for this `α`, for every fixed accuracy and the whole frequency range `|t|≤2XL^B`. Conjugates are covered by the same lemma. Rough support and size bounds are unchanged, since `H_m≥x^δ>W` and `W>M` eventually. P's coefficient-transfer lemma now proves the same Type II estimate with this `α` and any allowed `β`.

The scalar bounds do not depend on the number or exponents of inert bands, since `W` is defined from `x` alone. This matters: first fix the common coefficient precision, then choose sufficient fixed `K`, independent of the later choice of band exponents. T's fixed-character lemma uses exactly this order of choices for a different rough coefficient; we do not count this twisting device as new.

For a reduced class `b mod M`, use the identity

\[
 \mathbf1_{mn\equiv b\ (M)}
 =\frac1{\varphi(M)}\sum_{\chi_0\bmod M}
       \overline{\chi_0(b)}\chi_0(m)\chi_0(n).
 \tag{char}
\]

It is valid even when a factor is a nonunit, as both sides then vanish. Thus during composite telescoping put `χ_0(m)` into `α`, `χ_0(n)` into `β`; leave `F(mn−1)` invariant. In particular we never pretend the indicator in the predecessor is itself invariant.

## 5. Progression version of the entire extraction, with each change explicit

Fix `M,b` reduced, long-prime slot data `d,ε`, and a nonnegative smooth compactly supported `Φ`. Let `f_x,C_x` be exactly D `ext:statistic`. We prove

\[
 \sum_{p\equiv b\ (M)}\Phi((p-1)/x)
             (f_x(p-1)-C_x)=o(x/L).
 \tag{I-AP}
\]

### 5.1 The elementary progression remainder

Insert `u+1≡b (M)` into D `lem:progressions`. For a sieve divisor `r` with `(r,M)>1` the sum is zero, since `r|u+1` and `(b,M)=1`. For `(r,M)=1` the new main term is

\[
 \frac{x}{Mr}\left(\int\Phi\right)C_x M_x(H).
 \tag{CRT-main}
\]

To verify this, fix a long-prime tuple of product `l` and a divisor-model term `d'`. For sufficiently large `x`, `(ld',M)=1` because every prime in either product tends to infinity. Also `(l,r)=1`, since `r≤x^{c_0}` and each slot prime exceeds `x^ε`, with fixed `0<c_0<ε/2`. If `(d',r)>1` there is no solution; otherwise writing `u=ld'v`, the two congruences fix one residue of `v mod Mr`. Smooth counting gives `x/(Mrl d') ∫Φ+O_{M,Φ}(1)`. The original truncated-divisor reciprocal mass, factorial tail, and rounding bounds are unchanged up to fixed constants; the total rounding error remains `x^{1−ε+c_0+o(1)}`. The band primes dividing `r` are still forced absent, with the same `L exp(−L^.1)` comparison error. No band prime divides fixed `M` eventually. This proves the summed remainder `O_{M,A}(xL^−A)` with the stated main term, also without `f_x`.

### 5.2 Presieve and its surviving error

Fix the original even sieve depth `h`, put `γ=c_0/(4h+3)`, `z=x^γ`, and sieve only by primes not dividing `M`: the other primes cannot divide `u+1` in this class. The density at each remaining sieve prime is `1/q`. Since eventually `z>M`,

\[
 \frac1M\prod_{q\le z,\ q\nmid M}(1-1/q)
 =\frac1{\varphi(M)}\prod_{q\le z}(1-1/q).
\]

Apply the source block sieve separately to nonnegative weights `Φ𝒲f_x` and `Φ𝒲`, restricted to the class. The centered main terms cancel, and the surviving normalized error is at most

\[
 \limsup_{x\to\infty}\frac L{x,m_{\mathcal W}}
 \left|\sum_{\substack{u+1\equiv b\ (M)\\P^-(u+1)>z}}
 \Phi(u/x)\mathcal W(u)(f_x(u)-C_x)\right|
 \le C_M\frac{e^{-h}}\gamma.
 \tag{presieve-AP}
\]

The constant here is independent of `K,h` and of the particular fixed inert array; dependence on the fixed slot/cutoff data and `M` is allowed. This follows from the same model bounds as D: the only new main-term multiplier is `1/φ(M)`; remainders vanish for each fixed choice.

### 5.3 Composite replacement and the point where (RC) is indispensable

A presieved composite has between 2 and a fixed `O(1/γ)` prime factors, all greater than `z`. Discard repeated large factors using the source integer square-exception bound. All losses are bounded absolutely, so restriction to our class can only reduce them.

For each fixed factorization length, telescope prime slots to the source proxy `a(m)=1_{m>z}1_{P^-(m)>W}/(V(W)log m)`. Use (char) and §4 in each telescope. The other-factor coefficient is still rough, with the same fixed divisor-power bound; multiplication by a character preserves its truncation and norm bounds. The smooth logarithmic Fourier separation, `O(L²)` dyadic boxes, tail removal, clipping of `f_x−C_x` to an invariant bounded function, and the arbitrary interval restrictions have exactly the source hypotheses. The finite character sum costs a fixed constant. Choose `K` after these losses and after `h,γ`, but independently of the band exponents.

The replacement is the source proxy-factorization sum with the **unchanged external condition** `m_1⋯m_j≡b (M)`. Strip candidate prime parts from the threshold and logarithm, construct candidate groups, discard failures of the auxiliary coin partition, and expand retained successes as in D `ext:stripped-coefficient` through `ext:active-term`. Every error at these stages is an absolute weighted error `o(x/L)` over all integers/tuples. Multiplication by a residue indicator of modulus at most one preserves it. The earlier qualitative discarded error is not multiplied by the later polynomial number of terms.

Fix an expanded active set. All its small groups are full intervals, so it meets the extra assumption of (RC). When the active primes of `v=m_1⋯m_j` are allocated among the factors, the indicator `1_{v≡b (M)}` is the same for **every allocation**, as the product `v` itself does not change. Thus the exact source identity

\[
 j^{\omega_P(v)}(q_0/j)^{\omega_P(v)-s_P}
 =j^{s_P}q_0^{\omega_P(v)-s_P}
\]

still yields the invariant core `G_P(v)` of `ext:allocation-core`. The residue restriction remains **outside** this core. After square exceptions have been restored with the original negligible bound, the term to estimate is exactly

\[
 \sum_{u+1\equiv b\ (M)}\Phi(u/x)F_x(u)
                 W_1(u)W_1(u+1)G_P(u+1).
\]

Apply (RC) with residue `r=b−1` and `Ψ(t)=tΦ(t)`, multiplying its result by `x`. This gives `O_A(xL^−A)` for every fixed accuracy. Its invariant-core condition is precisely the source's `G_P(v)=G_P(v_*)`; its growth bound is `ext:core-bound`. Choose accuracy after the polynomial number and size of active-set terms, then sum. This proves that the entire composite contribution in (presieve-AP) is `o(x/L)`.

This step would fail with the original theorem alone: moving the indicator into `G_P` violates invariance. Section 3 supplies the missing estimate, rather than hiding the issue inside the word “adaptation.”

### 5.4 Removal of inert marks and order of limits

After subtracting composites, (presieve-AP) holds over primes in the class. For each fixed sufficient `K`, choose `B` disjoint inert arrays as in D and define its nonnegative square `Z_B=(B^−1 Σ_a𝒲_a/m_a−1)^2`. The source unconditioned upper bound `ext:prime-deweight-square` is already enough:

\[
 \limsup\frac Lx\sum_{p\equiv b\ (M)}\Phi((p-1)/x)Z_B(p-1)
 \le\limsup\frac Lx\sum_p\Phi((p-1)/x)Z_B(p-1)
 \ll C_K/B.
\]

The other Cauchy factor is `O((x/L)^(1/2))`, since `f_x−C_x` is uniformly bounded on the support and the class prime count is at most the total prime count. Averaging the weighted estimates therefore yields

\[
 \limsup_{x\to\infty}\frac Lx
 \left|\sum_{p\equiv b\ (M)}\Phi((p-1)/x)(f_x(p-1)-C_x)\right|
 \le C_M e^{-h}/\gamma+C\sqrt{C_K/B}.
\]

Fix `M` and the interior data; fix `h`, hence `γ` and all factorization lengths; fix a sufficient `K`; fix finitely many `B` arrays; take the real `x` limit; then let `B→∞`; finally take arbitrarily large fixed even `h`. Since `1/γ=(4h+3)/c_0`, the right side tends to zero. This proves (I-AP).

## 6. From the interior estimate to full fixed-progression PD

This passage uses the same probability argument as D §8, now with a verified conditional interior input; it does not assume conditional convergence from marginal convergence.

Choose `p` uniformly among class primes in `(x,2x]`. PNT in the fixed progression gives denominator `N_M(x)∼x/(φ(M)L)`. For every rectangle `∏(a_i,b_i]` with positive lower endpoints and `Σb_i<1`, choose the long slots `(x^{a_i},x^{b_i}]`. The reciprocal tuple sum tends to `∏log(b_i/a_i)`, with coincidences contributing `o(1)`. Equation (I-AP), smooth upper/lower cutoff approximation and fixed-progression PNT give that limit for the expected number of ordered distinct numerical prime-factor tuples.

Uniformly on the dyad `log(p−1)/log x=1+O(1/log x)`, so a fixed endpoint sandwich changes the normalization to `log(p−1)`. Multiplicity corrections on each compact interior set are negligible: a repeated tested prime entails `q²|p−1` with `q≥x^{a/2}`, and the integer upper bound `O(x^{1−a/2})` is still `o(N_M(x))` for fixed `M`. Hence for every compactly supported continuous test on the open simplex, the labelled-ball factorial measure converges to density `∏dt_i/t_i`.

The balls' masses sum to one exactly. Size-biased sampling without replacement multiplies this factorial density by `∏ t_i/(1−t_1−⋯−t_{i−1})`, yielding density `∏(1−t_1−⋯−t_{i−1})^−1`. The triangular change of variables `A_i=t_i/(1−Σ_{j<i}t_j)` identifies it with uniform measure on `(0,1)^d`, of total mass one. Compact interior exhaustion therefore excludes all escaped boundary mass. The first `d` size-biased draws converge jointly to independent-uniform stick fragments, and their expected unseen mass tends to `2^−d`.

Sorting the first `d` draws and padding zeros approximates each ranked coordinate within the unseen mass. Uniform continuity, Markov's inequality, and then `d→∞` give every finite ranked joint law. This proves the dyadic form of (AP). A finite dyadic decomposition of `(X/2^J,X]` and fixed-progression PNT give the cumulative form after first `X→∞`, then `J→∞`. The discarded class-prime proportion tends to `2^−J`.

For (R), the largest PD(1) part has density `1/t` on `1/2<t<1`, so its tail above `1−θ` is `c(θ)=−log(1−θ)`. The same denominator sandwich handles the threshold `x^(1−θ)`. This also follows by using one-point interior intensities up to `1−ε` and the just-proved absence of boundary mass. No convergence rate is extracted.

## 7. Positive-proportion primitive roots: full arithmetic reduction

Fix an admissible `a`; put `δ=10^−6` and choose any one fixed `0<θ<δ`, for example `θ=δ/2`. The accepted Kummer-field lemmas give constants `C_a,q_0(a)` such that for **all** primes `q≥q_0(a)` and **all** real `x≥2`,

\[
 \#\{x<p\le2x:p\text{ splits completely in }K_q\}
 \le C_a\left(\frac{x}{q(q-1)\log x}
       +\frac{x^{1-\delta}\log(2q)}{\log x}\right),
 \quad K_q=\mathbb Q(\mu_q,a^{1/q}).
 \tag{S}
\]

This is P `spl:field-bounds` plus `spl:smooth-estimate`, not the final proposition restricted to `q≤exp(L^.3)`. The field degree is `q(q−1)` for sufficiently large `q` depending on `a`; small degree-drop primes for perfect powers are below `q_0(a)`. The ratio `(log D_q+[K_q:Q])/[K_q:Q]≪_a log(2q)` gives precisely (S). Round 2 supplies the complete descent and uniformity proof; no conditioned splitting estimate is used here.

From P `alg:quadratic-progression`, choose

`M_0=8∏_{odd ℓ|a}ℓ`

and a reduced `u_0 mod M_0` such that `(a/p)=−1` throughout the class and `u_0≠1 mod ℓ` for every odd `ℓ|M_0`. This lemma includes negative squares and odd perfect powers. For fixed integer `Y` above `q_0(a)` and every prime factor of `M_0`, put

\[
 M_Y=M_0\prod_{\substack{3\le q\le Y\\q\nmid M_0}}q,
 \qquad
 R_Y=\{p:p\equiv u_0\ (M_0),\ p\not\equiv1\ (q)
        \text{ for each newly adjoined }q\}.
\]

For primes above `Y`, this is a union of reduced classes with density

\[
 w(Y)=\frac1{\varphi(M_0)}
       \prod_{\substack{3\le q\le Y\\q\nmid M_0}}
                  \frac{q-2}{q-1}\asymp_a\frac1{\log Y}.
 \tag{w}
\]

The comparison of its factors to Mertens' product is exact:
`[(q−2)/(q−1)]/(1−1/q)=1−1/(q−1)^2`; the product of these latter factors over odd primes converges to a positive number. CRT gives (w) without any independence assumption on Kummer fields.

Let `𝒢(x)={x<p≤2x:P⁺(p−1)>x^(1−θ)}`. For **each fixed** `Y`, summing (R) over the finitely many classes gives

\[
 \#(\mathcal G(x)\cap R_Y)/N(x)\longrightarrow c(\theta)w(Y).
 \tag{reservoir}
\]

Write on this set `p−1=mQ`, where `Q=P⁺(p−1)>x^(1−θ)` and `m<2x^θ`. For sufficiently large `x`, `Q>m`, so `Q` occurs once. If `Q|i_p(a)`, then `ord_p(a)|m`; hence `p` divides one of the nonzero integers `a^j−1`, `j≤ceil(2x^θ)`. The logarithm of their absolute product is `O_a(x^{2θ})`. Its number of distinct prime divisors greater than `x` is `O_a(x^{2θ}/log x)=o(N(x))`, since `2θ<1`.

Any other prime divisor `q` of `i_p(a)` divides `m`. No `q≤Y` is possible: quadratic nonresiduosity excludes 2, and the class construction gives `q∤p−1` for every odd `q≤Y`. For `Y<q<2x^θ`, divisibility of the index is equivalent to complete splitting in `K_q`, by P `alg:splitting-test` after excluding `p|a`. Summing the global estimate (S) and enlarging the prime sum to integers gives

\[
 \#\{x<p\le2x:\exists,Y<q<2x^\theta,\ q\mid i_p(a)\}
 \le \frac{C_a}{Y}\frac{x}{\log x}
       +O_a(x^{1-\delta+\theta})
 =\left(\frac{C_a}{Y}+o(1)\right)N(x).
\]

Here `Σ_{n>Y}1/[n(n−1)]=1/Y`, and the summed error saves a power because `θ<δ`. The constants can be enlarged once to cover endpoints. There is no growing-fixed-modulus invocation.

Now choose a fixed sufficiently large `Y` such that `C_a/Y<c(θ)w(Y)/4`, possible by (w). **Fix this `Y` and `M_Y` before sending `x` to infinity.** The reservoir eventually has at least `(7/8)c(θ)w(Y)N(x)` members. The middle exception eventually has at most `(3/8)c(θ)w(Y)N(x)` members, and the `Q` and finitely many excluded-prime exceptions together at most `(1/8)c(θ)w(Y)N(x)`. At least `(3/8)c(θ)w(Y)N(x)` remain, all with index exactly one. Thus the safe choice `c_a=c(θ)w(Y)/4` proves (A+) after increasing `x_a`.

For the cumulative lower density, sum the dyadic bound over all dyads contained in `[x_a,X]`; they cover all but a bounded initial interval. The relative omitted prime mass tends to zero, so the same positive lower bound holds cumulatively. No equality or limiting density is asserted.

## 8. Local obstructions, unsuccessful shortcuts, and finite falsification attempts

1. **One-sided conditioning is false as an algebraic replacement.** The noninvariant-core example in §2 and the one-endpoint orbit average in §3.3 are explicit failures. Using two endpoint residues repairs the exact lost information. Neither example contradicts (AP).
2. **Nonunit predecessor residues must be retained.** For odd primes in many classes, `p−1` is necessarily divisible by a prime of `M`. Our proof does not use multiplicative characters on `w` to recover its class. Formula (orbit) uses only invertibility of the shared/free dilation; formula (Fourier) is additive. The proof therefore includes `p≡1 (M)`, prime-power moduli, and `r=0`.
3. **Unrestricted small groups would be a gap.** D allows arbitrary sets as small groups. A small set containing only primes in one class need not satisfy (mix). Lemma RC explicitly requires a full prime interval in a small group. Extraction supplies many such groups. We do not claim the unrestricted-group version of RC.
4. **Periodicity may not be put into a kernel after the fact.** Doing so could invalidate its ideal norm. We keep the ideal family unchanged and use permitted physical endpoint vectors; only after accepted transference and exact stripping do we compute the residue multiplier.
5. **Fixed local factors are not PD-scale obstructions.** A class can force, for example, a fixed power of 2 into `p−1`, but its logarithmic mass tends to zero. The proof of §6 establishes this compatibility through conditional factorial intensities, rather than assuming it.
6. **PD independence is not Kummer independence.** For example, the reduced class `p≡1 mod5` forces `(5/p)=1` for `p≠5`; hence 5 is never a primitive root there despite (AP). This is an actual local-entanglement obstruction to a stronger false claim about every progression. The class construction in §7 explicitly chooses `(a/p)=−1`. Odd perfect-power obstructions are excluded by `p≠1 (q)` when needed. Intersections among higher Kummer fields are irrelevant to the global union upper bound.
7. **A union is essential to this quantitative budget.** A single class has mass `1/φ(M_Y)`, which can be much smaller than `1/Y`. Full PD on the union yields the explicit common factor `c(θ)`, with `w(Y)≍1/log Y`. Mere unspecified progression positivity would still not close the argument.

Reproduction: `python3 frontier/experiments/i03_arithmetic_progressions/check.py` (Python standard library only). Results are in the adjacent `results.json`:

- Exhaustively checked (orbit) for all `2≤M≤48`, all unit free shifts and all source residues/positions: **833,272 cases**, including **243,782 nonunit-source cases**, zero failures.
- Checked that a uniform unit factor times an arbitrary independent unit factor is uniform, in exact rational arithmetic, for 63 moduli `2≤M≤64`.
- Checked (Fourier) for 1,392 finite-array/rational-frequency cases; maximum absolute floating error `4.08×10^−13`.
- Constructed the quadratic-nonresidue/odd-prime-avoidance class for all 189 admissible signed bases between −100 and 100 and checked 18,488 prime instances below 20,000; zero failures. This includes negative squares and nontrivial perfect powers.
- Verified the local entanglement example for 306 primes `p≡1 mod5` below 10,000, and exact CRT union densities for small cutoffs through `Y=13` for the base-2 starting class.

These are checks of finite algebra, local compatibility, and implementation. They do **not** test transference, Type II cancellation, PD asymptotics, the tiny exponent `θ<10^−6`, or novelty. No empirical PD convergence is used as evidence for the theorem.

## 9. Primary prior art, significance, and novelty limits

Searches were run before formulating the new lifting argument and repeated after the statement/proof had been settled. Search phrases and retrievals are in the adjacent source records. Only primary papers support mathematical comparisons; MathDB is used for the target description, not as a proof source.

- **Ford–Konyagin–Luca**, *Prime chains and Pratt trees*, §6, Conjecture 5, gives the marginal shifted-prime PD conjecture and notes its consequence from Elliott–Halberstam. This does not supply the required conditional law from a marginal theorem. [Author PDF](https://www.ford126.web.illinois.edu/wwwpapers/chains.pdf); SHA-256 `9021b40cc5c7b773c3436845944cd9c238b8a13f581bea13d1dda4fe33f0ff3d`.
- **Bharadwaj–Rodgers**, *Large prime factors of well-distributed sequences*, **v4, 9 April 2026**, Theorem 7 and Lemma 8, gives full PD under level-one well-distribution and restricted-support correlations at a positive level. Proposition 2 supplies level one half for shifted primes. Its largest-factor estimate is an upper bound, not this reservoir lower bound. The new argument above verifies full interior correlations in each fixed class using accepted graph inputs, without claiming level-one distribution for all divisor moduli. [Primary v4](https://arxiv.org/html/2402.11884v4); SHA-256 `8f23ca2775119016c759a6152f69bbeb9b586ecc3042b909dcf63e7f28ba33ad`. Earlier v3 has different theorem numbering/hypotheses and was not used for the final comparison.
- **Moree**, *On primes in arithmetic progression having a prescribed primitive root. II*, Theorem 1 gives the GRH conditional AP asymptotic following Lenstra; Theorems 2–4 exhibit the local/entanglement corrections and zero-density conditions. Those are stronger quantitative conclusions under a different unproved premise. They show why “all reduced classes admit primitive roots” is false. We claim only the global positive-lower-density statement (A+). [Primary v1](https://arxiv.org/pdf/0707.3062v1); SHA-256 `df40b522f1956e7fb73fc95c1d51b0440204904ff5eeb878ee314311d07e2468`.
- **Goldmakher–Martin–Péringuey**, *Refinements of Artin's primitive root conjecture*, v1, proves refined density assertions under GRH and weaker unconditional bounds. The round 2 reading of §8 correctly distinguishes unconditional upper bounds on small index events from the positive lower bound needed here; the cached primary manuscript was rechecked. [Primary v1](https://arxiv.org/html/2502.19601v1); SHA-256 `593a558413a27081cb3de4c6044bb9f126ff5c0831988e128e429faa7bdaeefd`.
- **Murty–Naik**, *A non-abelian large sieve and Artin's primitive root conjecture*, arXiv:2608.21573v1, was found in the second pass. Its Theorem 1 gives an `x/log²x` bound for base 2 under a proposed nonabelian large-sieve inequality, and Remark 1.1 extends its argument to other admissible bases; it also proves partial unconditional inequalities; it does not provide that full inequality unconditionally. It is a relevant alternative reduction, not an established duplicate of (A+) from the stipulated corpus. [Primary v1](https://arxiv.org/html/2608.21573v1); SHA-256 `40ae4cb4e9503c50fdffe87a9cd8560a71e639be8d2bf39ae623cb336e5d2e78`.

The located primary literature does not already give (AP) or (A+) unconditionally. This is targeted novelty evidence, not proof of global priority. In particular, “unconditional” here always means **relative to the user's accepted pinned corpus**. We do not assert that those accepted new upstream premises are established in the external literature.

Inside the corpus, the general graph transference, local Mellin energy, coefficient-transfer criterion, and small-index elimination all preexist. The round 2 reviewer already supplied the all-class reservoir-to-Artin reduction. We claim as new work only the explicit two-residue physical lifting calculation, its compatibility with comparison energy, and the complete fixed-progression extraction that these enable. The result strengthens the accepted `≫_a x/log²x` primitive-root count to `≫_a x/log x`, retaining index exactly one, as well as strengthening the marginal PD theorem to its fixed-progression form.

MathDB's currently retrieved [Artin page](https://mathdb.com/p/370026/artin-s-primitive-root-conjecture) records the infinitude formulation and the accepted corpus's weaker count, explicitly distinguishing it from a density formula. The previously cited `/p/316116/...` URL failed retrieval in this round. I did not freshly verify a “Celebrated” badge, numerical score, or global rank and do not inherit those claims as verified evidence. Positive lower density is a substantial strengthening of its stated infinitude target, but the exact density conjecture remains beyond this report.

## 10. Independent-review priorities and handoff

The main claim is a completed deduction offered for review, not a new conditional theorem whose missing hypothesis has been relabelled. The least routine and most important checks are:

1. In §3.3, verify that the general physical pairing contract indeed allows both position residues and that the insertion `Ψ(n/(xD))/n` leaves **no shared-label dependence in the cutoff** after division by `D_R`.
2. Verify (orbit), the conditional uniformity from one full small shared interval, and the absence of shared labels in each comparison kernel. The interval qualification in RC is essential.
3. Check the Fourier energy argument with `Mk` denominators and the slightly larger fixed-log-power window; it must be applied to the first comparison endpoint before the final correlation theorem, not inferred from the theorem's conclusion.
4. Check all extraction error estimates remain absolute until discarded masses have been removed; in particular the progression indicator stays outside the allocated invariant core.
5. Check `M` is fixed before every limit, then `Y` is chosen by the explicit `w(Y)` comparison. Nothing requires a rate uniform in the enormous resulting modulus.

No independent agent was invoked, in accordance with the assignment. Parent should obtain a fresh proof audit before promoting this candidate. If that audit finds a hidden restriction in the physical-pairing or first-endpoint-energy contracts, the fallback progress is still concrete: the exact missing estimate is (RC), with the explicit candidate construction (physical-residues) and reduction (orbit), not an unspecified “AP adaptation.” The corrected B finding is separate and was not edited.
