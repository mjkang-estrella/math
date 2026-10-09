# R006 — Fixed-progression Poisson–Dirichlet law and positive-proportion primitive roots

Date: 2026-10-08. **Validated substantial deduction under the user's accepted OpenAI corpus.** Pin: `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The full independent proof audit passes after editorial corrections. The separate final novelty/significance review supports a substantial, nonroutine improvement relative to those premises. The parent accepts that assessment; worldwide priority remains unverified.

The result improves the accepted corpus's primitive-root lower bound from order `x/log²x` to order `x/log x` for every admissible integer base. Its additional analytic argument proves the prime-predecessor Poisson–Dirichlet law inside each fixed reduced arithmetic progression. This is one finding: the progression theorem and its primitive-root consequence share the same new correlation estimate.

The [complete proof](../iterations/i03-arithmetic-progressions.md), [independent audit](../reviews/i03-arithmetic-progressions-r4.md), and [parent verification](../sources/i03_arithmetic_progressions_r4/parent-verification.json) are part of this record. The proof below summarizes the deduction while retaining its critical hypotheses and order of operations.

## 1. Exact conclusions

Let `N(x)=π(2x)−π(x)`. List the prime factors of `p−1` with multiplicity as `q₁(p)≥q₂(p)≥…`, padding by 1, and set `V_j(p)=log q_j(p)/log(p−1)` for `p≥3`. Let `(L_j)` be the decreasing PD(1) random partition.

**AP.** For every fixed integer `M≥1`, every reduced residue `b mod M`, every fixed `k≥1`, and every bounded continuous real function `H` on `[0,1]^k`,

\[
 \frac{1}{\pi(X;M,b)}
 \sum_{\substack{3\le p\le X\\p\equiv b\pmod M}}
 H(V_1(p),\ldots,V_k(p))
 \longrightarrow \mathbb E H(L_1,\ldots,L_k).
\]

The corresponding dyadic average divided by `N(x)` tends to `E H/φ(M)`. In particular, for every fixed `0<θ<1/2`,

\[
 \frac{\#\{x<p\le2x:p\equiv b\pmod M,
               \ P^+(p-1)>x^{1-\theta}\}}{N(x)}
 \longrightarrow \frac{c(\theta)}{\varphi(M)},
 \qquad c(\theta)=-\log(1-\theta).
 \tag{R}
\]

**A+.** For every integer `a` with `|a|≥2` that is not a positive integer square, there are constants `c_a>0` and `x_a` such that, for **every real** `x≥x_a`,

\[
 \#\{x<p\le2x:p\nmid a,\ \operatorname{ord}_p(a)=p-1\}
 \ge c_a N(x).
\]

Thus the same set has positive relative lower density among all primes. Negative squares and odd perfect powers are included. The base is fixed before the limit. No natural-density existence, exact Artin constant, effective threshold, growing-modulus uniformity, or simultaneous primitive-root assertion for arbitrary sets of bases is proved.

All conclusions use the accepted pinned corpus as premises. They are not assertions that those premises have been independently established in the external mathematical literature.

## 2. Accepted inputs and additional work

The source abbreviations are the following exact directories at the pin:

| Prefix | Directory below `preprints/` |
|---|---|
| D | `The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/` |
| S | `Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/build/` |
| P | `Primitive-roots-for-every-admissible-integer-base-October-4-2026/build/` |
| T | `Simultaneous-primitive-roots-a-conditional-lower-bound-for-prime-bases-October-4-2026/build/` |

The complete [source manifest](../sources/i03_arithmetic_progressions/manifest.json) and [independent verification](../sources/i03_arithmetic_progressions_r4/verification.json) identify immutable URLs and hashes. The decisive interfaces are:

- D [`sections/06-correlations.tex`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/sections/06-correlations.tex): `prop:graph-transfer`, `prop:ideal-family`, and the proof equations for insertion, stripping, shared collisions, multiplier bounds and local endpoint energy. The `cor:` prefixes on these equations do not make them separate corollaries.
- S [`sections/02-transference.tex`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/build/sections/02-transference.tex): `thm:transference`, `cor:transference-pairing`, `lem:physical-schur`. Mark independence is required at each fixed position; dependence on the position is allowed. S §3 supplies the ideal kernels.
- D §§2, 5 and 9: fixed-modulus prime estimates, arbitrary fixed logarithmic-modulus character estimates, divisor moments, and rational-frequency endpoint estimates including nonunit classes. D §§7–8 supply the extraction and probability arguments whose progression modifications are verified below.
- P [`sections/08-type-ii.tex`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/build/sections/08-type-ii.tex): `lem:marked-coefficient-transfer`. T §4 already contains the fixed-character/lcm device; that device is not claimed as new.
- P [`sections/01a-reduction.tex`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/build/sections/01a-reduction.tex): `alg:quadratic-progression`, `alg:splitting-test`; P [`sections/07-splitting.tex`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/build/sections/07-splitting.tex): `spl:field-bounds`, `spl:smooth-estimate`. The latter all-`q` contracts, not only the narrower final splitting proposition, give the required tail estimate.

Marginal PD does not imply AP: a finite equidistributed label can be coupled with a PD partition to exclude a particular event from one label. Nor may one put a progression indicator into D's invariant second-endpoint core. The additional work is the two-position residue insertion, shared-label calculation, its comparison-energy estimate, and full progression extraction. The union-of-classes arithmetic reduction was developed in the preceding round and is credited there.

## 3. Restricted correlation lemma and proof

Use the exact data of D `thm:two-sided`, with `L=log x`: fixed long-slot count and positive separation parameter ε, slot lower endpoints at least `x^ε` and product of upper endpoints at most `x^(1−ε)`; fixed inert marking array; centered marked first factor `F_x`; disjoint active small groups in `[exp(L^.27),exp(L^.36)]` and big groups in `[exp(L^.39),exp(L^.46)]`, each kind numbering between fixed positive multiples of `log L`; harmonic group masses in a fixed positive compact interval; fixed damping; and an invariant second core `G(n)=G(n_*)`, bounded by `L^C τ(n_*)^C`. Big groups are full prime intervals as in D. **Require in addition that at least one small group is a full prime interval.** Every active set in the extraction has this property.

For every fixed modulus `m≥1`, every residue `r mod m` including nonunits, every fixed smooth compactly supported `Ψ:(0,∞)→C`, and every fixed `A>0`, the additional lemma is

\[
 \sum_{\substack{w\ge1\\w\equiv r\pmod m}}
 \frac{\Psi(w/x)}w F_x(w)G(w+1)W_1(w)W_1(w+1)
 \ll_{m,A,\text{fixed data}}L^{-A}.
 \tag{RC}
\]

Here `n_*`, `W₁`, the inert arrays and their ranges are exactly those of D; [§3.1 of the full proof](../iterations/i03-arithmetic-progressions.md#31-restricted-two-sided-statement) records that source contract. Constants may depend on all fixed data and on `m`; there is no growing-modulus assertion.

**Physical insertion.** Multiply the source first endpoint by `1_(n≡r mod m)` and the second by `1_(n′≡r+1 mod m)`. At fixed position the first factor remains independent of selected marks, and both physical norms decrease. The general graph-pairing estimate therefore applies with the original ideal operator. It controls the entire signed residual pairing; individual comparisons still need estimates.

**Strip and reassemble before mixing.** In each pattern, let `D_R` be the shared product and `D_C` the free shift product. Then

`n=D_R w`, `n′=D_R(w+D_C)`,

`Ψ(n/(xD))/n = D_R⁻¹ Ψ(w/(xD_C))/w`, where `D=D_R D_C`.

The fixed-position dyadic cutoffs and full Mellin integral must first be reassembled. Individual dyads retain dependence on `D_R` and are not eligible for the averaging argument. After reassembly the cutoff has none. Invariance removes shared labels from the two cores, and the ideal kernels already exclude them. The factor `D_R⁻¹` changes each shared-label sum to its probability measure `1/(V_g p)`. Source collision exclusions may be removed and restored with an absolute exponentially small error times fixed logarithmic powers.

Condition on `w`, all free and unshared labels, and all but one shared label in the full small interval. Do not condition on either residue event. Fixed-modulus Siegel–Walfisz and partial summation make that last label uniform among units modulo `m` to arbitrary logarithmic precision. All active labels are eventually coprime to `m`. For every unit `d` and arbitrary `w,r mod m`,

\[
 \frac1{\varphi(m)}\sum_{t\in(\mathbb Z/m\mathbb Z)^\times}
 1_{tw\equiv r}\,1_{t(w+d)\equiv r+1}
 =\frac1{\varphi(m)}1_{w\equiv rd}.
 \tag{orbit}
\]

Subtracting the congruences forces `td=1`; no division by `w` or `r` is used. The raw pattern `D_C=1` gives RC divided by `φ(m)`. Comparisons acquire `w≡rD_C mod m`. Uniform mixing errors remain negligible after absolute divisor-moment and fixed pattern-mass bounds.

**Comparison estimates.** Write `D_C=D_A D_B` and split the free products into unit residues `α,β`, without renormalizing their measures. Separate coefficient norms do not increase. The first endpoint becomes `U_s(w)=1_(w≡s mod m)U(w)`, `s=rαβ`, with

\[
 \widehat U_s(\xi)=\frac1m\sum_{j<m}e(-js/m)\widehat U(\xi+j/m).
\]

Cauchy bounds its local Fourier energy by the average of the shifted original energies. A center with denominator `k≤L^C` shifts to denominator at most `mk≤L^(C+1)` eventually. Run D's endpoint-energy proof at this larger fixed exponent, with the wider window and time cutoff that it permits. The scale separation remains valid because the free products give `H′≥exp(2L^.39−O(1))`, while a small mark is at most `exp(L^.36)`. The required frequencies stay in the accepted ranges. The low-frequency divisor model and high-frequency log-phase bound both allow the necessary residues; the latter includes nonunits. The unchanged multiplier and Parseval bounds handle minor arcs. Every comparison saves any prescribed log power, after fixed costs. Subtracting these comparisons from the small whole residual proves RC.

## 4. Extraction to AP

The [full proof §§4–6](../iterations/i03-arithmetic-progressions.md#4-fixed-character-twists-in-the-one-sided-prime-replacement) verifies the following steps; the [audit §§5–7](../reviews/i03-arithmetic-progressions-r4.md) checks their estimates independently.

1. In the composite replacement, a fixed character modulo `M` multiplies the scalar coefficient, and any tested character then has modulus at most `lcm(M,k)`. This is still a fixed logarithmic range. P's marked-coefficient-transfer criterion applies; the invariant function is unchanged.
2. A sieve divisor sharing a prime with `M` is incompatible with a reduced class. Otherwise CRT supplies the factor `1/M`. Omitting sieve primes dividing `M` changes the model density to `1/φ(M)` times the original sieve product. The source divisor tails and rounding errors still save the required powers.
3. Square, threshold, logarithmic and failed-coin errors are bounded absolutely before the signed active-set expansion. In particular, a qualitative discarded error is removed before the later polynomial expansion cost. Allocating active primes preserves the total product, so the progression indicator remains outside the invariant core. Every active set has full small intervals. Apply RC with `r=b−1` and `Ψ(t)=tΦ(t)` to remove composites.
4. The original nonnegative square bound for removing inert marks upper-bounds the progression-restricted square. The final normalized limsup is bounded by `C_M e^(−h)/γ + C sqrt(C_K/B)`, where `γ=c₀/(4h+3)`. Fix `M`, interior data, even sieve depth `h`, sufficient `K`, and finitely many `B` arrays; take `x→∞`, then `B→∞`, then arbitrarily large fixed even `h`. This proves the progression interior factorial intensities.
5. Their density on the open simplex is `∏dt_i/t_i`. Size-biased sampling converts it to the probability density of GEM(1) stick fragments generated by independent uniforms. Its total mass is one, excluding lost boundary mass; expected unseen mass after `d` draws tends to `2^(−d)`. Sorting, then letting `d→∞`, proves all finite ranked PD laws. Fixed-progression PNT and dyadic summation give AP. The largest PD(1) part has density `1/t` on `(1/2,1)`, giving (R).

## 5. Deduction of positive-proportion primitive roots

Fix an admissible `a`, and put `δ=10⁻⁶` as in P. Choose fixed `0<θ<δ`, for example `θ=δ/2`. P's quadratic-progression lemma supplies a reduced class `u₀ mod M₀`, `M₀=8∏_(odd ℓ|a)ℓ`, on which `a` is a quadratic nonresidue and `u₀≠1 mod ℓ` for odd `ℓ|M₀`.

For fixed large `Y`, keep **all** reduced classes above this class that avoid 1 modulo every odd prime `q≤Y` outside `M₀`. Their total prime-density weight is

\[
 w(Y)=\frac1{\varphi(M_0)}
 \prod_{\substack{3\le q\le Y\\q\nmid M_0}}\frac{q-2}{q-1}
 \asymp_a\frac1{\log Y}.
\]

Apply (R) to this finite union, whose modulus is fixed. It gives `c(θ)w(Y)N(x)+o(N(x))` primes with `p−1=mQ`, `Q>x^(1−θ)`, `m<2x^θ`, and eventually `Q>m`.

Write `i_p(a)=(p−1)/ord_p(a)`. If `Q|i_p(a)`, then `ord_p(a)|m`; such primes divide `∏_(j≤ceil(2x^θ))|a^j−1|`. Its logarithm is `O_a(x^(2θ))`, so the number of its prime divisors exceeding `x` is `o(N(x))`. No index prime `q≤Y` is possible: the quadratic condition excludes 2 and the selected classes exclude every odd `q≤Y`.

For the remaining primes `Y<q<2x^θ`, P's splitting test and all-`q` field/smoothing bounds give the **global**, unconditioned bound

\[
 N_{a,q}(x)\le C_a\left(
 \frac{x}{q(q-1)\log x}
 +\frac{x^{1-\delta}\log(2q)}{\log x}\right).
\]

Summation bounds their union by `(C_a/Y+o(1))N(x)`, after enlarging `C_a`, because the total error is `O_a(x^(1−δ+θ))`. This is not a conditioned Chebotarev estimate. Choose `Y` once so large that `C_a/Y<c(θ)w(Y)/4`, possible since `w(Y)≍_a1/log Y`. Only then let `x→∞`. Subtracting all exceptions leaves a positive proportion with index exactly one; `c_a=c(θ)w(Y)/4` is a safe choice after increasing `x_a`. Dyadic summation proves the cumulative lower-density assertion.

## 6. Validation and limitations

The independent audit found no unresolved mathematical gap in `RC → interior AP → AP/(R) → A+`. Parent integration corrected a malformed normalization, equation-label descriptions, the GEM wording, and made the already-required dyadic reassembly explicit. No new analytic estimate was needed after review.

The parent reproduced the author's output byte for byte and the reviewer's independent exact tests:

| Check | Cases | Result |
|---|---:|---|
| Shared-label orbit identity, moduli through 96 | 12,950,254, including 4,054,120 nonunit cases | No failures |
| Rational weighted stripping and dyadic reassembly | 1,560 | Exact agreement; 1,558 individual-dyad models were biased |
| CRT model, including incompatible sieve moduli | 17,892 | No failures |
| Uniform conditional residue-law error | 717,544 | No failures |

All 60 cached pinned manuscript files and five literature downloads passed integrity checks; 12 independently re-downloaded interfaces matched the pin, and all 26 reviewer artifacts matched their recorded hashes before integration. These finite checks do not prove transference, asymptotics or novelty. Validation consists of the written source-based deduction and independent AI review; it is not external human peer review or proof-assistant certification.

Reproduce the reviewer's finite checks with:

```bash
python3 openai-proof-research/frontier/experiments/i03_arithmetic_progressions_r4/reproduce_author.py
python3 openai-proof-research/frontier/experiments/i03_arithmetic_progressions_r4/independent.py
```

## 7. Final significance assessment and priority limits

The exact advance over P is a logarithmic-factor improvement to a positive proportion while retaining **index one** for every admissible fixed base. R004 supplied only bounded indices. The new progression estimate is not a consequence of marginal PD alone and closes the explicit invariant-core obstruction identified in the earlier attempt.

The [final round-5 novelty/significance review](../reviews/i03-arithmetic-novelty-r5.md) found no established duplicate under the available premises and recommends accepting the substantive, nonroutine improvement gate. It compares Ford–Konyagin–Luca's PD conjecture, Bharadwaj–Rodgers's level-one distribution criterion and published version, Moree's GRH density theorem, Goldmakher–Martin–Péringuey's unconditional upper bounds, Murty–Naik's large-sieve-conditional thin count, and Pollack's GRH uniformity theorem. It also checks the strongest nearby corpus interfaces rather than relying only on their final theorem statements.

An older relevant theorem of Nongkynrih (2001) gives positive-proportion primitive roots under a Kummer-field zero-free strip of width exceeding approximately 0.2038. The accepted all-field width here is only `10⁻⁶`; the stronger numerical QRH strip has a narrower field scope. Neither that older theorem nor the factorization companion converts the accepted premises directly into A+. The parent inspected the actual scanned theorem, including its factor 1/2, and the relevant pinned statements. An overlapping public positive-density claim by Carella exists; the review checks its actual Lemma 6.1 and identifies an elementary additive-character obstruction to its asserted error bound. It is not treated as an established duplicate. It would be false to claim that no earlier paper has claimed this conclusion.

The parent verified all 66 pinned files and nine external files in the final review's main manifest, plus all 103 reviewer artifact hashes. Its [verification record](../sources/i03_arithmetic_novelty_r5/parent-verification.json) distinguishes these checks from worldwide-priority certification. The search screened the full catalogue and path tree and read the relevant manuscripts, not every line of all 719 manuscripts.

MathDB supplies the named famous Artin infinitude target, not the proof. **Final attribution clarification:** an earlier parent retrieval omitted the separate Solutions area; both the round-5 snapshot and a fresh parent retrieval include an AI-assisted user remark reporting the OpenAI `x/log²x` claim. This is a retrieval difference, not evidence that the proof reviewer invented the remark. It is not MathDB endorsement and links a different revision. P at our pin remains the source for the quantitative comparison. No numerical MathDB score or badge is certified. Historical reviews and snapshots are retained unchanged.

**Parent decision:** the substantive/nonroutine research target is met by R006 under the stated accepted-corpus premise and bounded novelty assessment. The evidence is the additional compatible correlation construction and its positive-proportion consequence, not merely the absence of a search hit. This is one substantial plausible new deduction, not a certified worldwide-first theorem, a solution of Artin's exact density conjecture, or an externally peer-reviewed proof. No publication or priority registration has been attempted.
