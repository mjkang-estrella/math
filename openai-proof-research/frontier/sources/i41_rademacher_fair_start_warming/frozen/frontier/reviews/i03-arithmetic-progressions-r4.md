# Independent round 4 review: fixed-progression PD and positive-proportion primitive roots

Date: 2026-10-08. Pin: `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

## Verdict and scope

**PASS for Lemma RC, Theorem AP, its reservoir consequence (R), and Theorem A+ as deductions from the stipulated pinned contracts.** I found no fatal gap in the two-endpoint insertion, shared-label averaging, enlarged-denominator local energy, or subsequent extraction. The essential additional assumption in RC—one small group must be a full interval of primes—is sufficient and is supplied by every active set used in extraction. It must remain in the statement.

The proof does not derive conditional PD from marginal PD. It establishes an additional correlation estimate using the general physical pairing, then verifies the progression extraction. The resulting primitive-root assertion is a positive relative **lower** density, uniformly for all sufficiently large real dyadic endpoints for each fixed admissible base. It does not establish an exact Artin density or existence of a natural density.

**No unresolved mathematical step remains in the stated deductions under these accepted inputs.** There are small editorial corrections and useful explicit formulations below, but none requires a new estimate. This review does not certify the upstream theorems themselves. It also does not by itself discharge the separate worldwide-priority and project-success gate. The new lifting argument is a real additional construction; its improvement over the accepted corpus is substantial. Targeted primary-source screening found no established duplicate, with the limits described in §9.

I read `AGENTS.md`, the pin and relevant catalogue entries, the complete iteration index, R004, the round 2 review, and the complete 439-line round 3 report. I independently read the interfaces listed below, including the whole D correlation and extraction sections. I used no agents, staging, commits, or edits outside the assigned review and `frontier/{sources,experiments}/i03_arithmetic_progressions_r4/` paths. The parent retains the acceptance decision.

## 1. Source contracts and integrity

The prefixes in this review are the following exact directories at the pin:

- D: `preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/`.
- S: `preprints/Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/build/`.
- P: `preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/build/`.
- T: `preprints/Simultaneous-primitive-roots-a-conditional-lower-bound-for-prime-bases-October-4-2026/build/`.

The source URL for each file is recorded in [verification.json](../sources/i03_arithmetic_progressions_r4/verification.json), always using the immutable raw GitHub revision. Independent SHA-256 and Git-blob calculation verified all **60 pinned files** against the untruncated `sources/preprints-tree.json`; all **five external downloads** matched their recorded SHA-256. I additionally downloaded **12 key pinned interfaces afresh**, including D §§2, 5–9, S §§2–3, P reduction/splitting/Type II, and T fixed twists. All 12 matched the tree and cached bytes. `verify.py` reproduces these checks without changing the author's cache.

The decisive accepted contracts, with their actual labels and kinds, are:

1. D `sections/06-correlations.tex`, Proposition `prop:graph-transfer`; S `sections/02-transference.tex`, Theorem `thm:transference`, Corollary `cor:transference-pairing`, and Lemma `lem:physical-schur`. The first vector must be constant on the mark fiber **at a fixed integer position**. The second vector need only satisfy its norm bound. Position dependence is unrestricted. The hypotheses include `sup |f| ≤ exp(O(sqrt L))` and physical norms at most `X^(1/2)L^C3`. The exponent C3 is independent of padding J.
2. D Proposition `prop:ideal-family`; S `sections/03-ideal-kernels.tex`, Theorem `thm:ideal` and Lemma `lem:comparison-kernel`. Small groups have no freed padding slots. Each comparison has nonempty free products in both big blocks; its kernels use neither shared labels nor the last endpoint mark. Pattern mass and decomposition costs are fixed log powers, with their defining parameters independent of J.
3. D equations `cor:insertion-separation`, `cor:stripping-normalization`, `cor:stripped`, and `cor:shared-collision`. These specify the measure and the absolute collision errors. They are equations in the proof, not separate corollaries despite the `cor:` label prefix.
4. D equations `cor:bilinear-multiplier`, `cor:U-form`, `cor:arc-energy-target`, and `cor:SM`, together with Lemmas `lem:local-mellin` and `lem:divisor-model`. The endpoint energy is proved for every fixed accuracy and for arbitrarily large fixed major-arc exponents; it is stronger information than the concluding untwisted correlation alone.
5. D `sections/09-long-prime-appendix.tex`, Lemmas `lp:prime-polynomial` and `lp:log-phase`, restated as `lem:long-prime` and `lem:log-phase` in §2. The former accepts every Dirichlet character with modulus ≤ L^C for any fixed C and frequencies up to x². The latter accepts **every residue**, with modulus ≤ L^C, scales between `exp(L/(log L)^2)` and `2x^5`, and frequencies between `exp(L/(2(log L)^2))` and `4x^3`.
6. D `sections/05-major-arcs.tex`, Lemma `maj:long-coefficient`; P `sections/08-type-ii.tex`, Lemma `lem:marked-coefficient-transfer`; T `sections/04-marked-family.tex`, Lemma `lem:twisted-rough-type-ii` and equation `eq:product-progression`. P supplies a theorem-level scalar-coefficient interface. T already records the fixed-character/lcm maneuver, but its more restrictive final family is not imported as an arbitrary-progression theorem.
7. D `sections/07-extraction.tex`, Lemma `lem:progressions` and equations `ext:stripped-coefficient`, `ext:active-term`, `ext:allocation-core`, `ext:core-bound`, `ext:prime-deweight-square`, and `ext:final-limsup`. These identify which errors are absolute and which bounds survive the x-limit.
8. P `sections/01a-reduction.tex`, Lemmas `alg:quadratic-progression` and `alg:splitting-test`; P `sections/07-splitting.tex`, Lemmas `spl:field-bounds` and `spl:smooth-estimate`. The latter two have the all-q contracts needed here; the narrower final Proposition `prop:splitting` alone would not suffice.

The four hashes highlighted in the candidate all match, including D correlation SHA-256 `09d0d46506b82c0cc8c0f04d5c4ff39abe9b6699b7ab04078e73f759d6c46f1d` and S transference SHA-256 `c506e0d2f6323aa70916f69e76123492e0fbdafc00aa1a7e8578f36ebae09265`. Integrity checks are not evidence for the truth of an asymptotic theorem.

At the closing input check, only the shared iteration index had changed concurrently, through parent integration entries. I inspected the new entries; the candidate, pin, prior arithmetic review, R004, and original experiment inputs were unchanged. This review did not edit that index. The before/after hashes and review artifact hashes are recorded in `artifact-manifest.json`.

## 2. Both physical endpoint residues are permitted

This was the highest-risk applicability question. It passes the literal pairing contract.

To avoid confusing the new progression modulus with the source's notation `M=J+ell`, write m for the fixed progression modulus in this section, and take `ell=k=1` in the graph. For a physical state `(n,p-list)`, use the source endpoint value `conj(F_x(n))` with its extra half-damping, multiplied by `1_(n ≡ r mod m)`. At the other endpoint multiply the source value `G(n')` with its half-damping by `1_(n' ≡ r+1 mod m)`.

For every fixed n, the first multiplier has the same value for all represented mark lists. The damping also depends only on n. Therefore the new first vector is mark-independent in exactly the sense of S `cor:transference-pairing`; neither this corollary nor D `prop:graph-transfer` asks that it be invariant under multiplying n by a group prime. The second restriction is allowed even without checking mark independence, since that endpoint is arbitrary subject to its norm. Both multipliers have absolute value ≤1, so neither supremum nor physical norm increases. In particular the source proof of `cor:list-norm` still supplies the same C3 independent of J and the probe count.

The residue factors are inserted in the endpoint vectors, **not** in `K_nu`. Thus the original ideal family and its small norm remain untouched. Mellin separation of the smooth edge cutoff only introduces position powers into the first vector and `D^(-i zeta)` into the operator, exactly as in D `cor:insertion-separation`. The extra periodic vectors do not require a new ideal-norm theorem or any frequency-uniform assertion beyond the accepted family.

The residual pairing estimate concerns the whole signed operator. It does not imply smallness of each transition or each signed comparison. The report correctly postpones the latter estimates to the separate endpoint-energy argument.

## 3. Stripping, dyadic reassembly, and conditional mixing

Here is an explicit accounting of every possible shared-label dependence.

For a pattern, write `D=D_R D_C`, where `D_R` is the product of shared labels and `D_C` the auxiliary free product. Before stripping, the physical positions satisfy `n'=n+D`. Off the source's overlap exceptions, put `n=D_R w`. Then

`n'=D_R(w+D_C)`,

`Psi(n/(xD))/n = D_R^(-1) Psi(w/(xD_C))/w`.

The state/transition normalization in one group is `V_g^(-M-t_g)`. Its shared part is `V_g^(-(M-t_g))`; pairing this with the corresponding factors of `D_R^(-1)` gives one probability factor `1/(V_g p)` for each shared label. The remainder is `V_g^(-2t_g)`, the normalization of the two unshared endpoint lists. The two half-dampings together with the operator damping give exactly the two W_t factors by `cor:stripping-normalization`.

The other quantities behave as follows:

- `F_x(D_R w)=F_x(w)`: shared primes are outside both the inert bands and all long slots.
- `G(D_R(w+D_C))=G(w+D_C)`: the core removes the entire active prime-power part.
- The unshared lists and their damping now depend only on `w,w+D_C`.
- The comparison kernel has no shared label by `prop:ideal-family`, even though a general physical kernel could have such dependence. The proof uses this particular residual family.
- The only intended surviving shared factor is the pair of residue indicators.

There is a real ordering issue with the dyadic partitions, but the report handles it correctly. On one physical dyad a factor `1_(D_R w in [X,2X))` still depends on the shared label. One cannot apply uniform residue mixing to that truncated sum. The source uses those dyads to obtain bounds and then sums the exact pairings; the partition of unity becomes one. The enlarged target cutoffs are one on all relevant transitions. Likewise, restore the full Mellin integral before calculating the stripped expression; its tail has an arbitrarily small absolute error from Schur and the endpoint norms. After this reassembly the displayed cutoff is precisely `Psi(w/(xD_C))`. No restriction on the size of D_R survives. The physical support is always `n,n' = x^(1+o(1))`, so all contributing dyads lie in the permitted range.

Next remove the collision exclusions with the absolute estimates of `cor:shared-collision` and its following paragraphs. A shared label equalling another chosen label, or dividing `w(w+D_C)`, has total harmonic mass at most a fixed polynomial times `exp(-L^.27)`. There are only `O_J(log L)` labels and `O(L)` relevant distinct divisors of the positions. Changed damping loses at most `L^O(J)`. Free-label/endpoint collisions cost `L^O(1) exp(-c L^.39)`. Restricting by two indicators cannot enlarge these absolute errors. Fix J before using these statements.

In the resulting independent-label sum, fix the integer w, all free labels, all unshared endpoint lists, and all shared labels but one in a full small group. This is the legitimate conditioning: **do not condition on either physical residue being satisfied**. Everything except the two residue tests is now independent of the remaining label. If its interval has endpoints U,V, Siegel–Walfisz and partial summation give, uniformly for a unit t,

`sum_(p in [U,V], p ≡ t mod m) 1/p = (1/phi(m)) sum_(p in [U,V]) 1/p + O_(m,A0)((log U)^(1-A0))`.

Here the error is uniform in both endpoints, including all intervals allowed by RC. Since `log U ≥ L^.27` and the full group's harmonic mass is ≥v_-, normalization gives any fixed `O(L^-B)` error. A partial or residue-selected prime group would not satisfy this claim; the full-interval hypothesis is doing essential work.

The fixed product of the other shared labels is a unit mod m for sufficiently large x. Multiplication by it permutes the unit residues, so the conditional residue law of D_R differs pointwise from uniform by `O_(m,B)(L^-B)`. This is uniform even after fixing w and the free labels, because their dependence has already been removed from the sampling measure. It is not an assertion of independence in the original restricted arithmetic sum.

For every unit d and every r,w mod m, the two congruences

`t w = r`, `t(w+d) = r+1`

force `t d=1`, and hence the unique possible t is `d^(-1)`. It satisfies the first congruence exactly when `w=r d`. Thus the averaged multiplier is

`(1/phi(m)) 1_(w ≡ r d mod m) + O_(m,B)(L^-B)`.

This proof never inverts w, r, or r+1, and applies to nonunits and prime-power moduli. Taking `d=D_C` gives the candidate's comparison residue, while the raw term has `D_C=1` and supplies precisely `RC/phi(m)`.

Finally, the error can be summed without a hidden bias: after absolute values the marked factors and kernel mass cost fixed log powers; `F_x` is bounded; and a fixed divisor moment bounds

`sum_(w asymp xD_C) tau(w+D_C)^C / w`

by a fixed log power uniformly in the permitted D_C. Choose B after these exponents, J, and the desired final accuracy. The resulting total error is `O(L^-A)` for any fixed A. The arbitrary sign of G or the kernel is harmless because this is an absolute error estimate. This completes the required justification of mixing in the full stripped expression.

## 4. Fourier-shift energy and the parameter order

The comparison part also passes. Expanding the accepted cell/character kernels yields separate bounded tests on the two free products and the endpoint big marks. Fix one such expansion term and its two cells. Then the first endpoint has exactly D `cor:U-form`, with a fixed bounded big-mark test and fixed-log-power smoothness/twist parameters. Its definition does not contain either free product's residue.

Split the free tests by `D_A ≡ alpha`, `D_B ≡ beta (mod m)`. These restrictions are factors of absolute value ≤1 on their respective free tuples. They do not renormalize their laws and do not cost inverse probabilities of residue classes. Consequently the squared coefficient norms used in `cor:bilinear-multiplier` can only decrease. The endpoint mark tests remain the same for each residue split. Now `w ≡ r D_A D_B` becomes the fixed restriction `w ≡ s`, with `s=r alpha beta`.

For the source Fourier sign convention the exact identity is

`Uhat_s(xi) = (1/m) sum_(j=0)^(m-1) e(-js/m) Uhat(xi+j/m)`.

Cauchy gives the candidate's local energy inequality with factor 1/m. The center `h/k+j/m` has reduced denominator at most mk, even when k and m share factors. There is no unit condition on s.

This requires a stronger input than unconditioned smallness of the comparison sum. That input actually exists in D's proof: `cor:arc-energy-target` and `cor:SM` are established to every fixed accuracy, for any fixed major-arc exponent chosen after the ideal family. To make the use entirely explicit, let C6 be the multiplier's chosen arc exponent and put `C*=C6+1`. For large x, `m L^C6 ≤ L^C*`. Run the source endpoint-energy proof with

`H_* = H'/L^C*`, `T_* = LY/H_* = x L^(C*+1)`.

Its arcs contain the original windows `|beta| ≤ L^C6/H'`. This changes neither the ideal family nor the multiplier; it only asks the endpoint estimate for a slightly larger fixed denominator/window range. The exact hypotheses remain available:

- D `cor:low-main-term` uses all residues modulo the rational denominator. Every prime in a long tuple or model divisor eventually exceeds `L^C*`, so the divisor is invertible modulo that denominator. The tuple main term differs from the constant main term only by 1/l, and centering cancels it, including the zero-frequency case.
- `lem:divisor-model` is uniform for arbitrary bounded tuple tests. Thus the cell and character parameters already fixed in U are legitimate.
- In the high-frequency argument the chosen small endpoint mark still has `t_g=1`, and its test involves only big marks. The small polynomial may include residue restrictions; its exceptional-set estimate is coefficient-independent.
- `H_*/(L P_s) → infinity`, since `log H' ≥ 2L^.39-O(1)` while `log P_s ≤ L^.36`. All fixed log-power increases are negligible in this inequality.
- The long-prime input `lp:prime-polynomial` covers denominator `≤L^C*` and retained frequencies `≤2x L^(C*+1)<x²`. Its lower threshold can be met by choosing the low-time exponent later.
- The constant-term model retains the residue condition, which may be nonunit. Its residual scale is `x^(1-o(1))`; D `lp:log-phase` covers that scale, the larger fixed denominator, and the required frequencies. The constant model error is bounded on the whole time interval before restricting to sparse times, as required in `cor:constant-model-error`.

There is no circular choice here. Choose the transfer target from the original endpoint norm exponent; obtain the ideal family; fix a sufficient J. The comparison kernels and their fixed losses are then known. Choose C6 for minor arcs, enlarge it to C*, and choose endpoint accuracy after the finite arc count and decomposition losses. The source supplies arbitrary accuracy for this fixed C*. Low-frequency thresholds, model precision, and smooth-tail orders are chosen afterwards. Enlarging C* does not require changing the graph family or J.

Parseval with the unchanged second-endpoint energy handles the multiplier minor arcs, and the shifted local energy handles the major arcs. All comparisons are bounded individually at this point. If R is the raw restricted sum and C_nu the signed comparisons, transference and mixing give

`(R + sum_nu C_nu)/phi(m) = O(L^-A)`.

The independently proved `sum_nu |C_nu| = O(L^-A)` therefore isolates R. This is valid subtraction of signed quantities, not a positivity argument. It proves RC.

## 5. One-sided transfer and progression extraction

The changes in §§4–5 are all justified by exact contracts; RC is the only new analytic input needed for the composite correlation.

**Scalar character transfer.** For any fixed character chi0 mod M, its product with a test character modulo `k≤L^A0`, with the prescribed zero extensions, is a possibly imprimitive character modulo `lcm(M,k)≤L^(A0+1)` eventually. Its nonunit zero set is exactly the union of the two original nonunit sets. D `maj:long-coefficient` therefore supplies P `lem:marked-coefficient-transfer`'s full range `|t|≤2XL^B`, including principal products and conjugation. The prime-minus-rough discrepancy remains bounded and W-rough. The scalar formula involves x, W, the interval and the twists, not K or the band exponents. Its common bounds can therefore be fixed before choosing K; enlarging K or changing the inert arrays does not change those scalar sums. This is the same valid order of choices already made explicitly in T's fixed-twist proof.

Orthogonality for `mn ≡ b (mod M)` holds also on nonunits, because b is a unit and both sides vanish if either factor is not. Put the two characters into alpha and beta. Do not change the invariant predecessor function `F(mn-1)`. Truncating beta using divisor moments is still an absolute error; the character factors do not increase it. K may depend on the now fixed modulus, precision, factorization lengths and other fixed data, but its lower bound remains independent of the subsequent band exponents.

**CRT/sieve main term.** If `(r,M)>1`, `r|u+1` and `u+1 ≡ b mod M` are incompatible. In the coprime case, a long tuple l and model divisor d' are units modulo M for sufficiently large x. Also `(l,r)=1` by the long-slot lower bound. If `(d',r)>1` the contribution vanishes; otherwise writing `u=ld'v` gives exactly one class modulo Mr, and its smooth main term is `x/(Mrld') int Phi`, with O(1) rounding error. Thus the candidate's CRT main term is correct. Band primes dividing r are handled by the same forced-absence model as D `lem:progressions`; no band prime divides fixed M eventually. The absolute Bonferroni tail and total rounding costs retain their stated saving.

Sieve only at primes not dividing M. Eventually z exceeds every prime factor of M, and

`(1/M) product_(q≤z,q∤M)(1-1/q) = (1/phi(M)) product_(q≤z)(1-1/q)`.

This remains true for prime-power M. The nonnegative block sieve is applied separately to the two original nonnegative weights, and their centered main terms cancel. After division by the model mean, the surviving constant depends on the fixed slot/cutoff/modulus data, but not on K, h or the chosen array. Dependence of vanishing remainders on these parameters does not affect the limsup.

**Absolute errors versus signed expansion.** I checked the relevant parts of D §7, not merely the final interior theorem. Large-factor squares, coefficient truncations, smooth/Fourier errors, candidate-part threshold/logarithm changes, and the failed-coin mass are controlled absolutely before cancellation. A residue indicator cannot enlarge these estimates. In particular the qualitative `o(x/L)` failed-coin mass is discarded while the coin partition is positive; it is not multiplied later by `3^|C|`. The estimates for candidate-square exceptions after expansion have an exponential saving, so they can pay the fixed polynomial expansion cost.

The candidate groups are full prime intervals `[exp(y),exp(2y))`. Every retained active set contains a positive multiple of log L small groups and hence supplies the full small interval needed by RC.

**Allocation.** With v fixed, allocating its active primes among the factors changes neither v nor `1_(v ≡ b mod M)`. The stripped coefficient depends on the candidate-free bars, so each allocation still has the same coefficient. The exact source identity

`j^omega_P(v) (q0/j)^(omega_P(v)-sP) = j^sP q0^(omega_P(v)-sP)`

therefore remains valid with the external progression restriction. `G_P` remains precisely `ext:allocation-core`, depends only on v_*, and satisfies `ext:core-bound`. It would be wrong to put the progression condition inside this core. Apply RC with `r=b-1` and `Psi(t)=t Phi(t)`; multiplication by x gives the required ordinary weighted sum. Choose its accuracy after all polynomial active-set losses. The composite contribution vanishes.

**Deweighting.** The square Z_B is nonnegative. The unrestricted upper bound `ext:prime-deweight-square` dominates its sum over any fixed class, without assuming PD in that class. The other Cauchy factor is `O((x/L)^(1/2))` by boundedness of the statistic and the prime count. Thus the final bound is exactly of the form

`C_M e^(-h)/gamma + C sqrt(C_K/B)`.

Fix h, then K, then any finite B arrays, then take real x to infinity. Afterwards let B tend to infinity, and finally h through arbitrarily large even integers. No K, B or M grows with x in a theorem application. This proves (I-AP).

## 6. Conditional factorial intensities imply the full PD law

This passage is justified, including boundary tightness. It uses the newly proved (I-AP) as its conditional input; the marginal law is not being conditioned formally.

Fixed-progression PNT gives a denominator asymptotic `x/(phi(M)L)` on a dyad. Smooth approximation and the bounded tuple count convert (I-AP) into the rectangle factorial intensities `product log(b_i/a_i)` whenever the lower endpoints are positive and the upper endpoints sum to less than one. The fixed factor phi(M) is harmless in every negligible error. The exact normalization `log(p-1)` follows by a fixed-endpoint sandwich, since its ratio with log x is uniformly `1+O(1/L)`.

For compact interior tests, the correction for repeated numerical primes is bounded by `O(x^(1-a/2))` times a bounded tuple multiplicity. Dividing by the class-prime count makes it o(1). Fine rectangles inside a slightly larger compact simplex establish local convergence for continuous tests; their factorial masses are uniformly bounded because every tested ball has a fixed positive minimum mass.

The size-biased law is a probability law even when the finite collection is exhausted, by padding with zeros. On the interior its limiting density is

`h_d(t)=product_i (1-t_1-...-t_(i-1))^(-1)`.

The triangular stick transformation has reciprocal Jacobian h_d and maps the whole open simplex to `(0,1)^d`. Hence this limiting interior measure has total mass one. Compact exhaustion gives probability at least `1-o(1)-eta` in an interior compact set; this rules out every possible escaped boundary mass, including padded zeros and the face with total mass one. It does not require a separate estimate for very small prime factors.

The unseen mass after d draws converges in expectation to `2^(-d)`, since it is a bounded continuous function of the draws. Sorting the first d draws approximates each ranked coordinate with error at most the unseen mass. Markov's inequality followed by d tending to infinity gives the finite ranked joint laws. Fixed dyadic decompositions and progression PNT give the cumulative form of AP. The omitted initial dyadic mass tends to zero after the x-limit.

For `0<theta<1/2`, the PD largest-factor tail above `1-theta` is `-log(1-theta)`, with no atom at the threshold. The same exact-denominator sandwich gives (R). There is no claimed convergence rate or growing-modulus uniformity.

## 7. The A+ reduction and its error budget

This is the repaired round 2 reduction, now with its formerly missing input established by AP. It passes for every stated base, including negative squares and odd perfect powers.

P `spl:field-bounds` supplies degree `q(q-1)`, the logarithmic discriminant-to-degree bound, and the descended zero-free region for every sufficiently large q depending on a. Apply `spl:smooth-estimate` with one nonnegative smooth function ≥1 on [1,2], fixed independently of q. Complete splitting gives `q(q-1)` degree-one prime ideals per rational prime, all with weight ≥log x. Dividing the nonnegative upper bound gives the report's (S) for all real x≥2 and all q≥q0(a). This use does not inherit the upper q cutoff from the later simplified proposition. Degree-drop primes for perfect powers belong below q0(a).

P `alg:quadratic-progression` gives the required class modulo `M0=8 product_(odd ell|a) ell`: it forces `(a/p)=-1` and avoids 1 modulo every odd prime in M0. The signed-squarefree reduction in its proof explicitly includes negative squares. For odd powers, take Y beyond the exceptional primes in q0(a); the finitely many prime divisors of the exponent can then be excluded by the same small-prime construction. No inadmissible positive square is included.

For the union R_Y, CRT gives exactly

`w(Y) = (1/phi(M0)) product_(3≤q≤Y,q∤M0) (q-2)/(q-1)`.

The ratio of each new factor to `1-1/q` is `1-1/(q-1)^2`, whose product over odd primes converges to a positive constant. Thus `w(Y) asymp_a 1/log Y`. The denominator counts reduced classes, so no factor q instead of q-1 is lost. For each fixed Y, summing (R) over its finite set of classes gives reservoir mass `c(theta)w(Y)`, with `c(theta)=-log(1-theta)`.

On the reservoir, `p-1=mQ`, `Q>x^(1-theta)`, `m<2x^theta`. For sufficiently large x, Q>m, so Q occurs once. If Q divides the index, the order divides m and p divides a nonzero factor of `product_(j≤ceil(2x^theta)) |a^j-1|`. Its logarithm is `O_a(x^(2theta))` for either sign of a. The large-Q exception is therefore `O_a(x^(2theta)/log x)=o(N(x))`.

Any other prime divisor of the index divides m. The prime 2 is excluded by quadratic nonresiduosity, and all odd q≤Y are excluded because q does not divide p-1 in R_Y. For `Y<q<2x^theta`, P `alg:splitting-test` applies, since q divides p-1 and thus q≠p; primes dividing a have been excluded. Summing (S) globally, without claiming a conditioned splitting estimate, gives

`(C_a/Y) x/log x + O_a(x^(1-delta+theta))`.

The first sum telescopes after enlarging to integers; the second is o(N(x)) for fixed `theta<delta=10^-6`. Intersections of these exceptional sets only improve the union upper bound.

Choose Y so that `C_a/Y < c(theta)w(Y)/4`, and then freeze Y and M_Y before the x-limit. This is possible because `Y/log Y` tends to infinity. The report's eventual budgets `7/8 - 3/8 - 1/8 = 3/8` leave more than its stated `c_a=c(theta)w(Y)/4`. All primes outside the exceptions have index exactly one, not merely bounded index. Summing over disjoint descending dyads leaves only a bounded initial interval and proves the cumulative positive lower density.

No modulus grows in any application of AP. No Chebotarev independence, independence of different Kummer fields, or positivity in an arbitrary primitive-root progression is assumed.

## 8. Reproduction and additional finite falsification tests

The author's script was copied verbatim into the assigned experiment directory and run there, so its output path stayed within this review's scope. Its `results.json` is **byte-for-byte identical** to the original:

- 833,272 orbit cases, including 243,782 nonunit-source cases, with no failure.
- Uniform multiplicative convolution for 63 moduli, with no failure.
- 1,392 Fourier identity cases, maximum floating error approximately `4.08e-13`.
- 189 admissible signed bases, 18,488 prime instances in the constructed quadratic classes, with no failure.
- The 306-prime quadratic-entanglement example and the small CRT-union checks reproduce.

[Independent tests](../experiments/i03_arithmetic_progressions_r4/independent.py) additionally give:

- The forced-inverse orbit calculation through modulus 96: 12,950,254 source/shift/position cases, including 4,054,120 nonunit-source cases, with no failure.
- 1,560 exact rational weighted stripping models with signed remaining coefficients, residue-dependent label magnitudes, the cutoff, 1/n, and explicit physical dyadic partitions. All reassembled pairings equal the predicted stripped answer. **1,558 have individually biased physical dyads**, demonstrating why one must reassemble before mixing. This is a check of the algebraic issue, not a model for the analytic graph theorem.
- 17,892 exact CRT main-term cases, including 3,904 with sieve modulus sharing a factor with M; these incompatible cases give zero.
- 717,544 exact perturbed-residue-law cases confirming the uniform orbit-error bound after fixing another independent unit factor.

Outputs are [independent-results.json](../experiments/i03_arithmetic_progressions_r4/independent-results.json) and [reproduction.out](../experiments/i03_arithmetic_progressions_r4/reproduction.out). The tests do not verify transference, long-prime cancellation, mixing asymptotics, PD convergence, the tiny theta exponent, or novelty. Those conclusions rest on the proof and accepted contracts, not numerical extrapolation.

## 9. Novelty and significance: separate assessment

Fresh targeted searches covered progression-conditioned shifted-prime PD, fixed-base positive-density primitive roots, and the recent nonabelian-large-sieve reduction. Search records and the retrieved MathDB view are saved in the assigned source directory. I also inspected the author's cached primary texts and verified their hashes.

- Ford–Konyagin–Luca, *Prime chains and Pratt trees*, §6, Conjecture 5, states the marginal shifted-prime PD conjecture and its implication from Elliott–Halberstam. It does not supply joint information with a progression label from marginal PD. [Primary author PDF](https://www.ford126.web.illinois.edu/wwwpapers/chains.pdf).
- Bharadwaj–Rodgers v4, Theorem 7, requires level-one well-distribution for full PD; Lemma 8 gives the restricted-simplex correlations at lower level, and Proposition 2 supplies level one half for shifted primes. Theorem 11 is an upper bound for an exceptionally large prime factor, not the lower reservoir used here. These are not an unconditional duplicate of AP. [Primary v4](https://arxiv.org/html/2402.11884v4).
- Moree, Theorem 1, gives an AP asymptotic under GRH; Theorems 2–4 describe the density and its obstructions. This is stronger density information under a different premise, not an established unconditional duplicate of A+. [Primary v1](https://arxiv.org/pdf/0707.3062v1).
- Goldmakher–Martin–Péringuey, Theorems 8.1 and 8.8, provide unconditional upper bounds for small index-factor statistics. They have the wrong direction to imply the claimed positive lower density. [Primary v1](https://arxiv.org/html/2502.19601v1).
- Murty–Naik, Theorem 1 and Remark 1.1, derive an `x/log²x` primitive-root count from a stated nonabelian-large-sieve inequality, with extension to admissible bases. Their partial unconditional inequalities do not remove that theorem's hypothesis. [Primary v1](https://arxiv.org/html/2608.21573v1).

Within the inspected corpus, the accepted primitive-root result is `≫_a x/log²x`, D's main PD theorem is marginal, and T's fixed progression family has narrower hypotheses and a thin count. The candidate correctly does not claim the character-twist device, graph machinery, local Mellin energy, coefficient-transfer criterion, or all-q splitting estimate as new. The union-of-classes arithmetic reduction was already supplied by the round 2 reviewer. The additional contribution is the two-position-residue lifting with the shared-label orbit calculation, its compatibility with comparison energy, and the complete resulting AP extraction.

That contribution is mathematically more than a restatement of marginal PD: one-sided residue averaging loses the desired class, and inserting the class into the invariant core fails the source hypothesis. The two-endpoint construction resolves those specific obstructions. The improvement to index one on a positive proportion is substantial relative to both R004 and the accepted corpus's thin primitive-root count. This provides positive evidence for the project's nonroutine-improvement criterion.

The freshly retrieved [MathDB Artin page](https://mathdb.com/p/370026/artin-s-primitive-root-conjecture) calls the target famous, states its infinitude form, and records the OpenAI `x/log²x` claim while distinguishing it from a density formula. I did not observe a numerical importance score or a “Celebrated” badge and do not certify either. Its summary also mentions an unverified claimed positive-density proof; that secondary mention is not an established duplicate or a priority clearance. No worldwide priority claim follows from this bounded literature search. Parent review must assess that remaining gate independently, and any final claim must continue to state the accepted-corpus premise.

## 10. Editorial fixes and acceptance boundaries

These are presentation corrections, not unresolved proof obligations:

1. In `(presieve-AP)`, replace the malformed normalization `L/{x,m_W}` by `L/(x m_W)`.
2. Several `cor:` labels in §2.1 are equations, not corollaries. Cite them as equations in D's proof, especially `cor:arc-energy-target` and `cor:SM`. The needed quantified estimate is actually proved there; this correction makes the dependency precise.
3. State explicitly that all physical dyadic partitions and the Mellin separation are reassembled before shared-label mixing. The report already says this; retain it in any shorter integrated proof. Individual dyads are not eligible for the uniformity argument.
4. Describe the limiting size-biased draws as GEM(1) stick fragments **generated by** independent uniforms; the fragments themselves are not independent.
5. Preserve the full-small-interval assumption, the fixed-modulus quantifier, the order `x → infinity`, then array count, then sieve depth, and the lower-density wording. Do not promote A+ to an exact density formula or simultaneous positive-density primitive roots for arbitrary sets of bases.

**Proof acceptance recommendation:** accept RC → (I-AP) → AP/(R) → A+ as a completed deduction under the pinned contracts, after the minor typesetting/reference cleanup. **Research-success recommendation:** the mathematical improvement and nontrivial construction are supported; global priority and the final significance gate remain a separate parent decision. Nothing in this review changes the accepted status of the upstream corpus or edits/promotes the candidate on the parent's behalf.
