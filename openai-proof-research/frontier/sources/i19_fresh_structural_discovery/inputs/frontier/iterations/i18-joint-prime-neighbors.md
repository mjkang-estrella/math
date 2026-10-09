# I18 — Joint factor sizes of the two neighbors of a prime

Date: 2026-10-09. Status: **scoped negative/gap report; no proposed counted finding**. This is not a claim that the desired theorem is false, nor a proof that it cannot be derived from the stipulated corpus. It records exact deductions, attempted extensions, and an unresolved analytic estimate. No shared finding/index was edited, and no commit or publication was made. Separate fresh proof and significance reviews remain the parent's responsibility.

## 1. Assignment, conventions, and conclusion

The assignment is to seek a substantial joint factor-size law for `p-1` and `p+1`, preferably PD(1) × PD(1), beyond the accepted marginal/arithmetic-mode findings R006, R008, R009, R010. The user resumed the ten-finding objective on this date and authorized verified project-only public pushes, handled by the parent. The assigned scope excludes agents, shared-record edits, staging, commits, and pushes. I14's significance remains technical only; I15 and I17 are unrelated active work. The complete supplied brief is frozen in [brief.txt](../sources/i18_joint_prime_neighbors/brief.txt).

All assertions in `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted as true. This report checks *new inferences*, not their upstream truth. The full 749-manuscript tree and 9,340-file text cache were available; this is a targeted search and source analysis, not a claim to have read every manuscript. Dependencies and context copies are frozen separately from the read-only cache.

Let `M` be a fixed positive integer and `(b,M)=1`. Write

\[
 N_M(x)=\#\{x<p\leq2x:p\equiv b\pmod M\}
       \sim\frac{\operatorname {Li}(2x)-\operatorname {Li}(x)}{\varphi(M)}.
\]

The prime `p` is uniform in this set. Let `V_-(p),V_+(p)` be the decreasing sequences of logarithms of prime factors of `p-1,p+1`, with multiplicity, divided by `log(p-1),log(p+1)` respectively. The target is joint weak convergence in the two mass-partition spaces to independent PD(1) sequences. Reflection of the marginal theorem, another fixed Omega congruence, or a fixed local congruence is not counted as a discovery.

**Outcome.** A classical restricted mixed factorial law is proved below when the *combined* selected log mass is less than `1/2`. A separate elementary joint presieve remainder is proved when that combined mass is less than `1`. Neither reaches the full two-simplex required for the target, and neither is substantial new research. The strongest source interfaces checked do not directly permit the second shifted size statistic through prime extraction. The precise missing family of prime discrepancies is (MI) below. It is **unproved**, not a conditional solved finding.

## 2. Frozen source contracts

[manifest.json](../sources/i18_joint_prime_neighbors/manifest.json) records SHA-256, bytes, immutable raw URL, and Git blob for 103 retained source files in ten manuscript families; it also freezes 20 local inputs. Retention alone does not make a file a theorem dependency. Actual contracts used are as follows. Paths below are relative to `pinned/preprints/` in this iteration's source directory. Full filenames and read locators are also machine-readable in `source-contracts.json`.

* **D:** `The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026`. Section 03, `thm:type-II`, allows a bounded endpoint `F` with **F(qh)=F(h)** for every selected small-band prime, rough bounded second coefficients, and the specified prime-minus-rough first coefficient. Its error is `X (log x)^(-D_*)` for any prescribed fixed precision, with sufficiently large fixed `K` independent of the particular band exponents. Section 06, `thm:two-sided`, has centered first endpoint `W(n)(T(n)-C_x)`; all long prime slots are at least `x^epsilon` and their upper endpoints multiply to at most `x^(1-epsilon)`. The other endpoint obeys **G(n)=G(n_*)** and a fixed divisor-power/log-power bound. The marked correlation with `Psi(w/x)/w` is `O_A((log x)^(-A))` for every fixed `A`, uniformly over permitted active groups and long slots, with dependence on fixed inert bands allowed. It is a theorem about *two endpoints*, not an arbitrary function of a third neighboring integer. Section 07, `thm:interior`, obtains one prime-neighbor statistic after presieving, composite removal, allocation, and deweighting. Its progression lemma, allocation identity, and final limit order were checked, not bypassed.
* **S:** `Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026`, Section 02 `cor:transference-pairing` and Section 04 `thm:shift`. The general graph pairing allows a general norm-controlled second vector, but it averages independent slot permutations at both endpoints. In its application the first vector is constant on its mark fiber, and shared-label stripping and endpoint symmetrization are actual operations. The shifted convolution theorem retains invariant endpoint hypotheses. Arbitrary second-vector allowance is not a license to attach a statistic to the *stripped* endpoint without tracking which labels are shared.
* **P:** `Primitive-roots-for-every-admissible-integer-base-October-4-2026`, Section 08 `lem:marked-coefficient-transfer`. This stronger scalar coefficient interface requires, for every fixed `A_0,B,A`, cancellation against **every character modulo k <= (log x)^(A_0)** and every `|t| <= 2X(log x)^B`, uniformly on permitted intervals, with arbitrary fixed logarithmic saving. The endpoint still has the original invariance property. All extra coefficient parameters must be fixed before `x` grows. It does not supply cancellation modulo an added long prime `q >= x^epsilon`.
* **J:** `The-joint-Dickman-law-for-consecutive-integers-September-24-2026`, `distribution.tex`, `labels.tex` (`prop:mixed`), and the conclusion. The ordinary consecutive-integer joint smoothness law and the stronger fixed-bin two-endpoint multiplicative-phase decorrelations are available. The normalization is ordinary integer averaging. The binwise statements support ordinary joint PD deductions discussed in i07; calling these only a largest-factor theorem would understate the input. They nevertheless carry no prime indicator at the midpoint `2n+1`.
* **O:** `Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026`, introduction `thm:q-affine`, `thm:elliott`, `cor:affine`, and analytic transfer sections. Binary corrected Elliott is for fixed bounded multiplicative functions under its nonpretentiousness condition and gives ordinary `o(X)` cancellation. The quantitative affine Liouville theorem has an **absolute positive logarithmic exponent**, with an implied constant depending on the fixed forms; it neither asserts arbitrary logarithmic precision nor uniformity for forms growing with `X`. None of these is a three-position prime-conditioned theorem.
* **E, T, Z:** the even-Omega predecessor manuscript, simultaneous-primitive-root conditional manuscript, and quasi-Riemann-hypothesis manuscript were retained and checked as companion context. E's active-band sign changes and P/R010's complex scalar modes do not supply a second shifted long-factor statistic. T/i06 distinguishes the composite coefficient input from the rough correlation input; success at the former does not solve the latter. Z's zero-free half-plane, including its specified Hecke family, does not itself state the mixed prime discrepancy (MI).

The full R006/R008/R010 finding records, i03/i05/i10 proofs, i10 integration note, and their final proof/significance reviews were read. i07's arithmetic/ordinary joint-law discussion and i06's two-gap analysis were consulted where needed. Their frozen copies include obsolete intermediate status sentences; current accepted status is the user's four findings, not those historical sentences. R006 permits fixed residue data while proving a single size law; R008 adds parity; R010 adds fixed complex arithmetic modes and their properly recombined principal model. None states joint shifted size independence. No internal record here is counted as an independent literature-priority certificate.

## 3. CRT and local obstructions, with proofs

For positive `A,B,M` and `(b,M)=1`, the system

\[
 p\equiv1\pmod A,\quad p\equiv-1\pmod B,\quad p\equiv b\pmod M
 \tag{CRT}
\]

has a solution precisely when

\[
 (A,B)\mid2,\qquad (A,M)\mid b-1,\qquad (B,M)\mid b+1.
\]

This is the pairwise compatibility criterion for generalized CRT. When compatible it gives one class modulo `lcm(A,B,M)`, and this class is a unit: each prime dividing the modulus divides at least one of `A,B,M`, on which its prescribed residue is a unit. With an additional central presieve condition `p=0 mod r`, compatibility requires and is equivalent to `(r,ABM)=1` in addition to the displayed conditions. The residues `b-1` and `b+1` on the two neighbors need not be units modulo `M`; nowhere may they be inverted without a separate condition. These facts include prime powers, not only squarefree moduli.

For odd `p`, `gcd(p-1,p+1)=2`. For a fixed odd prime `ell`, PNT in fixed progressions yields the following limiting *joint* valuation probabilities (without an additional imposed residue class):

\[
 \Pr(v_\ell(p-1)=k,v_\ell(p+1)=0)=\ell^{-k},\quad
 \Pr(v_\ell(p-1)=0,v_\ell(p+1)=k)=\ell^{-k}\quad(k\geq1),
\]
\[
 \Pr(0,0)=\frac{\ell-3}{\ell-1};\qquad \Pr(k,j)=0\ (k,j\geq1).
\]

Indeed, exact valuation `k` selects `ell-1` reduced classes modulo `ell^(k+1)`, out of `ell^k(ell-1)`; the two signs are disjoint. At `ell=2`, the only possibilities are `(1,k),(k,1)` with `k>=2`, each of mass `2^(-k)`, by the same count among odd residues. These masses sum to one. Distinct fixed primes are independent *across primes* by CRT; the two neighboring valuations at the same prime are emphatically not independent. Under `p=b mod M`, condition these fixed finite residue counts using (CRT); do not insert the unrestricted probabilities blindly.

Consequences such as “the two neighbors cannot both be squarefree” and the impossibility of a common odd prime factor are routine. A common largest prime factor for odd `p` would have to be 2; the two neighbors would be powers of 2 differing by 2, forcing `p=3`. None contradicts independent normalized PD limits. For each fixed `ell`, first bound the probability of valuation at least a fixed `K` by its fixed-progression limit, then take `K` large. On the remaining event `v_ell log ell/log p` tends to zero. This ordered limiting argument also works in a fixed reduced class `b mod M`. It avoids an unproved prime-progression estimate with a modulus growing like `p^epsilon`.

## 4. Proved baseline: joint factorial intensities below combined mass 1/2

**Proposition 1 (classical restricted law, not a finding).** Fix integers `r,s>=1`, a fixed reduced class `b mod M`, and a continuous function `f` with compact support in

\[
 \mathcal U_{r,s}=\{(t_1,\ldots,t_r,u_1,\ldots,u_s):t_i,u_j>0,
                       \ \sum_i t_i+\sum_j u_j<1/2\}.
\]

For each neighbor, take ordered tuples of distinct prime-factor *occurrences* in its factorization. Then

\[
 \frac1{N_M(x)}\sum_{\substack{x<p\leq2x\\p\equiv b\ (M)}}
 \sum_{\substack{q_1,\ldots,q_r\mid p-1\\\text{distinct occurrences}}}
 \sum_{\substack{z_1,\ldots,z_s\mid p+1\\\text{distinct occurrences}}}
 f\left(\frac{\log q_i}{\log(p-1)},\frac{\log z_j}{\log(p+1)}\right)
 \longrightarrow
 \int f(\mathbf t,\mathbf u)\prod_i\frac{dt_i}{t_i}\prod_j\frac{du_j}{u_j}.
 \tag{1}
\]

The notation inside `f` denotes all `r+s` coordinates. The same statement with one empty side is allowed. This is the product-PD factorial measure only on this restricted open set; it is not the joint PD law.

**Proof.** Compactness gives a positive lower coordinate bound `a` and positive distance from total `1/2`. Start with a rectangle whose coordinate intervals have fixed positive endpoints and whose upper endpoints sum to `1/2-delta`, `delta>0`. Initially normalize logs by `log x`. Let `T_-(n)` count ordered numerically distinct prime tuples `q_i` in these slots dividing `n`, and let `T_+(n)` be the corresponding `z_j` count. Put `A=prod q_i`, `B=prod z_j`, and `d=r+s`. For large `x` these primes exceed `M` and 2. Cross-side repetitions cannot occur for a contributing `p`. Thus `A,B,M` are pairwise coprime and (CRT) gives a unit class `c(A,B)` modulo `MAB`.

Swapping the finite sums gives exactly

\[
 \sum_{\substack{\mathbf q,\mathbf z\\(A,B)=1}}
 [\pi(2x;MAB,c(A,B))-\pi(x;MAB,c(A,B))]. \tag{2}
\]

All moduli are at most `M x^(1/2-delta)`. A fixed modulus has at most `d!` representations by the labeled slots, because its `d` distinct long primes determine the tuple up to a permutation. Bombieri–Vinogradov, in the usual version summing the maximum reduced-residue prime-counting error, bounds the error in (2) by `O_{d,M,A_0}(x/log^(A_0) x)` for every fixed `A_0`: eventually the displayed range lies below `sqrt(x)/log^B x` for its required `B`. Applying the theorem at `x` and `2x` suffices. There is no unsupported maximum over a long-factor tuple hidden in this step.

For the main term,

\[
 \frac1{\varphi(MAB)}=
 \frac{1+O_d(x^{-a})}{\varphi(M)AB}.
\]

The sum of `1/(AB)` over all slot choices is bounded by a constant depending only on their endpoints. Removing the cross-side and within-side diagonals changes it by `O_d(x^(-a))`: fix a repeated pair, sum `q^(-2)` over `q>=x^a`, and bound the remaining finitely many prime harmonic sums. Mertens' prime harmonic formula on every fixed exponent interval `(alpha,beta]` gives `sum 1/q -> log(beta/alpha)`. Dividing by `N_M(x)` proves (1) for such rectangles and numerical prime tuples.

Prime powers do not affect the answer. For either neighbor the number of integers in the dyad divisible by `q^2` for some prime `q>=x^a` is at most

\[
 O\!\left(x\sum_{n\geq x^a}n^{-2}+\sqrt{x}\right)
       =O(x^{1-a}+\sqrt{x})=o(x/\log x).
\]

Every tuple in the relevant ranges is bounded in count by a constant: there are at most `log(3x)/(a log x)` factor occurrences above `x^a`. This proves that replacing numerical distinctness by distinct occurrences changes the normalized sum by `o(1)`.

Finally `log(p±1)/log x=1+O(1/log x)` uniformly in the dyad. Use rectangles with small boundary strips, whose limiting integrals tend to zero with strip width, or uniform continuity for continuous tests. A finite grid inside the open support, bounded tuple counts, and upper/lower approximations prove (1). All data are fixed before `x` tends to infinity. No assertion about an `x`-dependent number of slots or shrinking rectangles is made. QED.

This is a two-colored application of classical prime distribution in progressions. The limited-simplex method has explicit single-sequence precedent in Bharadwaj–Rodgers, Lemma 8; their Proposition 2 covers the classical shifted-prime level `1/2`. Their theorem must not be misquoted as a full prime-neighbor PD theorem from level `1/2`—the full theorem uses level 1. [Primary source, v4](https://arxiv.org/html/2402.11884v4).

## 5. Proved presieve input below combined mass 1

The preceding argument suggests using the stronger D extraction instead of BV. The elementary progression input can indeed be extended on a larger, but still restricted, region.

**Proposition 2 (joint ordinary presieve remainder, not prime extraction).** Fix the two finite slot families, all lower exponents at least `a>0`, with sum of *all upper exponents* at most `sigma<1`. Let `T_-,T_+` count ordered numerical distinct primes in their respective slots. Set

\[
 C_{-+}(x)=\sum_{\substack{\mathbf q,\mathbf z\\(A,B)=1}}\frac1{AB}.
\]

Fix `Phi` smooth and compactly supported in `(0,infinity)`, and choose a fixed `0<c<min(a,1-sigma)`. Uniformly in integers `1<=r<=x^c`, put

\[
 S_r=\sum_{\substack{u\geq1\\u+1\equiv b\ (M)\\r\mid u+1}}
       \Phi(u/x)T_-(u)T_+(u+2).
\]

Then, with fixed-data constants,

\[
 \sum_{r\leq x^c}\left|S_r-
 \mathbf1_{(r,M)=1}\frac{x}{Mr}\left(\int_0^\infty\Phi(t)dt\right)C_{-+}(x)\right|
 \ll_{r_0,s_0,M,\Phi}x^{\sigma+c}. \tag{3}
\]

Here `r_0,s_0` denote the fixed numbers of slots, to distinguish them from the presieve divisor `r`. Moreover `C_{-+}=C_- C_++O(x^(-a))`, where `C_±` are the individual harmonic tuple sums.

**Proof.** If `(r,M)>1`, the central congruences are inconsistent and both terms vanish. Otherwise every long prime exceeds `r` and `M`. A nonzero contribution forces `(A,B)=1`, since they are odd and divide integers differing by 2. The conditions on `u` are `u=0 mod A`, `u=-2 mod B`, `u=b-1 mod M`, `u=-1 mod r`. They select one class modulo `M r A B`. Smooth summation over this class is `x/(MrAB) integral Phi+O_Phi(1)`, uniformly even when the modulus exceeds the support length. There are at most `(r_0+s_0)! floor(x^sigma)` coprime tuples: their squarefree product determines them up to finitely many permutations. Summing this rounding error over `r<=x^c` proves (3). The comparison of harmonic constants is the repeated-prime estimate from Proposition 1. QED.

The power saving in (3) is stronger than every fixed logarithmic saving after division by `x`. This statement is deliberately for the displayed elementary statistic: it does not silently include all D inert weights, moving candidate arrays, or a prime indicator. For combined mass at least 1, the same tuple-by-tuple rounding proof has no power-saving budget. For combined mass between `1/2` and 1, (3) supplies only a presieve ingredient; a separate, unresolved composite-removal/correlation bridge remains. Neither range has been turned into a new prime-conditioned partial law in this report.

## 6. Attempts to cross the prime-conditioning barrier

### 6.1 Putting both size statistics in the Type II endpoint

The natural new expression is

\[
 \sum_{m,n}\alpha_m\beta_n\mathcal W(mn-1)
       (T_-(mn-1)-C_-)T_+(mn+1). \tag{4}
\]

Its bounded core is `F(v)=(T_-(v)-C_-)T_+(v+2)`. Selected small primes do not affect the long factors of `v`, but they do affect those of `v+2`: `T_+(qv+2)` need not equal `T_+(v+2)`. Thus (4) does not meet D's invariance hypothesis.

The failure occurs at a definite algebraic step, not just in a theorem's wording. On writing `mn-1=ah`, the left core becomes `T_-(h)-C_-`, whereas the other statistic becomes `T_+(ah+2)`. In the Cauchy square it occurs as

\[
 T_+(ah+2)\overline{T_+(a'h+2)}
\]

inside the sum over different selected products `a,a'`, together with `mn-1=ah` and `m'n'-1=a'h`. Only a factor depending on `h` alone can be discarded in the source's Cauchy step while preserving its cancellative square. Pointwise boundedness of the two displayed factors does not allow their removal from that signed square. Taking absolute values earlier discards the cancellation being proved.

An exact toy witness is `h=33`, selected labels 3 and 5, and `T(v)=1_{101|v}`: `T(3h+2)=1`, `T(5h+2)=0`, `T(h+2)=0`. This is an algebraic check, not an asymptotic counterexample under the permitted band sizes. A new estimate for the weighted square might exist; it is not established here.

### 6.2 Using the general two-endpoint graph pairing

The extraction correlation normally has `F(u)G_P(u+1)`. Appending `T_+(u+2)` adds a third position. Putting it on the first physical vector makes shared-label stripping produce `T_+(D_R w+2)`, while putting `T_+(n'+1)` on the second physical vector produces `T_+(D_R(w+D_C)+1)` after stripping. Neither is the required invariant core at the stripped unit-shift endpoint. Norm control in S does not prove decay for these resulting comparison terms.

A more careful alternative was tested: divide the target integer by its designated padding labels *inside a mark-dependent second vector*, then attach `T_+(n'/P_padding+1)`. For the unsymmetrized raw edge with `P_padding=D_R`, this would give the desired shift. But S symmetrizes target slots independently. The target vector cannot recognize which of its labels the source shares. The symmetrized raw expression averages divisions by the other target labels too. It is not the desired marked statistic.

The finite diagnostic makes this mismatch exact: source `(462;3,7)`, target `(465;3,5)`, one shared padding label 3 and physical difference 3. For `T(v)=1_{13|v}`, dividing the target by the shared label gives `T(465/3+1)=1`; dividing by label 5 gives `T(465/5+1)=0`; target symmetrization gives `1/2`. This does not refute a redesigned colored graph construction. It shows why the cited black-box graph result does not yield the proposed cancellation simply by changing `g`.

### 6.3 Expanding the right statistic into long congruences

Expanding `T_+(mn+1)` into `mn=-1 mod B` makes coefficients separable by characters, but the character moduli contain long prime factors, each at least `x^a`. P's strongest scalar coefficient criterion covers logarithmic moduli, not these polynomial moduli. Summing over all `B` also requires aggregate control rather than a pointwise estimate with untracked constants. Classical BV handles the restricted range in Proposition 1; neither this expansion nor a fixed-modulus R006 character argument handles the full region. Specialized stronger distribution results would require their actual modulus/weight hypotheses to be checked. No assertion is made that `1/2` is the strongest known distribution exponent for every specially weighted modulus family.

### 6.4 Pairing the outer endpoints and placing primality in the middle

One can arrange a graph shift of 2 and hope to retain the central prime at `u+1`. But the midpoint is a function of the edge and its shared/comparison labels, not a function of one endpoint satisfying the source's hypotheses. Before shared stripping, the physical midpoint in a raw edge of difference `2D_R` is `D_R(w+1)`, divisible by `D_R`; testing it for primality plainly does not test primality of `w+1`. Attaching the test after dividing out `D_R` reintroduces dependence on which labels are shared and the symmetrization issue. Replacing primality by presieve and composites does not eliminate the need for a new three-position estimate.

### 6.5 Ordinary joint PD, arithmetic modes, and small factors

The substitution `p=2n+1` identifies `p-1=2n`, `p+1=2(n+1)`. The fixed factor 2 is negligible on the logarithmic scale, but the condition that `2n+1` is prime remains. J's ordinary joint law cannot simply be restricted to this density-zero set. O's binary Elliott theorem neither represents the third prime indicator nor supplies the required prime-scale error for the resulting moving-bin tests. A fixed positive log saving in one binary theorem cannot be upgraded by assertion to arbitrary precision through the whole signed extraction.

R010's phases multiply cleanly when a selected prime is stripped from *the same integer*. In contrast, a statistic of `av+2` has no such scalar multiplier relative to a statistic of `v+2`. Adding a fixed character or another Omega residue on either neighbor is at most a routine variant, not the joint size theorem. Fixed local tests can be encoded by finitely many prime progressions; R006's single size law combined with those tests is also routine. Small-factor models on subpower scales do not determine factors of size `p^t` for fixed `t>0`.

### 6.6 Sieve bounds and comparison events

The thin cofactor approach writes `p+1=2aQ`, `p-1=2bR`, so `aQ-bR=1`. An upper sieve for the associated three linear prime forms can bound narrow near-equality strips, but positivity/asymptotic independence over the whole region is not obtained merely by an upper bound. This route was not ignored: the current primary literature already develops it for strict largest-factor comparisons, as documented below. No version of that comparison argument is proposed as a new finding here.

A final targeted scan of the full read-only text cache also found the uniform two/three-form upper sieve in `An-asymptotic-formula-for-the-number-of-totients-September-25-2026/build/source/layers.tex`, `lem:sieve`. Its actual statement is an upper bound for the simultaneous primality of `n,An+1` and optionally `A'n+1`, not an asymptotic or a lower bound for the required marked neighboring-factor statistics. The “prime-conditional-bin” hit in `A-quadratic-bound-for-Jacobsthals-function-September-25-2026/build/sections/prime-paths.tex` concerns the conditional transition of a decreasing prime path; it is not conditioning consecutive integer partitions on a prime midpoint. Both inspected files are frozen as context. The scan and its precise matches are retained in `corpus-search.json`; its finite keyword coverage is not an exhaustive nonexistence theorem.

## 7. Exact missing prime estimate and what it would resolve

Here is a concrete target, expressed without an ambiguous “assume enough independence.” Fix `r,s>=0`, fixed slot exponent intervals bounded away from zero, and a fixed reduced class `b mod M`. Require the upper exponents to sum to at most `1-epsilon` **on each side separately**, for fixed `epsilon>0`. As before set `A=prod q_i`, `B=prod z_j`; all numerical prime tuples are distinct within a side, and retain only `(A,B)=1`. For large `x`, `(AB,M)=1`. Let `c(A,B)` be the CRT class in (CRT), and `DeltaLi=Li(2x)-Li(x)`.

The missing family is

\[
 \boxed{\quad
 \sum_{\substack{\mathbf q,\mathbf z\\(A,B)=1}}
 \left[\pi(2x;MAB,c(A,B))-\pi(x;MAB,c(A,B))
                    -\frac{\DeltaLi}{\varphi(MAB)}\right]
          =o(x/\log x).
 \quad} \tag{MI}
\]

Every slot family is fixed before the limit; a full uniform theorem over D's admissible families would be stronger than the fixed-box family needed here. There is **no absolute value inside the tuple sum** in (MI); requiring that would be unnecessarily strong. The classes and moduli are exactly specified, including their reduction and local exclusions. The combined modulus can approach `M x^(2-2epsilon)`. Individual PNT estimates for such moduli are neither claimed nor required; the issue is cancellation/structure in their aggregate.

The finite divisor-sum swap (2) and the main-term calculation in Proposition 1 show that (MI) is equivalent, for these boxes, to

\[
 N_M(x)^{-1}\sum_{\substack{x<p\leq2x\\p\equiv b\ (M)}}
 T_-(p-1)T_+(p+1)=C_- C_++o(1). \tag{5}
\]

This is an equivalence of explicit target statements, not a proof of either. Cross-side equal primes and long square powers cause only the previously proved negligible errors. Proposition 1 proves (MI) below combined mass `1/2`; Proposition 2 does not prove it even below combined mass 1. Even a hypothetical level-1 prime AP theorem used by this *direct* modulus-size argument would only cover combined mass below 1, not the full pair of simplexes. This is a limitation of the direct argument, not an assertion about everything such a theorem might imply by other methods.

For clarity, the full (5) family would suffice for joint PD: sample factors without replacement with probabilities proportional to their logarithmic masses, independently between the two neighbors conditional on `p`. Multiplying the factorial density `prod dt_i/t_i prod du_j/u_j` by the two ordered size-biased selection kernels cancels those coordinate factors and yields the product of the usual GEM(1) finite-prefix densities

\[
 \prod_{i=1}^r\frac1{1-t_1-\cdots-t_{i-1}}
 \ \prod_{j=1}^s\frac1{1-u_1-\cdots-u_{j-1}}
\]

on the two open simplexes. Each integrates to 1. Compact exhaustion therefore loses no prefix probability; the empty-side cases give the corresponding marginals. After a fixed number `k` of size-biased selections the limiting expected residual mass on each side is `2^(-k)`. Boundedness and prefix convergence give the same limiting expectation for the finite samples; Markov's inequality controls the sum of the two residual masses by `2^(1-k)/eta`. Let `x` tend to infinity for fixed `k`, then `k` tend to infinity, and sort. Truncation and continuity of decreasing rearrangement in `l^1` give product PD. This identifies the mathematical strength of the *unproved input*; it does not package an assumed input as a solved conditional finding.

### Requirements for a marked-extraction proof of (MI)

A route following D must actually supply both the replacement for (4) at arbitrary prescribed logarithmic precision and the three-position correlation remaining after allocation. It must also provide a joint progression input on every needed support, not just (3), whose support restriction stops at combined mass 1. Solving a scalar composite coefficient lemma alone is insufficient (the distinct gap already visible in i06).

For the allocation stage, a useful precise unresolved expression is

\[
 \sum_u\Phi(u/x)\mathcal W(u)(T_-(u)-C_-)T_+(u+2)
           W_{1,q_0}(u)W_{1,q_0}(u+1)G_P(u+1). \tag{6}
\]

Here `G_P` is D's exact stripped `j`-fold rough-factor core (`ext:allocation-core`), with active primes and inactive candidate primes removed in the prescribed tests. Dropping `T_+(u+2)` turns (6) into precisely `ext:correlation-to-use`; retaining it is the new task. An estimate `O_A(x/log^A x)` for all permitted fixed data, at arbitrary chosen `A`, or a fully justified suitable recombined substitute, is needed. Ordinary `o(x)` is insufficient. Unproved boundedness does not become cancellation merely by multiplying a known estimate by `sup T_+`.

All square errors, smoothing, coefficients, allocation factors, and the polynomially many signed active subsets must be absorbed at the **prime scale** `o(x/log x)`. In R010 the principal model is independent of the active subset on the physical integers; only *after* summing the coefficients `(-1)^|T| c_1^|P| j^|P|`, with `P=S union T`, does its size reduce to the positive product proxy times a retained-event probability in `[0,1]`. Bounding separate model terms absolutely is not a substitute. An I18 proof would need this same common-model identity with the extra shifted statistic retained, or an explicitly proved alternative, for every signed term. No such identity or analytic error estimate has been established here.

Finally the valid source order is: fix interior data and the progression cutoff exponent; fix the even sieve parameter `h`, hence `gamma` and finitely many composite lengths; choose Type II precision and sufficient fixed `K`; choose finitely many disjoint exponent arrays; take real `x -> infinity`; remove arrays by their number tending to infinity; then take `h -> infinity`, choosing a new sufficient fixed `K` each time. Constants may depend on the fixed arrays and disappear only in the first limit. D's final bound has the form `C e^(-h)/gamma+C sqrt(C_K/b_array)`, with `gamma^(-1)=(4h+3)/c_0`. No joint argument here has shown the same form or uniformity. Neither the array count nor the number of modes may be allowed to grow with `x` without new estimates.

## 8. Why ordinary convergence plus all marginal laws is not a bridge

There is a simple probabilistic diagnostic, not an arithmetic counterexample. Let `mu=PD(1)`, `delta_x=1/log x`, and generate a labeled mixture: with probability `1-delta_x` draw two independent samples from `mu`; with probability `delta_x` draw one sample and duplicate it. The two marginals are exactly `mu` for every `x`. The unconditional joint law tends to `mu tensor mu`, even in total variation. Conditional on the rare label, it is the diagonal coupling, not the product.

Attach independent fixed residue/parity/mode labels if desired; their independence from either marginal persists. This shows why ordinary joint convergence and strengthened marginal statements alone do not logically transfer to a rare prime condition. It does not model the actual integers, and it does not prove that the detailed analytic corpus cannot resolve (MI). It isolates the invalid probabilistic shortcut. The finite two-point version in the diagnostic script verifies these assertions with exact fractions.

## 9. Primary literature checks and significance limit

Early searches and a fresh final search covered joint largest factors of `p-1,p+1`, simultaneous smooth shifted primes, PD under primality conditioning, truncated largest factors, and local/common-factor obstructions. Queries, actual-statement locators, versioned URLs, retrieved HTML hashes, and the final raw search result are retained in `literature/`. Search summaries alone are not treated as theorem statements. External preprints are comparisons, not new premises used to prove (1) or (3), except the standard classical BV formulation explicitly identified above.

* **Genheng Zhao, “On the largest prime factors of p−1 and p+1,” arXiv:2609.35610v1, 28 September 2026.** Theorem 1.1 states positive proportions for both strict orderings. Propositions 3.5–3.6 bound a narrow near-diagonal strip above a fixed exponent greater than `1/2`, with a constant uniform in strip width. The proof uses the cofactor relation and a three-linear-form upper sieve. Its local factors explicitly account for exceptional primes and coprimality. Thus a proposed thin-strip/positive-ordering consequence is already directly represented in a primary preprint; it is not a new I18 result. [Actual version](https://arxiv.org/html/2609.35610v1).
* **Zhiyuan Yang, “On the largest prime factors less than y of consecutive shifted primes,” arXiv:2609.15166v1, 14 September 2026.** Theorem 1.4 states half-density for truncated orderings in its subpower `y` range; Theorem 1.6 gives a positive lower bound for fixed `y=x^alpha`, `alpha<17/32`, with the stated limiting behavior of its bound. The full untruncated half-density appears as a conjecture, not the theorem. The actual BV and upper-sieve statements were also read. These results preclude presenting a routine truncated ordering variation as a substantial new finding. [Actual version](https://arxiv.org/html/2609.15166v1).
* **Bharadwaj–Rodgers, “Large prime factors of well-distributed sequences,” arXiv:2402.11884v4.** Definitions, Proposition 2, Theorem 7, Lemma 8, and Remark 9 distinguish full PD from limited-total-mass tests at a smaller level of distribution. This is direct prior methodological coverage of the restricted-factorial baseline. It does not state the full joint neighboring-prime law. [Actual version](https://arxiv.org/html/2402.11884v4).
* **Kevin Ford, “Joint Poisson distribution of prime factors in sets,” arXiv:2408.03803v4.** Theorem 1 and its preceding probability model concern prime factors in sets for one shifted prime and quantify a small-factor approximation under the stated distribution hypothesis. The total-variation estimate becomes an approximation in a subpower truncation regime. The model's fixed-prime divisibility law is adjusted to primes in reduced progressions. It must not be promoted to independent full logarithmic factor partitions of both neighbors. [Actual version](https://arxiv.org/html/2408.03803v4).

No full product law was located in these targeted searches, but that is not a worldwide-priority claim and cannot compensate for the missing proof. The scoped outcome is no substantial new joint theorem proved. Proposition 1, Proposition 2, the CRT formulas, the diagnosis of specific failed substitutions, and the exact target (MI) are retained as reusable technical work, not as count padding.

## 10. Validation, provenance, and handoff

The exact standard-library diagnostic is [check.py](../experiments/i18_joint_prime_neighbors/check.py), with [results.json](../experiments/i18_joint_prime_neighbors/results.json). It checks 4,608 CRT/presieve systems, 768 prime-residue CRT systems, 38 valuation identities, 27 finite divisor-count swaps, the two algebraic stripping/symmetrization examples, and rare-event countermodels with exact rational arithmetic. Its zero failures support only those finite identities, not an asymptotic theorem. The proofs above are the mathematical justification for the propositions.

Run from the project root:

```sh
python frontier/experiments/i18_joint_prime_neighbors/check.py
python frontier/experiments/i18_joint_prime_neighbors/verify.py
```

The verifier checks frozen input hashes, pinned Git object identities against the frozen complete tree, versioned literature bytes, the diagnostic output, and the artifact seal. `artifact-seal.json` hashes every I18 artifact except itself and the generated validation report; it includes this report, scripts, all retained inputs, and literature evidence. `validation.json` records verification and checks whether the live local inputs still match their frozen versions. A concurrent parent edit is reported separately from corruption of the frozen input. Full details of this distinction are in the verifier.

No independent proof review or significance pass is asserted. Recommended handoff status: **I18 investigated; joint-size discovery remains unresolved; accepted count unchanged at four**. If a future attempt supplies (MI) or the complete marked bridge, it needs fresh proof and significance review of the actual new argument, including the restrictions and failures documented here.
