# i06 — Cubic reservoir: a completed scalar estimate and an unclosed rough correlation

2026-10-08. Premises: the pinned corpus `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` is true, and the reviewed R006 is available. **CR is not proved, even for `{2,−6}`. This round does not deliver the requested second substantial result.** It independently passes the three i05 propositions, proves the precise Hecke character–Mellin estimate needed by one lower-level interface, and cancels the resulting rough composite contribution. The remaining rough-predecessor correlation is stated with its quantifiers below. It is not relabeled as a theorem.

The [separate audit](../reviews/i05-joint-artin-r2.md) treats i05's proof and prior-art claims. All writes are confined to that audit, this report, and `frontier/{sources,experiments}/i06_cubic_reservoir/`. No agents, staging, commits, or shared edits were used; other research lanes were not duplicated.

## 1. Target and the modulus budget

Write `N(x)=pi(2x)−pi(x)`, `c(theta)=−log(1−theta)`, and fix `0<theta<10^−6`. Let

`L_0=Q(zeta_3,cuberoot(2),cuberoot(3))`, `E=Q(zeta_3)`.

The subscript on L_0 distinguishes the field from the analytic notation `L=log x` below. The group is `F_3² semidirect C_2`; the good translations satisfy `s≠0` and `s+t≠0`. There are four out of nine. As proved in i05 and checked independently, the maximal abelian subfield is E.

The requested CR instance is, for every fixed `24|M` and every reduced b reducing to 13 or 19 modulo 24,

\[
 \#\{x<p\le2x:p\equiv b\pmod M,\ P^+(p-1)>x^{1-\theta},
           2,-6\text{ both noncubes mod }p\}
 =\left(\frac{4c(\theta)}{9\varphi(M)}+o(1)\right)N(x).
 \tag{CR26}
\]

The proof sought must cover all these fixed moduli, or a sufficient family with a quantitative lower bound. In particular, for b_0=13 or 19, set

\[
 M_Y=24\prod_{5\le q\le Y}q,\quad
 R_Y=\{p:p\equiv b_0\ (24),\quad p\not\equiv1\ (q),\ 5\le q\le Y\},
 \quad
 w(Y)=\frac18\prod_{5\le q\le Y}\frac{q-2}{q-1}.
 \tag{1}
\]

Products here and below indexed by q are over primes. Then `w(Y) asymp 1/log Y`. R006 gives reservoir mass `c(theta)w(Y)` in R_Y for each fixed Y. The global middle-index tail is at most `(C_{2,−6}/Y+o(1))N(x)`. A lower bound `kappa(theta)w(Y)N(x)` with the same positive kappa for every fixed sufficiently large Y closes the budget. A sequence of positive constants kappa_Y is useful only with explicit dependence strong enough to make `Y kappa_Y w(Y)` exceed the tail constant. Nothing in this round supplies either lower bound.

The exact main term in (CR26), if proved class by class, would have the common factor `4c(theta)/9`. Constants in convergence rates may depend arbitrarily on fixed M; that does not damage the argument, since Y is frozen before the x-limit. It is the leading lower-bound constant, not the threshold, whose deterioration would be fatal.

## 2. Four Hecke traces: the exact nonabelian part

For `a in {2,3,6,12}`, let eta_a be the nontrivial cubic Hecke character of `E(cuberoot(a))/E`, with zero extension at its finite conductor. On unramified prime ideals,

`eta_a(mathfrak p)=(a/mathfrak p)_3`.

Cubic reciprocity makes this a finite-order ray class character; alternatively use the Kummer Artin character. All four a are noncubes over E by the rational norm argument. Complex conjugation c satisfies `eta_a^c=eta_a^−1`. Define, at rational primes p not dividing 6,

\[
 T_a(p)=\begin{cases}
 \eta_a(\mathfrak p)+\eta_a(\overline{\mathfrak p}),&p\equiv1\pmod3,\quad N\mathfrak p=p,\\
 0,&p\equiv2\pmod3.
 \end{cases}
 \tag{2}
\]

The first value is independent of the prime chosen above p. It is 2 if a is a cube modulo p and −1 otherwise. These are the traces of the four nontrivial two-dimensional irreducible representations of the order-18 group, one for each projective cubic direction.

At a split prime with cubic coordinates (s,t), their exponents are `s,t,s+t,2s+t`. Set

\[
 B(p)=T_3(p)+T_{12}(p)-2T_2(p)-2T_6(p).
 \tag{3}
\]

There is the exact identity, for p=1 modulo 3,

\[
 \mathbf1_{2,-6\text{ noncubes mod }p}=\frac49+\frac{B(p)}9.
 \tag{4}
\]

**Proof.** Write `z=eta_2(mathfrak p)`, `v=eta_3(mathfrak p)`. A noncube indicator is `(2−z−z^−1)/3`. Multiply this expression for z and zv. The mixed terms are `z²v+(z²v)^−1+v+v^−1`, giving (4). Equivalently enumerate the nine possible (s,t). On good vectors B=5; on bad vectors B=−4. The average of B over the nine vectors is zero. The factor −1 in −6 is a rational cube. This proves every normalization in (4). □

For all unramified rational primes, the corresponding identity has constant part `(2/9)(1+chi_{−3}(p))` instead of 4/9. We use (4) only in the compatible split progressions.

Consequently, given R006, (CR26) is **equivalent** to the single cancellation statement

\[
 \sum_{\substack{x<p\le2x\ p\equiv b\ (M)\
                  P^+(p-1)>x^{1-\theta}}} B(p)=o(N(x))
 \qquad(M,b,\theta\text{ fixed as above}).
 \tag{MT}
\]

Separate cancellation of all four T_a is sufficient and stronger. No independence of the two cubic residue symbols is asserted on the large-factor reservoir. The four-direction decomposition only identifies the missing signed moment.

For the tail application it would already suffice that, for every fixed sufficiently large Y,

\[
 \liminf_{x\to\infty}\frac1{N(x)}
 \sum_{\substack{x<p\le2x\p\in R_Y\P^+(p-1)>x^{1-\theta}}}B(p)
 \ge -2c(\theta)w(Y).
 \tag{MT-lower, unproved}
\]

Indeed (4) would then leave at least `(2/9)c(theta)w(Y)` in lower proportion. Choosing Y so that `C_{2,−6}/Y < c(theta)w(Y)/18`, followed by the already-proved large-index exception estimate, leaves positive proportion. Thus (MT-lower) is an explicit sufficient tolerance, not an unnecessarily demanded exact joint asymptotic. The logically sharp budget only asks that the sum in (4) leave more than the actual global tail; (MT-lower) gives a convenient common margin.

## 3. What cubic reciprocity does and does not encode

Anwar–Pappalardi Lemma 5 gives, for these bases, modulus 72 in `O_E=Z[omega]`: a fixed primary prime-element residue modulo 72 preserves both cubic symbols. Their convention can be replaced by the unique generator congruent to 1 modulo 3; multiplying by −1 changes neither ideal nor cubic symbol. A rational residue of the norm does not determine the ray class of that generator.

For example,

* `pi=−2−9 omega` has norm 67 and symbols `(eta_2,eta_3)=(omega,1)`;
* `rho=10−3 omega` has norm 139 and symbols `(omega,omega²)`.

Both rational primes are 67 modulo 72 and 19 modulo 24. The first is good and the second bad. These identities are checked using `omega=−a/b mod p` when `pi=a+b omega`, followed by exact modular exponentiation. They are a concrete example of i05's general maximal-abelian-subfield argument.

There is an additional precise warning about norm twists. For every rational integer n coprime to the conductor,

\[
                      \eta_a((n))=1. \tag{5}
\]

To prove this, the ideal (n) is fixed by conjugation, while `eta_a^c=eta_a^−1`; hence its value has order dividing both 2 and 3. It is therefore 1. At split rational primes the two ideal values cancel; at inert primes the rational cubic residue in `F_(p²)` is also 1. Thus evaluating the Hecke character at the rational principal ideal (p) discards precisely the nontrivial trace in (2). It cannot replace T_a(p).

Lifting the graph to Eisenstein elements would restore invariance under rational scalar dilation for the ideal character, but it changes the predecessor geometry:

\[
 N(qz)-1=q^2N(z)-1\ne q^2(N(z)-1),\qquad
 N(z+d)-N(z)=\operatorname{Tr}(z\bar d)+N(d).
 \tag{6}
\]

The error in the first equality is `q²−1`, and the second expression depends on z. The accepted graph is for rational integer affine shifts with shared scalar prime labels. No ideal/lattice graph theorem for `N(z)−1` is among the interfaces used here. Replacing its underlying integers by prime ideals is a new theorem requirement, not a change of notation. The cubic Gauss-sum companion also does not supply that theorem: its dispersion input concerns multiplicative ideal variables and Gauss-sum weights, with `AB asymp X`, `X^.32≤B≪X^.5`, and height at most `X^.17`, rather than the norm-minus-one reservoir.

## 4. A proved scalar interface from the accepted Hecke strip

This section closes a limited part of i05 §7's fourth attempted approach. The following is a standard zero-free-strip deduction with all relevant ranges supplied, not a novelty claim.

**Lemma SL (proved under the accepted QRH manuscript).** Fix a in `{2,3,6,12}`, a real `epsilon_0>0`, and fixed `A_0,B,C>0`. Put `L=log x`. Let

`x^epsilon_0 ≤ H ≤ C_0 x`, `I subset [H,2H]` be any interval,
`k≤L^A_0`, `chi mod k` be any Dirichlet character, principal or imprimitive, and `|u|≤x²`.

For every fixed `0<epsilon<1/8`, uniformly in these variables,

\[
 \left|\sum_{p\in I}T_a(p)\chi(p)p^{iu}\right|
 \ll_{a,\epsilon,\epsilon_0,A_0,C_0}
                    H^{7/8+\epsilon}L^4.
 \tag{SL}
\]

Omit the finitely many primes dividing 6. In particular, if `X asymp x`, the scalar sequence

\[
 \alpha_m=\mathbf1_{m\in I,\ m\ {m prime}}T_a(m)m^{iv},
          \qquad |v|\le L^C,
 \tag{7}
\]

satisfies P `lem:marked-coefficient-transfer` for every fixed logarithmic accuracy and the entire range `|t|≤2X L^B`, when tested against `chi(m)m^{it}`. Its scalar comparison model is **zero**. It is supported on W-rough integers and bounded by 2, with `W=exp(L^.24)`.

**Proof.** Let `psi=eta_a (chi circ N)` over E. The conductor of its primitive associate has norm at most `C_a k²`; any additionally deleted Euler primes divide a fixed ideal times (k). This character is nonprincipal for every chi. Indeed norm twists are invariant under conjugation of ideals. If psi were principal, conjugating and dividing would give `eta_a²=1`, contradicting its nontrivial cubic order. This argument includes principal and imprimitive chi.

The accepted QRH `thm:main` gives no zero for any such primitive Hecke L-function in `Re s>7/8`. Its `lem:logarithmic-control`, with the theorem already available, gives on `Re s≥7/8+epsilon` the bound

\[
 |L'_E(s,\psi)/L_E(s,\psi)|
       \ll_{a,\epsilon}\log\{(k+2)(|\Im s|+3)\},
 \tag{8}
\]

through the bounded real strip needed here; the Euler series handles larger real parts. Deleted Euler factors add at most `O_epsilon(log(k+2)+1)` there: each denominator `N(mathfrak p)^s−eta(mathfrak p)` has modulus at least `N(mathfrak p)^(7/8+epsilon)−1`, and the sum of the logarithms of the deleted norms is `O_a(log(k+2))`.

Write

`−L'_E/L_E(s,psi)=sum_(n≥1) b_psi(n)n^(−s)`.

These coefficients are supported on rational prime powers and satisfy `|b_psi(n)|≤2 Lambda(n)`. For unramified rational primes,

`b_psi(p)=T_a(p)chi(p)log p`.

The inert primes have no prime ideal of norm p, giving the zero in (2). At powers, the degree-two bound follows by summing the residue degrees of ideals above a rational prime.

Apply truncated Perron to `sum_(n≤y) b_psi(n)n^(iu)` with a half-integer y, `H/2≤y≤3H`, starting at `Re s=1+1/log(3H)` and height `T=x^10`. The coefficient bound gives a truncation error `O(H L^3/T)`; the half-integer convention keeps every integer at distance at least 1/2 from y. It represents any desired integer cutoff exactly. Shift the rectangle to `sigma=7/8+epsilon`. The integrand is

`−(L'_E/L_E)(s−iu,psi) y^s/s`.

There is no pole in the crossed strip, including at `s=1+iu`, because psi is nonprincipal. On both horizontal segments (8) gives a bound `O(H L/T)`. On the new vertical segment it gives

`O(y^sigma log((k+2)(T+|u|+3)) integral_(−T)^T |sigma+it|^(−1) dt)`

`=O(H^sigma L²)`.

These bounds are uniform for `|u|≤x²`, and prove the desired bound, with room in L^4, for von Mangoldt coefficients on arbitrary subintervals of `[H,2H]`. Prime powers of exponent at least two contribute `O(H^(1/2) log²(3H))` absolutely. Partial summation by `1/log p` removes the remaining logarithm; retaining L^4 gives (SL). Endpoint inclusion/exclusion changes at most `O(log H)` at the von Mangoldt stage and is absorbed.

For the source coefficient interface, replace u by `t+v`. For every fixed B,C and `X asymp x`, its absolute value is less than x² for all sufficiently large x. After division by H, (SL) is at most

`H^(−1/8+epsilon)L^4 ≤ x^(−epsilon_0(1/8−epsilon))L^4`,

which is smaller than `L^(−A)` for every prescribed fixed A. Support and size are as stated because `H≥x^epsilon_0>W`. All choices of accuracy are available before the source chooses its inert-band number K. □

This proof uses a source **logarithmic derivative bound in a fixed strip**, not partial summation of a low-frequency Chebotarev error up to height x². The latter would lose a factor of the height and would be insufficient. It also uses the correct ideal character; it does not falsely regard a cubic character as a Dirichlet character of a rational modulus.

For any fixed additional rational modulus M, insert a character modulo M and replace k by `lcm(k,M)≤L^(A_0+1)` eventually. Thus SL covers every fixed modulus later used in (1), with the same exponent. This establishes a scalar interface, not the common positive reservoir factor.

### A natural arithmetic extension and a completed composite estimate

Define

\[
 A_a(n)=\sum_{N\mathfrak a=n}\eta_a(\mathfrak a),
       \qquad L_E(s,\eta_a)=\sum_{n\ge1}A_a(n)n^{-s}.
 \tag{9}
\]

It is multiplicative, `|A_a(n)|≤tau(n)`, and `A_a(p)=T_a(p)` away from 6. On squarefree n its weight is the product of the prime traces. At a split unramified p its Euler recurrence gives `A_a(p²)=T_a(p)²−1`; it is not the completely multiplicative extension of its prime values. This fixes a specific model, rather than leaving composite Frobenius values arbitrary.

**Lemma CC (proved).** Fix `0<gamma<1/2`, a reduced class b modulo a fixed M, a fixed smooth compactly supported Phi in `(0,infinity)`, and `D>0`. Use P's inert marking arrays and weight mathcal W, and any source-permitted bounded invariant F. For K sufficiently large in terms of these fixed data, independently of the subsequent inert-band exponents,

\[
 \sum_{\substack{v\equiv b\ (M)\P^-(v)>x^\gamma\v\ {m composite}}}
  A_a(v)\Phi((v-1)/x)F(v-1)\mathcal W(v-1)
          \ll x(\log x)^{-D}.
 \tag{CC}
\]

The implicit constant and threshold may depend on the fixed inert array, as in the source. This lemma is not a prime-count lower bound.

**Proof.** Remove v divisible by a square of a prime exceeding `x^gamma`. There are `O(x^(1−gamma))` such integers in the support. Cauchy and a fixed divisor moment, using `|A_a(v)|≤tau(v)` and bounded F and mathcal W for fixed K, give an absolute error `O_K(x^(1−gamma/2)L^C)`. It saves every fixed logarithmic power. A remaining v has a bounded number `2≤j≤J_gamma` of prime factors. Count its ordered factorizations with factor `1/j!`; (9) makes the coefficient the product of T_a at those primes.

Select the first prime m and let n be the product of the other j−1. Their dyadic scales are both at least a fixed positive power of x and have product comparable to x. The product congruence is exactly

`1_(mn=b mod M)=(1/phi(M)) sum_(chi_0 mod M) conjugate(chi_0(b)) chi_0(m)chi_0(n)`.

Take alpha in (7), with the extra chi_0, and beta the convolution of the remaining weighted prime indicators, with chi_0(n). Beta is rough and bounded by a fixed divisor function times a fixed constant. The divisor-moment truncation in D §7, equations leading to `ext:proxy-replacement`, bounds its discarded part by any prescribed negative logarithmic power after clipping at a fixed power of L. Its exponents do not depend on K.

Separate the smooth product cutoff by Fourier inversion in `log(mn/x)`, as in that same source argument; its tail costs an arbitrarily small log power and its retained twists have `|v|≤L^C`. The replacement of `(mn−1)/x` by `mn/x` costs only a fixed log power in the whole sum. SL verifies P's scalar criterion for the selected prime slot, with zero proxy. P then bounds every retained bilinear sum by an arbitrary negative log power times x. Choose accuracy after the finite j-range, dyadic, character, Fourier, and truncation losses, then choose K. No two-sided active-group theorem or Chebotarev-selected interval is used. Restore the square errors. This proves CC. □

For D's centered long-factor statistic, clip `f_x−C_x` to its bounded range and rescale to obtain F, precisely as D does. Its invariance holds because every long slot is disjoint from the inert bands. Lemma CC therefore applies to the exact centered statistic needed below.

## 5. The still-missing rough estimate and a quantified sufficient interface

Lemma CC suggests an actual alternative to forcing a trace into D's invariant second core: subtract trace-weighted composites directly, using SL. But one must first control the trace-weighted rough sum. D's initial ordinary-integer progression/sieve calculation does not establish that control for (9).

Here is one sufficient, quantified interface. It is deliberately stated as **unproved**. It is stronger than the minimal signed moment (MT), but weaker in scope than a general Chebotarev–PD theorem.

**Missing interface RP.** Fix `24|M`, reduced b=13 or 19 modulo 24, a in `{2,3,6,12}`, a nonnegative fixed smooth Phi, and a one-slot interval

`I_x=(x^alpha,x^beta]`, with `1−theta<alpha<beta<1`.

Let `f_x(u)=sum_(q in I_x)1_(q|u)` and `C_x=sum_(q in I_x)1/q`. Choose the source presieve constant `0<c_0<epsilon/2` for an epsilon satisfying `epsilon<min(alpha,1−beta)`. For each fixed sufficiently large even h put `gamma=c_0/(4h+3)`. Let K be sufficiently large for CC and the source inert arrays, and let `m_W>0` be the source model mean of an inert array. The needed statement is

\[
 \limsup_{x\to\infty}\frac{\log x}{x m_{\mathcal W}}
 \left|\sum_{\substack{v\equiv b\ (M)\P^-(v)>x^\gamma}}
 A_a(v)\Phi((v-1)/x)\mathcal W(v-1)
               (f_x(v-1)-C_x)\right|
       \le C_{M,a,\alpha,\beta,\Phi}\frac{e^{-h}}\gamma.
 \tag{RP, unproved}
\]

The constant on the right must be independent of h, K, and the particular fixed inert array; vanishing errors and thresholds may depend on them. It would also suffice to prove a zero right side for each sufficiently small fixed gamma and every needed inert array. The formula identifies the rough model **A_a**, the factor being centered, the marked normalization, the progression, the scale range, and the necessary order of limits.

If RP were available, CC would remove its entire composite contribution. To remove the inert marks, use D's nonnegative deweighting square (or the already-audited R006 version). Since `|T_a(p)|≤2`, Cauchy bounds the additional signed weight by twice the same unconditioned square estimate. For B disjoint inert arrays the resulting unmarked centered prime sum has normalized limsup at most

`C_(M,a,alpha,beta,Phi) e^(−h)/gamma + C sqrt(C_K/B)`.

Fix h, then K, then a finite B; take x to infinity, then B to infinity, then h through arbitrarily large even integers. SL with fixed-modulus character orthogonality already gives `sum_(p=b mod M) T_a(p)Phi((p−1)/x)=o(x/log x)`. The centering term can therefore be removed after deweighting. This would prove the trace-weighted one-slot interior intensity vanishes.

Only one-slot intensities near the top are necessary here. For `alpha>1/2` there is eventually at most one numerical prime divisor in the slot. Approximating dyadic cutoffs smoothly and covering the compact interval `(1−theta+eta,1−eta]` by finitely many slots gives trace cancellation there. The omitted lower and upper slivers have unweighted AP reservoir mass tending to zero as eta tends to zero, by R006's continuous PD marginal in that fixed progression. The bound `|T_a|≤2` dominates their weighted contribution. First take x to infinity, then eta to zero. This would prove (MT) for each trace, hence (CR26) for **all** fixed compatible M, and would close (1)'s tail budget with the exact common factor.

This paragraph is a checked implication with the explicit missing premise RP. It is not a proof of RP or CR.

### Why the elementary presieve argument does not supply RP

Writing (9) as a sum over ideals, and then primary generators z, converts the central divisibility test into

`q | N(z)−1` for a long rational prime q, while the trace is a ray class character of z. The original CRT count instead has a one-dimensional free integer variable after writing `u=q d v`. These are different counting problems. Even without the rough condition, counting lattice residues `N(z)=1 mod q` has a boundary error of scale at least that produced by summing about q residue classes in a two-dimensional lattice; naive absolute summation over `q>x^(1−theta)` is far outside a usable range. No cancellation across those large norm-congruence moduli has been proved here.

Equivalently, for the prime version the unique-large-factor identity is

\[
 \sum_{\substack{x<p\le2x\p\equiv b\ (M)\P^+(p-1)>x^{1-\theta}}}T_a(p)
 =\sum_{m<2x^\theta}\ \sum_{\substack{Q>x^{1-\theta}\Q\ {\rm prime}\
                       x<mQ+1\le2x\mQ+1\ {\rm prime}\mQ+1\equiv b\ (M)}}T_a(mQ+1).
 \tag{10}
\]

In the target classes the outer cofactor is a multiple of 6. SL concerns `T_a(p)chi(p)p^(it)` on prime intervals. It does not concern a product of two prime indicators with `T_a(mQ+1)` as in (10). Applying SL to the Q-variable would change its coefficient to `T_a(Q)`, which is a different function. Applying P with n=1 violates its explicit requirement `H_m,H_n≥x^delta`.

## 6. Resolution of each attempted route in i05 §7

1. **Insert a Frobenius indicator into the invariant core.** Still invalid. D `thm:two-sided` requires `G(n)=G(n_*)` after removing all active prime powers. For a completely multiplicative extension f, a shared product contributes `f(D_R)`; for the natural coefficient A_a, multiplicativity supplies `A_a(D_R)` off coprimality exceptions, with additional local recurrences on overlaps. Neither is identically one. The independent script exhibits exact failures of stripping. For example, for the normalized completely multiplicative extension with `f(7)=f(13)=−1/2`, `f(7·13)=1/4≠f(13)`.

2. **Conjugate weights at the two physical endpoints.** For a unit-valued completely multiplicative f, shared factors cancel, but the raw term is weighted by `f(w) conjugate(f(w+1))`, not by a function of the prime w+1 alone. Multiplying the first physical endpoint by the inverse weight just reinstates the lost shared factor. The trace T_a and natural A_a are not unit-valued; in particular A_a vanishes at inert rational primes. The endpoint-energy statement is for the original centered long-factor core. No inverse-weight or modified-energy estimate is obtained here.

3. **Use only split active primes.** Still outside the accepted contract. D §6 explicitly requires every big group to be all primes in an interval; D §7 constructs full candidate intervals. Neither ordinary Chebotarev nor SL extends the graph comparison, successful-mark selection, allocation, and deweighting simultaneously to a thin set of primes. For an artificial choice of cubic orientation, the very meaning of multiplying rational-prime Frobenius labels additionally needs a model. No such substitution is made.

4. **Scalar coefficient transfer.** Partially resolved. SL verifies the exact full range for each **centered trace prime coefficient**, with zero scalar model; CC proves the corresponding rough-composite cancellation. The constant character part of the good indicator is already supplied by R006. What remains is RP for the natural arithmetic extension A_a, not an assumed “trace times the ordinary rough density” proxy. The source's ordinary-integer rough presieve cannot be imported unchanged. Thus the difficult extraction has been isolated more sharply, but not completed.

5. **Direct use of the E-Hecke strip or cubic reciprocity.** The strip is strong enough for SL. It is not a level-one distribution estimate for the shifted prime sequence. At a growing congruence modulus d, a direct character expansion plus an absolute per-character strip bound supplies no factor `1/phi(d)` in the error; summing such errors can at best pay a limited range, not all `d` near `x^(1−theta)`. The alternative switched form (10) retains a primality condition on the quotient. Reciprocity gives a prime-element ray class, while (5)–(6) explain why its transfer to the rational dilation graph fails. None of these limitations is a universal impossibility theorem for a different argument.

## 7. Primary prior-art screen and novelty verdict

The prior-art check concerns the actual joint statement, not merely the words “simultaneous primitive roots.” Search records are saved under the assigned source directory. I read the relevant primary theorem statements rather than treating search snippets as evidence.

* [Moree–Stevenhagen](https://arxiv.org/pdf/1203.4313v2), Theorems 5.6 and 6.2, already gives the arbitrary dependent signed-base algebraic criterion. The prime-density interpretation is GRH conditional. This rules out claiming novelty for Q/F/C.
* [Anwar–Pappalardi](https://www.impan.pl/shop/publication/transaction/download/product/92279), Lemmas 1, 4, 5 and the final norm-polynomial construction, already supplies quadratic realization and cubic ray-class realization. Its Hypothesis-H conclusion is infinitude, not (CR26).
* [Bharadwaj–Rodgers v4](https://arxiv.org/pdf/2402.11884v4), Theorem 7, requires level-one well-distribution for full PD. Lemma 8 gives correlation information only on the simplex below the available distribution level; Theorem 11 bounds the near-one largest-factor event **above**, not below. Neither marginal PD nor a positive Chebotarev distribution level meets those hypotheses at the near-one slot needed here.
* [Vatwani–Wong, *Patterns of primes in Chebotarev sets*](https://www-math.nsysu.edu.tw/~pjwong/stuff/chebotarevprimes.pdf), §4, Theorem 4.1, records Chebotarev Bombieri–Vinogradov levels, initially below `min(2/|G|,1/2)` and improved under an Artin-holomorphy condition. Even a level approaching 1/2 does not provide the near-one predecessor intensity. Its prime-pattern theorem is not CR.
* The remaining i05 primary references were checked at their actual statements: Lenstra (1977), Theorems 3.1, 4.1, 4.6, separates algebraic nonvanishing from GRH prime density; Lenstra–Moree–Stevenhagen, Theorems 5.7–5.8 and §6, treats progression and near-primitive-root entanglement; Moree's AP paper, Theorems 1–3, evaluates the GRH single-base progression density; Järviniemi–Perucca, Theorem 4.1 and Lemma 3.3, gives GRH mixed-index/Frobenius density and finite automorphism criteria. The last was read in i05's saved publisher text after a fresh DOI opening failed. None provides the large-predecessor-factor conditioning in (CR26). Their source links and hashes are retained in i05's manifest and this round's verification record.

These comparisons do not certify that nobody has proved (CR26). They identify no established duplicate in the primary sources actually examined and, more importantly, identify no theorem there that fills RP. Search hits about averaging bases or about primitive-root values of polynomials were not used as proofs of this fixed-pair Frobenius/large-factor joint statement.

SL is a standard consequence of the accepted zero-free strip; CC is a direct use of the accepted scalar-transfer interface with a fixed finite convolution. The representation-theoretic identity and reciprocity diagnosis are elementary or classical. Their combination is useful research progress in this project but does not meet the requested nonroutine-novelty gate. **Separate verdicts:** the displayed proofs of SL and CC are complete under the stated source contracts; RP, MT, and CR are unproved; no substantial new result is claimed; worldwide novelty is not certified.

## 8. Source ranges, integrity, and reproducible diagnostics

Source abbreviations D and P are those of R006/i05. New Q denotes

`preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex`.

The exact interfaces used are:

* Q `thm:main`, lines 106–111, gives the all-height, all-finite-order E-Hecke zero-free half-plane `Re s>7/8`.
* Q `lem:logarithmic-control`, beginning at line 1530, supplies the conductor/height-uniform logarithmic-derivative bound a fixed distance to the right of the zero supremum. Its preceding `lem:hecke-strip-growth` and its proof fix the conductor convention. The cited derivative conclusion, rather than an upstream analytic audit, is used in SL.
* P `sections/08-type-ii.tex`, `thm:marked-type-ii` and `lem:marked-coefficient-transfer`, fixes `H_m,H_n≥x^delta`, rough support, size, invariant F, all `k≤L^A_0`, and all `|t|≤2XL^B`. It allows arbitrary intervals for alpha and chooses K after fixed coefficient losses, independently of the band exponents.
* D `sections/07-extraction.tex`, the composite replacement paragraphs at lines 234–318, supplies the divisor truncation, square-error, cutoff separation, and clipping procedures used in CC. Its `ext:prime-deweight-square` is used only in the explicitly conditional RP implication.
* D `sections/06-correlations.tex`, lines 10–80, states the full-interval and invariant-core restrictions. Equations `cor:stripping-normalization`, `cor:stripped`, and `cor:U-form` identify the failed weighted extension. D extraction `ext:allocation-core` and the full candidate intervals at lines 319–329 verify that selecting only split primes would change the contract.
* The cubic Gauss-sum companion's `sections/background-type1.tex`, lines 1–65, states the primary-generator, cubic reciprocity, and nonprincipal Kummer character conventions; `sections/dispersion.tex`, `prop:dispersion`, has the different scales described in §3. No dispersion estimate from that companion is imported into CR.
* P `sections/07-splitting.tex`, `spl:field-bounds`, `spl:smooth-estimate`, and the all-q displayed consequence supply the already-reviewed global tail, with width `10^−6`, not the stronger but field-restricted Q width.

All new upstream downloads use immutable raw URLs at the pin and match the complete preprint tree by Git-blob SHA-1. The inherited i05 manifest is independently rehashed; this checks integrity only. Important SHA-256 values are:

* Q complete LaTeX: `42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3`.
* P scalar-transfer section: `97b1d9b0456a5951a25bbd9ee297da2c275a9c63e202aef139ad63e2c834794e`.
* D extraction section: `975713ca85a0318b26b17886afae993052bf3525bb020b3498f5cbf04c835f49`.
* Cubic Gauss-sum arithmetic section: `1c7be908c862dc440772964cfdd59e095e7b0f079cec11d99f5c7a9644198dd1`.
* Bharadwaj–Rodgers v4 PDF: `ed904c2bede049703b37f1e2ff68b376aecbb15164c77ab5885b22654f47bad8`.

The PDF hash is not the HTML hash recorded in earlier project rounds. [verification.json](../sources/i06_cubic_reservoir/verification.json) records full paths and hashes; [new-source-manifest.json](../sources/i06_cubic_reservoir/new-source-manifest.json) records immutable URLs; [literature-manifest.json](../sources/i06_cubic_reservoir/literature-manifest.json) distinguishes successful PDFs and retrieval failures.

Reproduce from the repository root:

```bash
python3 frontier/experiments/i06_cubic_reservoir/reproduce_i05.py
python3 frontier/experiments/i06_cubic_reservoir/independent.py
python3 frontier/sources/i06_cubic_reservoir/verify.py
```

The first output is byte-identical to i05's original. The independent experiment enumerates the nine translations and all 324 ordered group commutators; verifies (4) at 4,784 split primes below 100,000; checks 9,568 oriented primary generators and cubic labels, including all 432 occupied primary unit residues modulo 72; checks rational-principal-ideal cancellation; verifies eight exact CRT union weights; and records 48 exact-integer large-factor diagnostics in dyads up to two million. Thresholds `Q^4>x^3` and `Q^10>x^9` avoid floating-point comparisons. The count identity `9·good=4·reservoir+sum B` holds in every diagnostic.

One diagnostic illustrates a severe finite-size effect: at `x=10^6`, theta=1/10, the class 13 modulo 24 has no reservoir primes, whereas class 19 has 594, of which 249 are good. For class 19 these counts are unchanged on imposing exclusions through Y=11: the only possible cofactor is m=6, so the extra exclusions are automatic. This is not numerical evidence of a modulus-uniform limiting constant.

Those numerical theta values, 1/4 and 1/10, do **not** test the requested regime. In fact, in these compatible classes and for large x, `6|m` in `p−1=mQ`; hence the target reservoir is empty unless `x^theta>3`. For class 13 modulo 24, `12|m`, strengthening this to `x^theta>6`. Even at theta=`10^−6`, the weaker condition already requires `log x>1,098,612`, before one can discuss an asymptotic. The finite runs are checks of algebra, normalization, and implementation only, never evidence of tiny-theta density or of the analytic lemmas.

The useful next obligation is the explicit RP estimate, or directly the weaker signed moment MT-lower with the full modulus budget. Proving only a scalar prime estimate, a fixed-M local density, or another finite compatibility criterion would leave that obligation open. This round ends with that failure stated, rather than treating the conditional implication as the requested result.
