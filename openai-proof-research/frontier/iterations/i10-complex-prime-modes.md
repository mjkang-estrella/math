# i10 — A physical principal model for complex prime-predecessor modes

Date: 2026-10-08 (session date). Premise: all applicable theorems at
`openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are true; R006 and R008
are accepted. This is a fresh continuation of i07, not a reopening of its
finished alternatives or an audit of the corpus.

**Author status: completed candidate proof, for independent parent validation.**
The new bridge is a principal model on actual integer positions, common to
every active set. It has exact small-prime covariance, matches the low
frequencies and presieve progression sums, and has a separate high-frequency
proof. The model terms are recombined into the positive coin partition before
taking absolute values. Their uniform smallness then suffices at prime
normalization. No R number or change to the accepted finding count is made.

The construction below is not scalar recentering and does not suppress a
nonzero Selberg–Delange term. Its density, including all retained lower terms,
is given explicitly in (3). The principal model itself is nonzero.

## 1. Statement and dependencies

For a prime p≥3 let V(p) be the ranked logarithms of its predecessor's prime
factors, with multiplicity, divided by log(p−1). Let V have PD(1).

**Theorem CP (under the stipulated corpus).** Fix M≥1, (b,M)=1, m≥3, k≥1,
a residue a modulo m, and a continuous complex function H on [0,1]^k. Then

\[
 \frac1{\pi(X;M,b)}\sum_{\substack{3\le p\le X\\p\equiv b\ (M)}}
 1_{\Omega(p-1)\equiv a\ (m)}H(V_1(p),\ldots,V_k(p))
 \longrightarrow \frac1m\mathbb EH(V_1,\ldots,V_k).                 \tag{1}
\]

The same statement holds in terminal dyads with their class-prime
normalization. Every parameter displayed here is fixed before X tends through
real values to infinity. No rate, growing modulus, arbitrary multiplicative
function theorem, or priority certification is asserted.

We prove the following genuinely additional analytic assertion. Fix a
nonreal root of unity z and write f_z(n)=z^Ω(n). For each fixed nonempty
interior tuple statistic

\[
 T_x(n)=\sum_{\boldsymbol\ell}1_{\ell\mid n},\quad
 \ell=\ell_1\cdots\ell_d,\quad
 \ell_i\ge x^\epsilon,\quad \ell\le x^{1-\epsilon},\quad d\ge1,
\]

the tuples being ordered, numerically distinct, and in D's specified slots,
and each fixed smooth compact cutoff Φ,

\[
 \sum_{p\equiv b\ (M)}\Phi((p-1)/x)f_z(p-1)T_x(p-1)=o(x/\log x).
                                                                  \tag{2}
\]

Write C_x=Σ_ℓ1/ℓ=O_{d,ε}(1). Boundedness of T_x on x^{O(1)} ranges is
used repeatedly. The proof works separately for each fixed nonreal z; it
does not infer other roots from z=i or from z=−1.

Source prefixes are exactly those of i07: D is the Poisson–Dirichlet
prime-predecessor paper; S the weighted dilation graphs paper; P the
primitive-root coefficient-interface paper; Z the September 30 quasi-RH
paper. The retained immutable files and label ranges are in
[the manifest](../sources/i10_complex_modes/retrieval-manifest.json) and
[locators](../sources/i10_complex_modes/source-locators.json).

The actual contracts used are D `prop:graph-transfer`, `prop:ideal-family`,
the physical norms and shared-label stripping in §6, its bilinear multiplier
and local Mellin reduction, the small-prime exceptional-set and sparse Gram
proofs, D `lp:prime-polynomial` and `lp:log-phase` with their subinterval
uniformity, D `lem:block-sieve`, and the positive proxy/coin/allocation/
deweighting identities in §7. P `lem:marked-coefficient-transfer` supplies
the original scalar coefficient interface in fixed progressions. Z
`thm:main` supplies zero-freeness in Re s>7/8, **allowing the principal
pole**. R008 §§4–8 and its r2 review supply the already validated
single-endpoint lifting and signed probability bookkeeping. The changes
needed for the new endpoint are proved here.

The full i07 report, its contract and locator records, the complete 13,223-entry
untruncated tree, and the relevant retained theorem/proof interfaces were
consulted. All 38 i07 retained corpus blobs were checked; 11 relevant files
were freshly fetched from pinned raw URLs. The companion checks do not
reclassify D's centered theorem as a complex-mode theorem: E's sign remains
band-supported, and O's Elliott theorem remains a qualitative ordinary
integer theorem. Neither is used to bypass (2).

## 2. The two classical inputs, with the needed uniformity

The primary external inputs are de la Bretèche–Tenenbaum,
[*Remarks on the Selberg–Delange method*, v8](https://arxiv.org/pdf/2010.12929v8),
Theorem 1.2 and formula (1.10), and Granville–Shao,
[*When does the Bombieri–Vinogradov theorem hold for a given multiplicative
function?*, v1](https://arxiv.org/pdf/1706.05710v1), Theorem 1.1(b).
Their complete statements, not abstracts, were read; versioned PDF/text
bytes are retained. We use the former for the fixed function f_z, and the
latter for its **centered** progression discrepancy. We do not apply either
as a black box to an x-dependent multiplicative function.

Here are the consequences and their derivations. The Euler series is
ζ(s)^z G_z(s), with

\[
 G_z(s)=\prod_p(1-p^{-s})^z/(1-zp^{-s}).
\]

The product is analytic near 1, and all branches come from Re s>1.
The fixed-function Selberg–Delange expansion has arbitrary fixed precision:
for every A, sufficiently many terms leave O(R(log R)^−A). Its cumulative
coefficients are the Taylor coefficients of
`((s−1)ζ(s))^z G_z(s)/s`, divided by Γ(z−j). Differentiating the cumulative
expansion by partial summation gives the density coefficients without `/s`.
There is no differentiation of an unspecified error term.

For every θ<1/2 and A>0,

\[
 \sum_{q\le R^\theta}\max_{(a,q)=1}
 \left|\sum_{n\le R,\ n\equiv a(q)}f_z(n)
   -\frac1{\varphi(q)}\sum_{n\le R,(n,q)=1}f_z(n)\right|
 \ll_{z,A,\theta}R(\log R)^{-A}.                              \tag{BV}
\]

To justify the Siegel–Walfisz hypothesis here under Z, for a nonprincipal
character χ the series of f_zχ is L(s,χ)^z times an Euler product absolutely
convergent in every half-plane Re s>1/2. In any fixed closed half-plane
Re s≥σ₀>7/8, the logarithm of the nonprincipal L-function has bound
O_{σ₀}(log(q(2+|t|))). Indeed apply Borel–Carathéodory to discs centered at
2+it, with outer radius less than 2−7/8 and inner radius greater than
2−σ₀. The polynomial upper bound for L follows from periodicity/partial
summation; its logarithm at 2+it is bounded by its absolutely convergent
Euler series. The discs contain no zeros or poles. This also handles
imprimitive nonprincipal characters, whose extra Euler factors are nonzero
there. Thus L(s,χ)^z has a polynomial bound, uniform in q and t.

Mellin inversion for a smooth dyadic cutoff can now be shifted, for example,
to σ₀=15/16. Its derivative costs are polynomial in any log-sized inserted
time. Choosing the transform decay order above the fixed polynomial growth
gives O(R^{15/16}q^{C_z}L^C) for q≤L^D. Smooth majorants of transition width
R(log R)^−K remove the cutoff at a cost O(R(log R)^−K+1), since |f_z|≤1.
This proves sharp Siegel–Walfisz at every logarithmic modulus and every
desired precision. Larger q in the criterion are handled by the elementary
R/q+1 and R/φ(q) bounds. Character orthogonality subtracts exactly the
principal mean. Finally |Λ_{f_z}(p^j)|=log p, so f_z is in Granville–Shao's
class C. Its convolution inverse is μ(n)f_z(n), also in C, and f_z on
the primes is z1_P. Classical prime BV and their
Theorem 1.1(b) prove (BV). Its smooth dyadic version follows by putting the
modulus sum inside the partial-summation integral; no sum of endpoint
suprema is assumed.

All uses below have residual scales ≥x^{ε−o(1)}. Fixed log-power losses
can therefore be paid by choosing A last in (BV). The nonprincipal
argument does **not** apply to the principal branch point; it is retained
in the model that follows.

## 3. Explicit density and position model

Set L=log x, ρ=23/50=.46, y=exp(L^ρ), and

\[
 n_y=\prod_{p\le y}p^{v_p(n)},\qquad
 V_y=\prod_{p\le y}(1-1/p),\qquad P_{z,y}(s)=\prod_{p\le y}(1-zp^{-s}),
\]
\[
 A_z(s)=((s-1)\zeta(s))^zG_z(s),\quad
 b_{z,y,N}(v)=\sum_{j=0}^{N-1}
 \frac{(A_zP_{z,y})^{(j)}(1)}{j!\Gamma(z-j)}
                 (\log v)^{z-1-j}\quad(v>1).                    \tag{3}
\]

N is a sufficiently large **fixed** integer, chosen after all precision
and low-time costs. This is a density expansion, rather than a cumulative
expansion. In particular its leading coefficient is
G_z(1)P_{z,y}(1)/Γ(z), not the coefficient with the small primes omitted
and then silently restored.

Choose a fixed smooth real χ with 0≤χ≤1, χ(t)=0 for t≤ε/4, and χ(t)=1
for t≥ε/2. Write β(v)=χ(log v/L)b_{z,y,N}(v), defining it as zero when
v≤1. Define on **all positive integers**

\[
 \boxed{\quad
 \mathcal B_x(n)=\frac{f_z(n_y)}{V_y}\,z^d
          \sum_{\boldsymbol\ell}\frac1\ell\,
                   \beta\left(\frac{n}{n_y\ell}\right).
 \quad}                                                         \tag{4}
\]

This model depends on x, the original slots, z, N and χ. It does not
depend on an active subset, its padding parameter, a comparison pattern,
mark tests, a Mellin time, or an ideal kernel. All primes in every possible
inert and active group lie below y, whereas all long-slot primes exceed y.

**Lemma 1 (size, covariance, and coefficient bounds).** Put δ_z=1−Re z>0.
For every fixed N and fixed positive-power position range n≤x^C,

\[
 |\mathcal B_x(n)|\ll_{N,z,\epsilon,d,C} L^{-(1-\rho)\delta_z},
 \qquad
 \mathcal B_x(an)=f_z(a)\mathcal B_x(n)\quad(P^+(a)\le y).         \tag{5}
\]

The implied constants can depend on N; the logarithmic exponents and
rescaled smooth derivative exponents used below can be chosen independently
of N, for each fixed number of derivatives and sufficiently large x.

**Proof.** Exact prime-power factorization gives (an)_y=a n_y and
(an)/(an)_y=n/n_y, proving covariance even when a and n overlap. For each
fixed j≥1,

\[
 |(\log P_{z,y})^{(j)}(1)|\ll_{j,z}(\log y)^j,
 \qquad |(A_zP_{z,y})^{(j)}(1)|\ll_{j,z}|P_{z,y}(1)|(\log y)^j.
                                                                  \tag{6}
\]

Expand the local logarithms; Σ_{p≤y}(log p)^j/p≪_j(log y)^j and
the higher prime powers converge with the same bound. The second inequality
follows by the finite derivative product formula and analyticity of A_z
near 1. For log v between εL/4 and CL, each successive term of (3) costs
a factor O_{j,z,ε}(L^{ρ−1}). Hence β and each fixed derivative in log v
are bounded by C_N|P_{z,y}(1)|L^{Re z−1}, with additional harmless
nonpositive powers of L for derivatives. Finally

\[
 \frac{|P_{z,y}(1)|}{V_y}
 =\exp\left(\delta_z\sum_{p\le y}\frac1p+O_z(1)\right)
 \asymp_z(\log y)^{\delta_z}=L^{\rho\delta_z}.
\]

Sum 1/ℓ using C_x=O(1). This proves (5). The geometric decrease
L^{ρ−1} absorbs the finite list of derivative constants once x is large
depending on N. It does not introduce an exponent proportional to N. □

Notice that using the coefficient ℓ¹ norm of P_{z,y} instead of (6)
would lose this bound. The cancellation of its coefficients has already
been performed in the derivatives in (3).

## 4. Truncations with both square and progression control

We record the error mechanisms explicitly, since a global L² error alone
cannot be summed over x^{c₀} presieve moduli. Let

\[
 D_0=\exp(L^{1/2}),\qquad h_0=\lfloor L^{.01}\rfloor.
\]

The reciprocal mass of y-smooth a is 1/V_y=L^{ρ+o(1)}. With η=1/log y,

\[
 \sum_{P^+(a)\le y}\frac{a^\eta}{a}
 =\prod_{p\le y}(1-p^{-1+\eta})^{-1}\ll L^C,
 \quad
 \sum_{\substack{P^+(a)\le y\\a>D_0/y}}\frac1a
 \ll L^C\exp(-\tfrac12L^{.04}).                                \tag{7}
\]

The product estimate follows by comparing its logarithm with Σ1/p;
Σ(p^η−1)/p=O(1), and the prime-power terms are bounded for large x.
If n_y>D₀, multiplication of its prime factors one at a time produces a
divisor a in (D₀/y,D₀]. Consequently this exceptional set has a positive
divisor majorant supported below D₀, with the reciprocal mass in (7).
On integer dyads this proves arbitrary log-saving counting estimates.
It also proves arbitrary log-saving square estimates after fixed local
divisor moments by Cauchy. Such moments are logarithmic: the local series
Σ_{e≥0}(e+1)^j B^{1_{e>0}}/p^e has first-order term O_{j,B}(1/p).

On a fixed physical list of product P, all primes of P are ≤y and
n_y=P(n/P)_y. The same Rankin bound gains at most
P^η≤L^{O_J(1)}, since log P=O_J(L^ρ log L). Thus these errors also save
arbitrary log powers in physical list norms, after J is fixed.

For the condition P^−(v)>y use the literal finite expansion

\[
 1_{(v,\prod_{p\le y}p)=1}
   =\sum_{\substack{d\mid v,\ P^+(d)\le y\\\mu^2(d)=1,\ \omega(d)\le h_0}}
           \mu(d)+E(v),
 \qquad |E(v)|\le {\omega_{\le y}(v)\choose h_0+1}.               \tag{8}
\]

The inequality is the Bonferroni remainder, including its zero cases.
The right-hand side is a nonnegative divisor sum of degree h₀+1.
All its divisors are ≤exp(O(L^.47)); its reciprocal mass is at most
(C log L)^{h₀+1}/(h₀+1)!, which saves every log power. The retained
absolute reciprocal mass is ≤∏_{p≤y}(1+1/p)=L^{O(1)}.

Here is the progression version of these estimates. In a tuple term
u=ℓv, impose r|u+1 and u+1≡b (M), with r≤x^{c₀} and c₀<ε/8. A divisor
constraint a|v gives either no solution or O_M(x/(ℓra)+1) integers on
the fixed compact support. All divisors used in (7), (8), and their
products have size exp(O(L^{1/2}))=x^{o(1)} and ordinary coefficient mass
x^{o(1)}. The number of long tuples is O_d(x^{1−ε}). Therefore the total
rounding error is

\[
 x^{1-\epsilon+c_0+o(1)}=O_A(xL^{-A})\quad\hbox{for every fixed A}.\tag{9}
\]

The main errors sum to x times a fixed power of L times the reciprocal
tails just displayed. Without a tuple divisibility constraint the rounding
bound is the stronger x^{c₀+o(1)}; the harmonic tuple sum in (4) costs O(1).
Fixed-array weights are bounded and may be absorbed. For small powers of
fixed primes in M, CRT changes constants only.

For L² use of (8), powers of binomial coefficients are bounded by
L^{O(1)}B^{ω_{≤y}(v)}1_{ω_{≤y}(v)≥h₀}. A larger fixed B and the local
moment bound give exponential decay in h₀. If one sums (8) over all
a|n with P^+(a)≤y, the extra count is at most τ(n_y). Its fixed moments
are still logarithmic. This is the aggregate square-error argument;
one must not apply Minkowski and sum 1/√a up to D₀.

These observations justify all the truncations below by positive
progression envelopes or by squared coefficient errors, as appropriate.

## 5. Principal matching at low times

**Lemma 2 (rough density).** Fix a positive residual exponent ε₁ and
logarithmic modulus, time and derivative bounds. For R in
[x^{ε₁},x^C], k≤L^C, (a,k)=1, smooth fixed-dyad ψ, and |t|≤L^B,

\[
 \frac1R\sum_{\substack{v\equiv a(k)\\P^-(v)>y}}
       f_z(v)\psi(v/R)(v/R)^{it}
 =\frac1{\varphi(k)}\int\psi(u)u^{it}b_{z,y,N}(Ru)\,du+O_A(L^{-A}).
                                                                  \tag{10}
\]

For each desired A there is N₀ such that every fixed N≥N₀ works; the assertion is
uniform in all displayed data. For unweighted rough integers the corresponding
formula has density V_y/φ(k), with arbitrary log precision, and also holds
for smooth amplitudes with the derivative bounds of Lemma 1.

**Proof.** Every prime of k is ≤y. For nonprincipal characters, expand
roughness by (8); complete multiplicativity leaves the ordinary nonprincipal
f_z-character sums at scales R/d≥x^{ε₁−o(1)}. Section 2 and the
L^{O(1)} reciprocal coefficient mass give arbitrary log saving. The positive
envelope in §4 handles the expansion error, even after the polynomial-in-k
cost of character orthogonality.

For the principal sum, (8) gives convolutions with μ(d)f_z(d). Apply
the fixed-function density expansion to each residual scale R/d. Its
arbitrary precision pays the reciprocal coefficient mass and 1+|t|.
Taylor-expand the powers of log(Ru/d) around log(Ru). Here
log d=O(L^.47), so a Taylor remainder of order J is bounded in absolute
value by a fixed L^C times L^{−.53J}. The retained moments are

\[
 \sum_{P^+(d)\le y}\frac{\mu(d)f_z(d)}d(-\log d)^j
                         =P_{z,y}^{(j)}(1).                       \tag{11}
\]

Restoring the omitted degrees in each fixed moment costs arbitrary log
saving: insert the moment factor into the factorial tail in (8), or
differentiate its finite Euler product a fixed number of times. The
coefficient identity

\[
 \frac1{\Gamma(z-j)}{z-1-j\choose r}
                   =\frac1{r!\Gamma(z-j-r)}
\]

and the derivative product rule give exactly (3), after collecting total
degree j+r. Choose the number of base terms and Taylor terms sufficiently
large, and collect the first N terms; (6) bounds the remaining fixed tail.
This proves the unrestricted rough density expansion. Since roughness
already excludes the primes of k, the principal character gives this same
sum divided by φ(k). This proves (10). For the unweighted case use CRT
in (8): the density in a unit class is
k^−1∏_{p≤y,p∤k}(1−1/p)=V_y/φ(k). The rounding errors are x^{−ε₁+o(1)}
after normalization and the envelope saves every log power. □

**Lemma 3 (all local tests, including nonunit additive frequencies).**
Let H_x(n)=H_x(n_y), |H_x|≤L^C, with no regularity imposed on its values.
At Y=x^{1+o(1)}, uniformly in k≤L^C, h modulo k, |t|≤L^B, and the
allowed smooth ψ,

\[
 \frac1Y\sum_n\psi(n/Y)(n/Y)^{it}H_x(n)
       [f_z(n)T_x(n)-\mathcal B_x(n)]e(hn/k)=O_A(L^{-A}).           \tag{12}
\]

**Proof.** Remove n_y>D₀ by §4. In a tuple term write n=ℓav, with
P^+(a)≤y, a≤D₀, and P^−(v)>y. The n_y is exactly a; no coprimality
between a and a previously selected small label is imposed. The coefficient
is z^d f_z(a)H_x(a). Lemma 2 applies at R=Y/(ℓa)≥x^{ε−o(1)}.
After summing unit classes the explicit principal term is

\[
 \frac{z^d}{\ell a}f_z(a)H_x(a)
 \frac{c_k(ha\ell)}{\varphi(k)}
 \int\psi(u)u^{it}b_{z,y,N}(Yu/(\ell a))\,du.                    \tag{13}
\]

For the model, write n=av with v rough, and use unweighted rough counting.
The 1/V_y in (4) cancels the rough density V_y. Its ℓ summand is
precisely (13), because ℓ is a unit modulo k and
c_k(haℓ)=c_k(ha), even when a is a nonunit. The cutoff χ is identically
one on these truncated positive-power residual scales. Errors cost at most
L^CΣ_a1/aΣ_ℓ1/ℓ=L^{O(1)}. Choose the precision after that cost and B.
This proves (12). There is no uncomputed main term in its error. □

## 6. Separate high-time estimate for the physical model

This is needed in addition to (12). Rapid decay of a *continuous* density
integral by itself would not establish the discrete high-time estimate.

Let H_marks=𝒲 W_t^b be D's actual first marked weight, with bounded big-mark
test b and t_g=1 on small groups. Both it and the version with one small
mark removed depend only on n_y and have a fixed log-power bound.
The low-frequency endpoint is the difference in (12), with this H_marks.
Its squared norm is YL^{O(1)}, since both T_x and 𝓑_x are bounded.

For high times perform the identical small-mark extraction as D
`cor:extract-small`. Its square exceptions have relative squared mass
L^{O(1)}exp(−L^.27); multiplication by either bounded first core leaves
that bound unchanged. In the genuine tuple part, f_z(p_s p_l u)=z²f_z(u).
The long prime polynomial changes by a constant of modulus one, and the
residual coefficients have unchanged squared norms. Thus D's actual
coefficient-independent sparse Gram proof and long-prime estimate give
arbitrary log saving for that part, as in R008 §5.3. This does not change
the original Type II α or β.

As in that proof, relaxing numerical distinctness in the long slots has
squared coefficient error O(YL^C x^−ε), and is removed on the full time
interval by ordinary mean square before the sparse-time argument.

For the model part use the **exact** identity
𝓑_x(p_s n)=z𝓑_x(n). It gives the same small-prime polynomial P_s(t),
up to the constant z. The remaining coefficient at scale
R₀≍Y/P_s=x^{1+o(1)} is H_rem(n)𝓑_x(n). Here is a finite divisor model
for that coefficient, distinct from simply invoking D's constant-term
bound. Write n_y=a≤D₀ and then expand P^−(n/a)>y using (8). It gives
terms indexed by a,e,ℓ of the form

\[
 \frac{z^d f_z(a)H_{\rm rem}(a)\mu(e)}{V_y\ell}
 1_{ae\mid n}\,\beta\left(\frac n{a\ell}\right),
 \quad P^+(a),P^+(e)\le y,\quad a\le D_0,\quad
 \mu^2(e)=1,\quad\omega(e)\le h_0.                            \tag{14}
\]

In (14) d is the original tuple dimension. The normalization after
n=ae v is a coefficient
1/(ae). Its absolute reciprocal sum, including the harmonic tuple sum and
the 1/V_y, is L^{C_*}; **not O(1)**. The same bound holds for the total
variation of the smooth amplitudes, by Lemma 1. Its exponent can be chosen
independent of fixed N. All progression scales R₀/(ae)=x^{1+o(1)},
and in particular are bounded below by x^{1−o(1)}.

The omitted coefficient has L² mass O_A(R₀L^−A) for every A: use the
smooth-part tail and the aggregate square-error argument in §4. Ordinary
Dirichlet mean square controls it on the entire retained time interval
|t|≤2T₀, T₀=xL^{C₆+1}, before restricting to exceptional times:

\[
 R_0^{-2}\int_{|t|\le2T_0}\left|\sum_n E_n n^{it}\right|^2dt
 \ll L^{-A}(T_0/R_0+\log R_0),\qquad
 T_0/R_0\asymp LP_s/H=o(1).                                   \tag{15}
\]

For each term of (14), separate the rational additive phase by residue
classes. The divisor ae need not be a unit modulo k; this is harmless:
e(h ae v/k) is split directly into classes of v modulo k. One does not
invert ae. The smooth amplitude β(e v/ℓ) has the bounded variation just
proved, uniformly in all its indices.

At L^B≤|t|≤T_mod=exp(L/(log L)^2), comparison of each progression sum
with its logarithmic-phase integral and partial summation gives, after
paying the reciprocal mass and residue costs,

\[
 |N_0(t)|\ll L^{C_*}(|t|^{-1}+x^{-c}),\qquad
 \int_{L^B\le|t|\le T_{\rm mod}}|N_0(t)|^2dt
       \ll L^{2C_*-B}+x^{-c'}.                                \tag{16}
\]

The smooth amplitude has no time oscillation other than the retained
log-sized twists, which are incorporated in t after increasing B. For
T_mod<|t|≤2T₀, apply the actual subinterval estimate D `lp:log-phase`
and partial summation at scale R₀/(ae), modulus k≤L^C. This yields

\[
 |N_0(t)|\ll L^{C_*}\exp(-L/(\log L)^{C_{19}}).                  \tag{17}
\]

All scale and time inequalities of that lemma hold: the scale is
x^{1+o(1)}, the lower time exceeds exp(L/(2(log L)^2)), and the upper
time is <4x³. On the ordinary set where P_s(t) is small, the collapsed
remaining coefficient has scale Y/P_s≫T₀, so ordinary mean square suffices.
On its exceptional unit intervals, their number is ≤exp(O(L^.9)) by
D's factorial prime-polynomial argument. Equations (16) and (17), with
the small-prime supremum, now give arbitrary log saving there. In (16)
one integrates 1/t²; in (17) one pays only the exceptional intervals,
not the entire length T₀.

Choose B after the fixed group, kernel, separation and derivative exponents.
These exponents are independent of N. Then choose N in Lemma 3 after B
and all required low-time precision. This prevents a B–N circular choice.
The source local Mellin lemma and bilinear multiplier argument therefore
bound every comparison with first core

\[
 \mathcal W(n)\,[f_z(n)T_x(n)-\mathcal B_x(n)]                  \tag{18}
\]

to arbitrary prescribed logarithmic precision.

## 7. Propagation through the complete physical residual

**Proposition PM (marked physical-model transfer).** Under D's actual
active-group hypotheses, with a full small interval for fixed-progression
mixing, G(n)=G(n_*), |G(n)|≤L^Cτ(n_*)^C, and all fixed data as above,
for every A there is N₀ such that every fixed N≥N₀ satisfies

\[
 \sum_{w\equiv r(M)}\frac{\Psi(w/x)}w\mathcal W(w)
 [f_z(w)T_x(w)-\mathcal B_x(w)]
       W_1(w)W_1(w+1)G(w+1)=O_A(L^{-A}).                        \tag{PM}
\]

The same N may be used for every active set and every coefficient core
in one fixed extraction, by choosing it after their uniform log exponents.

**Proof.** On physical positions use the first vector defined by (18),
conjugated according to D's pairing convention, with its extra half damping
and residue indicator. It is constant on each mark fiber at a fixed n.
The core is bounded for sufficiently large x by Lemma 1; D's reciprocal
list norm is ≤1. Its norm exponent is independent of J and N; thresholds
may depend on either. The second vector is the original G with its norm
bound. Thus the actual graph pairing contract applies to the **original**
ideal family. No phases are inserted into that family before using its
operator estimate.

Restore all dyads and the Mellin insertion, including its original
Schur-controlled tail. In pattern ν write n=D_Rw and n′=D_R(w+D_C).
There are Js−c_ν shared labels, c_ν=Σ_g|C_g|. Both summands in (18)
obey the same exact covariance, giving

\[
 [f_zT_x-\mathcal B_x](D_Rw)
       =z^{Js}z^{-c_\nu}[f_zT_x-\mathcal B_x](w).                \tag{19}
\]

The smooth-part quotient in (4) is precisely what makes (19) exact;
there is no Taylor error in log D_R. The cutoff, tuple coefficients and
every lower density term satisfy the identity. Repeated auxiliary labels
are counted with multiplicity. Collision errors remain the source absolute
errors, because the core is bounded.

After complete reassembly the shared-label measure is harmonic, and a
full small interval gives R006's fixed-modulus unit mixing. The identity

\[
 \varphi(M)^{-1}\sum_{t\in(\mathbb Z/M)^\times}
  1_{tw=r}1_{t(w+D_C)=r+1}
     =\varphi(M)^{-1}1_{w=rD_C\ (M)}
\]

uses that D_C is a unit; it holds for nonunit r as well. Accordingly the
full residual is (R+Σ_{ν≠0}z^{−c_ν}C_ν)/φ(M)=O_A(L^−A), for the
**difference** (18). Every comparison difference is small by §§5–6.
Fixed residue restrictions shift rational frequencies to denominators at
most Mk and are covered by the same estimates. Choose their precision
after all family, pattern, arc and dyad costs, and subtract them to isolate
R. This proves PM. □

PM is an explicit proof of the model's legitimacy in the physical vectors
and in the entire residual. It is stronger than a scalar endpoint
expansion. It does not say that an individual uncentered comparison is
negligible.

## 8. The summed presieve remainder, with its principal model

**Proposition PR.** Fix 0<c₀<ε/8. For H from D's fixed finite inert-array
collection (including the constant, products, repeated arrays and bounded
linear combinations), for every A all sufficiently large fixed N satisfy

\[
 \sum_{\substack{r\le x^{c_0}\\(r,M)=1}}
 \left|\sum_{\substack{r\mid u+1\\u+1\equiv b(M)}}
 \Phi(u/x)H(u)[f_z(u)T_x(u)-\mathcal B_x(u)]\right|
 \ll_A xL^{-A}.                                                \tag{PR}
\]

The congruence sums are unweighted integer sums, not prime sums.

**Proof.** H(u)=H(u_y) and is bounded by a constant for fixed arrays.
Discard u_y>D₀ using the positive divisor envelope (7), with the summed
CRT rounding calculation (9). In the genuine tuple term put u=ℓav,
a=u_y≤D₀, P^−(v)>y. All primes of ℓ exceed x^{c₀}, so (ℓ,rM)=1
eventually. Terms with (a,r)>1 are impossible. Put g=gcd(b−1,M).
Compatibility with the fixed class is exactly gcd(a,M)=g; otherwise
there is no solution because v is a unit at every prime of M. In the
compatible case v belongs to a reduced class modulo

\[
 q=rM/g.                                                       \tag{20}
\]

Indeed a/g is a unit modulo M/g and all coefficients are units modulo r.
For the model term u=av the same q occurs, with a possibly different
reduced residue, but the same g and a. This is also valid when b−1=0
modulo a prime power in M: the entire corresponding valuation is in a,
and the rough v is still a unit there.

First obtain (BV) for f_z(v)1_{P^−(v)>y} at the required scales by
inserting (8) in both the progression sum and its centered natural mean.
Only e coprime to q contributes to a reduced class. Its residual scale
R/e is ≥x^{ε−o(1)} and the moduli (20), distinct as r varies, are
≤Mx^{c₀}<(R/e)^{1/3}. Apply (BV) at exponent 1/3 with smooth partial
summation. Sum the errors with the L^{O(1)} reciprocal coefficient mass.
The positive Bonferroni envelope controls its own progression errors by
CRT, not by multiplying a global L² bound by x^{c₀}. Its natural-mean
errors cost at most Σ_{q≤Mx^{c₀}}1/φ(q)≪L^{O(1)}. This proves that
the retained f_z-rough progression sums equal their natural principal
means divided by φ(q), with total error O_A(RL^−A).

In those natural means remove the additional restrictions at primes p|q
with p>y. Their absolute cost is at most

\[
 O\left(R\sum_{\substack{p\mid q\\p>y}}\frac1p\right).
\]

After division by φ(q) and summation over q this is arbitrarily
log-saving, since

\[
 \sum_{q\le Mx^{c_0}}\frac1{\varphi(q)}
       \sum_{\substack{p\mid q\\p>y}}\frac1p
 \ll L^{O(1)}\sum_{p>y}\frac1{p(p-1)}
 \ll L^{O(1)}/y.                                               \tag{21}
\]

One may sum over all integers q to bound the subset (20). For p|q,
write q=pt and use φ(pt)≥(p−1)φ(t); the standard reciprocal-totient
sum is O(log Q), which also follows by expanding n/φ(n) into squarefree
divisors. This proves (21) without an estimate for prime shifts.

The remaining natural mean is the unrestricted f_z-rough mean. Its
smooth expansion is Lemma 2 at k=1. Its exact contribution for fixed
a,ℓ is therefore

\[
 \frac{xz^d f_z(a)H(a)}{a\ell\varphi(q)}
      \int\Phi(u)b_{z,y,N}(xu/(a\ell))\,du.                    \tag{22}
\]

Now evaluate the position model in the progression, using u=av,
roughness expansion (8), and CRT at modulus q. Its unweighted rough
density in a reduced class is

\[
 \frac{V_y}{q\prod_{p\mid q,\ p\le y}(1-1/p)}
 =\frac{V_y}{\varphi(q)}
             \prod_{p\mid q,\ p>y}(1-1/p).                    \tag{23}
\]

The factor 1/V_y in (4) cancels V_y. Replacing the last product in
(23) by 1 costs (21), with the bounded smooth amplitudes and polynomial
reciprocal a mass. What remains is exactly (22), for each ℓ and a,
including every retained density coefficient. Thus the main terms cancel
before summing errors.

The total a and tuple reciprocal masses are L^{O(1)} and O(1). All
support products in CRT are exp(O(L^{1/2})), so the rounding bound (9)
survives their ordinary coefficient masses. Choose N and the BV accuracy
after these fixed costs. This proves PR. □

In particular (21) explains why matching only logarithmic moduli in PM
is insufficient for presieving, and why it nevertheless suffices to put
all primes ≤y into the position model: the omitted larger prime divisors
of a presieve modulus have a summably tiny principal effect.

## 9. Presieving and recombining the composite models

Let h be a large fixed even integer, γ=c₀/(4h+3), and sieve u+1 up to
x^γ, only at primes not dividing M. For a fixed inert array put

\[
 D_x(u)=f_z(u)T_x(u)-\mathcal B_x(u),\qquad
 A_0(u)=\Phi(u/x)\mathcal W(u)(T_x(u)+1)1_{u+1\equiv b(M)}.
\]

For sufficiently large x, |𝓑_x|≤1 and |D_x|≤T_x+1. Thus the four
weights A₀±Φ𝒲 Re D_x and A₀±Φ𝒲 Im D_x, with the same class
indicator, are nonnegative. PR gives identical unsigned progression main
terms for each plus/minus pair. D/R006's original progression theorem
for T_x+1 supplies their common density 1/r and mass proportional to
x m_𝒲(C_x+1)/M. The block sieve applies because
x^{γ(4h+2)}<x^{c₀}. Subtracting pairs yields

\[
 \limsup_{x\to\infty}\frac{L}{xm_{\mathcal W}}
 \left|\sum_{\substack{u+1\equiv b(M)\\P^-(u+1)>x^\gamma}}
           \Phi(u/x)\mathcal W(u)D_x(u)\right|
 \ll_{M,d,\epsilon,\Phi} e^{-h}/\gamma.                        \tag{24}
\]

The surviving constant is independent of K, the fixed array, and h;
the array-dependent remainder constants disappear in the x limit. The
original unsigned upper sieve for Φ𝒲, together with (5), bounds the
presieved model sum by o(xm_𝒲/L), for each fixed h and array. Consequently
(24) also holds with D_x replaced by f_zT_x. No complex positivity is
being assumed.

For a presieved composite u+1 with j factors, 2≤j≤2/γ, follow the
original unsigned proxy replacement. The i07 covariance calculation
f_z(ah)=z^K f_z(h) leaves f_z(h) outside the original determinant
Cauchy square. α and β remain the original scalar coefficients, including
the fixed-character twists for M. This gives Type II replacement with
the required K, independently of the inert exponents. All prime-square,
coefficient truncation, threshold/logarithm stripping, and Fourier-tail
errors are the original absolute errors, since |f_zT_x| is bounded.

Next discard failed coin outcomes under the positive proxy tuple mass,
before any signed expansion. Expand only the retained outcomes. Allocation
of active primes among the j factors fixes u, so D's allocation identity
is unchanged; f_z(u)T_x(u) stays outside it. For each active set P, PM
gives the actual fully marked sum in i07 CM as

\[
 \mathfrak M_{z,P}(x)=
 \sum_{u+1\equiv b(M)}\Phi(u/x)\mathcal W(u)\mathcal B_x(u)
              W_1(u)W_1(u+1)G_P(u+1),                           \tag{25}
\]

plus O_A(xL^−A). This is an explicit position-model sum, with 𝓑_x
given by (3)–(4). It is not an unevaluated potential main term hidden
inside O(). The same 𝓑_x works for every P. Choose A, and then N,
after the uniform log cost of the active-set expansion, all j in their
fixed finite range, and the physical comparisons.

**The aggregate cancellation step.** Do not bound the terms (25) separately.
Undo the allocation identity for their actual signed coefficients, then
undo the expansion of the failure factors. Since 𝓑_x(u) is independent
of P and allocations, it factors through both finite identities. The
sum of all model terms is exactly the original positive stripped proxy
tuple sum with multiplier 𝓑_x(v−1), times the probability of retained
coin outcomes, up to the already exponentially small candidate-square
exceptions. That probability lies in [0,1]. Therefore its absolute value
is at most

\[
 \sup_{u\asymp x}|\mathcal B_x(u)|\,
 O_{j,K,\Phi,M}(x/L)
 \ll_{N,j,K,\Phi,M}xL^{-1-(1-\rho)\delta_z}=o(x/L).             \tag{26}
\]

The positive proxy mass O(x/L) is D's rough-box count, before the active
expansion. No factor 3^{|𝒞|}, j^{s_P}, or individual kernel coefficient
norm multiplies the small power in (26). Such costs are paid only by the
arbitrary-precision **error** in PM. All qualitative discarded failure
errors were removed before this expansion and remain unamplified.

This proves composite subtraction. The presieved model was already small,
so (24) holds for primes with f_zT_x. D/R006's unsigned array square
then removes the marks by Cauchy, because |f_zT_x|=T_x is bounded:

\[
 \limsup_{x\to\infty}\frac Lx
 \left|\sum_{p\equiv b(M)}\Phi((p-1)/x)f_z(p-1)T_x(p-1)\right|
 \le C_{M,d,\epsilon,\Phi}\frac{e^{-h}}\gamma
                 +C_{d,\epsilon,\Phi}\sqrt{C_K/B}.             \tag{27}
\]

Fix interior data; choose h, γ and the finite j range; choose sufficient
K; fix any finite B disjoint inert arrays. Choose the finite physical
families, high-time thresholds, and finally N and remainder precisions.
Take x→∞ **first**, then B→∞, and finally h→∞, choosing a new sufficient
fixed K for each h. Model constants depending on N,K,B have vanished in
the first limit. Since γ^−1=(4h+3)/c₀, (27) proves (2).

## 10. Completion of the joint law and exact scope

For completeness, the probability passage is not an assertion that Ω
modulo m is continuous in the factor partition. For each nonreal mode
z, attach f_z(p−1) to the unsigned factorial measures. Their total
variations are dominated by the R006 unsigned measures. Equation (2)
gives zero on every compact interior tuple test, with changes of dyadic
cutoff and log normalization controlled by the unsigned endpoint strips.
Multiply by the usual size-biased factors. The unsigned size-biased laws
converge to the GEM(1) law of total mass one, so compact exhaustion proves
zero weak complex-measure limit on the entire cube. Already the one-draw
total mass gives E f_z(p−1)→0. Sorting d draws approximates the ranked
coordinates within the unseen mass; its limiting expectation is 2^−d.
Uniform continuity then gives cancellation with every H in (1). This is
the dominated-measure argument fully written in R008 §8, now applied to
the new estimate (2), not used as a substitute for it.

For m fixed, perform this proof for its finitely many nonreal nontrivial
roots. The mode −1, when present, is R008; the mode 1 is R006. Finite
Fourier inversion of 1_{Ω≡a(m)} proves (1), first in dyads and then
cumulatively by a finite dyadic decomposition and fixed-modulus PNT. □

The new work relative to i07 is Lemmas 1–3, the discrete high-time
argument (14)–(17), PM, PR, and the aggregation (25)–(26). It addresses
the full CM contract: legitimate physical vectors, all comparison
patterns with the inverse phase, all principal progression terms,
and prime-normalized size after recombination. The ordinary mean of f_z
remains nonzero throughout. The theorem is a deduction under the stipulated
corpus, not an unconditional theorem independent of that premise.

## 11. Failed shortcuts, literature limits, and validation

The scalar subtraction `f_z T_x − constant` was rejected: its slot
dependence and rational-frequency principal terms do not agree. Using
`(log n)^{z−1}` directly was rejected: shared labels move its logarithm
and generate pattern-dependent corrections. Using only the active set
in n_y was rejected for aggregation: that produces different models
for different P. The uniform choice of every prime ≤exp(L^.46) and the
argument n/(n_yℓ) repair those failures simultaneously.

Absolute divisor coefficient bounds alone do not prove (5): cancellation
must be performed in (11)/(6) first. A continuous Fourier decay argument
alone does not prove (17): the actual integer progression lemma and its
subinterval form are used. An L² error multiplied by x^{c₀} would not
prove PR: (7)–(9) supply positive short-divisor envelopes. Individual
main-term bounds after the signed expansion would lose arbitrary fixed
log powers: (26) is an exact reassembly before absolute values.

Primary browsing reopened the full Selberg–Delange and Granville–Shao
statements above and searched the precise complex shifted-prime target.
The nearby Hildebrand paper's
[publisher abstract](https://londmathsoc.onlinelibrary.wiley.com/doi/abs/10.1112/plms/s3-59.2.209)
advertises a partial Halász analogue, not the joint theorem proved here;
its inaccessible full statement is not an input or a claimed exclusion.
The prior i07 companion screen and R008 review remain the applicable
bounded novelty checks. This work does not infer priority from unsuccessful
searches, repeat the quartic/PD alternatives, or count the standard
probability consequence as a separate result.

Reproduce the exact finite algebra and provenance checks from the project:

```sh
python3 frontier/experiments/i10_complex_modes/check.py
python3 frontier/experiments/i10_complex_modes/record.py
```

The finite checks concern density coefficient recurrence, exact small-part
covariance including repeated primes, additive principal unit invariance,
CRT local densities, and signed coin reassembly. They do not count primes
or numerically validate an asymptotic. The provenance script checks the
complete-tree blob pin, freshly retained raw files, unchanged input hashes,
and report/artifact hashes. Writes are confined to this report and
`frontier/{sources,experiments}/i10_complex_modes/`; no agents, staging,
commits, shared-index changes or other-project writes were used.

**Review priorities.** The parent should independently check the uniform
rough-density derivation in §5, the aggregate (rather than Minkowski)
square-error bound in §4, the nonunit fixed-class reduction and large-prime
principal correction in §8, and the exact common-model reassembly in §9.
The author finds no remaining unproved estimate within the stated corpus
premise. Acceptance, novelty assessment and any eventual finding number
remain parent actions.
