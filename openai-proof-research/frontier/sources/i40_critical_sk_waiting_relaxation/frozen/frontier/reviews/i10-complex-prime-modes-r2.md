# Independent proof audit r2: complex prime-predecessor modes

Date: 2026-10-08. **Verdict: PASS under the stipulated corpus and accepted R006/R008 premises.** The completed 856-line candidate establishes its nonreal-mode interior estimate, and hence Theorem CP, without an additional unproved distribution hypothesis. I found no unresolved universal estimate in the proposed construction. The main advance over i07 is a single physical principal model with exact covariance, a separate discrete high-time estimate, a summed presieve remainder, and recombination of the model contributions before absolute values.

This is an independent proof-review recommendation, not acceptance or assignment of an R number. The current accepted findings R006, R008, and R009 remain unchanged. It is not a worldwide novelty audit. The nonreal extension is not a direct substitution in R008 or the qualitative Elliott theorem; no direct routine reduction was identified in the inspected interfaces. The original candidate is preserved.

Reviewed candidate SHA-256: `cd87b7cf1636395410aeb90dc431eae695d43f7e824b7fd0a49ddd04ca4a3409`.

## 1. Scope, inputs, and what this verdict means

For every fixed reduced class b modulo M, fixed m≥3, residue a modulo m, finite ranked-coordinate count k, and continuous complex H on [0,1]^k, CP asserts

\[
 \frac{1}{\pi(X;M,b)}\sum_{\substack{3\le p\le X\\p\equiv b\ (M)}}
 1_{\Omega(p-1)\equiv a\ (m)}H(V_1(p),\ldots,V_k(p))
 \longrightarrow \frac1m\mathbb EH(\mathrm{PD}(1)).
\]

The same holds on terminal dyads with their class-prime normalization. Everything is fixed before X→∞. There is no rate or growing-m assertion. The cases m=1 and m=2 are respectively R006 and R008. The audit assumes all applicable results at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` true; it checks their use and all new deductions, not their upstream truth.

I read AGENTS.md, the pin, the relevant catalogue entries, the complete 13,223-record untruncated preprint inventory, the entire candidate, the full i07 arithmetic report, the accepted R008 record and its complete proof/audit, and the pertinent R006 record. The inventory contains 749 manuscript directories; its actual paths, rather than the catalogue's older headline count or the truncated root-tree cache, were screened. No claim to have read every manuscript follows from this path screen.

I read the actual source contracts and the proofs used to extend them: D's complete §§6–7, its Type II Cauchy reduction, long-coefficient proof, probability passage, and logarithmic-phase/long-prime interfaces; P's full coefficient-transfer proof; S's endpoint-pairing proof and ideal-family contracts; Z's actual zero-free statement; and the E/O restrictions relevant to the rejected shortcuts. Fourteen files were freshly retrieved from immutable raw URLs and checked against the complete tree's Git blobs. The 38 i07 retained files and 11 candidate retained files were also rechecked. Both versioned primary PDFs were downloaded again and match the supplied bytes. Source ranges and exact hashes are retained, separately from assertions of mathematical correctness.

Abbreviations: D is *The Poisson–Dirichlet Law for Prime Predecessors*; S is *Weighted Dilation Graphs, Smooth Shifted Primes and Totient Fibers*; P is *Primitive Roots for Every Admissible Integer Base*; Z is the September 30 *Quasi-Riemann Hypothesis*; E is the September 17 even-predecessor paper; O is the ordinary two-point multiplicative-correlation paper. Exact paths and ranges are in [source-ranges.json](../sources/i10_complex_modes_r2/source-ranges.json) and [retrieval-manifest.json](../sources/i10_complex_modes_r2/retrieval-manifest.json).

## 2. Classical inputs and the moving rough density — candidate 100–154, 318–371

**Pass.** In [de la Bretèche–Tenenbaum v8, Theorem 1.2 and (1.10)](https://arxiv.org/pdf/2010.12929v8), take ρ=z, r=1, and σ>1/2. The prime discrepancy f_z(p)−ρ is identically zero, and the prime-power absolute convergence condition holds. Thus the accuracy parameter can be arbitrarily large. This input is applied to the fixed function f_z, not asserted uniformly for an arbitrary x-dependent Euler product.

Here is an independent check of the density conversion. Write t=s−1 and

\[
 A_z(1+t)=\sum_{j\ge0}a_jt^j,\qquad
 \frac{A_z(1+t)}{1+t}=\sum_{j\ge0}c_jt^j.
\]

The cumulative coefficient is c_j/Γ(z−j). Its literal differentiated finite expansion has coefficient

\[
 \frac{c_j}{\Gamma(z-j)}+
 \frac{(z-j)c_{j-1}}{\Gamma(z-j+1)}
 =\frac{a_j}{\Gamma(z-j)}
\]

at degree j, with c_{−1}=0. Use Stieltjes partial summation on the remainder, with variation O(L^C(1+|t|)); do not differentiate the remainder. The extra final differentiated term can be absorbed by starting with enough base terms. This verifies the absence of `/s` in candidate (3).

For nonprincipal χ, the factorization is L(s,χ)^z times an absolutely convergent Euler product in Re s>1/2. Z `thm:main` excludes zeros in Re s>7/8 and explicitly allows the principal pole. On a closed smaller half-plane, Borel–Carathéodory on discs centered at 2+it bounds the analytic logarithm by O(log(q(2+|t|))). Its value at the center is fixed by the Euler series. Nonprincipal imprimitive characters introduce no pole and their extra factors have no zeros there. Consequently the twisted series has polynomial growth. Smooth Mellin inversion may be shifted to 15/16; arbitrary fixed smoothing accuracy and character orthogonality give the centered Siegel–Walfisz criterion at q≤L^D. For larger q, the elementary R/q+1 and R/φ(q) bounds suffice after choosing D large. Nothing in this argument removes the principal branch.

[Granville–Shao v1, Theorem 1.1(b)](https://arxiv.org/pdf/1706.05710v1) requires f and its convolution inverse in class C, prime-restricted BV, and SW for f. It does **not** require an independently assumed SW theorem for the inverse in part (b). Here Λ_f(p^j)=z^j log p, the inverse is μf_z, and its logarithmic derivative has the negative coefficients, so both are in C. The prime restriction is z1_P. These facts and the preceding SW argument give candidate (BV) for every fixed θ<1/2. If inverse SW is desired, the same nonprincipal argument works with L(s,χ)^(−z); it is not a missing hypothesis. Smooth BV is obtained with the modulus sum inside the partial-summation integral and a strict exponent margin at all comparable endpoints.

For the moving rough cutoff, truncate inclusion–exclusion at h₀=floor(L^.01). Retained squarefree d satisfy log d≤O(L^.47), and their absolute reciprocal mass is O(L^ρ). At R≥x^{ε₁}, all R/d remain positive-power scales. Taylor expansion of log(Ru/d) around log(Ru) has expansion parameter O(L^−.53). Each fixed additional Taylor degree therefore gains .53 in the log exponent before a fixed reciprocal-mass loss. The exact identity

\[
 \frac1{\Gamma(z-j)}{z-1-j\choose r}
 =\frac1{r!\Gamma(z-j-r)}
\]

and the derivative product rule give (A_zP_{z,y})^(j)(1)/(j!Γ(z−j)), as claimed.

The restoration of omitted moment degrees is legitimate. Explicitly, for every fixed j,

\[
 \sum_{\substack{d\mid\prod_{p\le y}p\\\omega(d)>h_0}}
 \frac{(\log d)^j}{d}
 \le 2^{-h_0}\sum_{d\mid\prod_{p\le y}p}
       \frac{2^{\omega(d)}(\log d)^j}{d}
 \ll_j 2^{-h_0}L^{C_j}.
\]

For the last bound, differentiate ∏_{p≤y}(1+2p^{-s}) a fixed j times at s=1; the derivative sums are O_j((log y)^j) times a fixed power of log y. This provides the needed arbitrary log accuracy without a growing-order derivative or an unjustified factorial-tail moment estimate. After collecting a sufficiently large fixed number of terms, all extra fixed terms beyond N are small by candidate (6). Every fixed N beyond a sufficient threshold works.

For k≤L^C, every prime of k is eventually ≤y. The principal character on rough integers is therefore identically one; unit classes have principal density b_{z,y,N}/φ(k). The unweighted density is V_y/φ(k), not V_y/k. Nonprincipal sums follow by the finite roughness expansion and the already proved SW estimate. This verifies Lemma 2, including its normalization and polynomial modulus/time costs.

## 3. Uniform bounds, truncations, and aggregate square errors — candidate 158–314

**Pass.** Since (an)_y=a n_y for every y-smooth a, the quotient n/n_y is unchanged, even with overlapping prime powers. Thus (4) has exact covariance on all positive integers, without truncating the definition. The tuple primes are outside y, so T_x(an)=T_x(n) as well.

For fixed derivative order j, logarithmic derivatives of P_{z,y} are O_j((log y)^j). Finite differentiation gives

\[
 |(A_zP_{z,y})^{(j)}(1)|\ll_{j,z}|P_{z,y}(1)|(\log y)^j.
\]

On the cutoff support log v≥εL/4, its jth density term is bounded by a fixed constant times |P_{z,y}(1)|L^{Re z−1−(1−ρ)j}. Also |P_{z,y}(1)|/V_y≈L^{ρ(1−Re z)}. Summation over the harmonic tuple mass proves

\[
 \|\mathcal B_x\|_\infty\ll_N L^{-(1-\rho)(1-\Re z)}.
\]

This exponent remains positive for every fixed nonreal root, however close to 1. Coefficient cancellation is used before taking absolute values; replacing P_{z,y}(1) by its absolute coefficient sum would not give this result. For every fixed number of smooth derivatives the log exponent can be independent of N: the finitely many higher terms have geometric powers L^{−(1−ρ)j}, with a threshold depending on N. This is the precise reason the later B–N choice is noncircular.

For η=1/log y, the y-smooth Euler product at 1−η is L^{O(1)}: its logarithm differs from the one at 1 by O(1). Hence the reciprocal mass of a>D₀/y is at most L^C exp(−cL^.04). Whenever n_y>D₀, successive multiplication of prime factors yields a divisor a in (D₀/y,D₀]. This is a positive short-divisor envelope, not merely a density heuristic.

For roughness, the Bonferroni remainder is bounded by binom(ω_{≤y}(v),h₀+1). The reciprocal mass of this envelope is at most (C log L)^(h₀+1)/(h₀+1)!, and all its divisors are ≤exp(O(L^.47)). For a compatible congruence in a tuple term, CRT gives O_M(x/(ℓra)+1). Every product of the fixed number of envelope divisors has size exp(O(L^.5)), hence ordinary coefficient mass x^{o(1)}. The long-tuple count is at most d!x^{1−ε}. Thus the total rounding loss is x^{1−ε+c₀+o(1)}, even after the presieve-modulus sum. Reciprocal tails pay the remaining harmonic r-sum. For model terms, the tuple occurs harmonically and not as a divisibility constraint; their rounding loss is smaller. Shared factors with M cost only a fixed factor. A divisor sharing a prime with r makes the condition r|u+1 impossible.

For clarity, the aggregate square bound can be made explicit. Summing the finite roughness errors over possible smooth parts a|n introduces at most τ(n_y), not a sum of independent L² norms. Apart from a fixed log factor and the bounded harmonic tuple sum, its pointwise absolute value is bounded by

\[
 \tau(n_y)2^{\omega_{\le y}(n)}
     1_{\omega_{\le y}(n)\ge h_0}.
\]

Square this, use 4^w1_{w≥h₀}≤2^{−h₀}8^w, and apply a fixed divisor moment to τ(n_y)^2 8^w. Such moments are O(RL^C) on a dyad. One can see this from the positive divisor expansion of its increasing local factors; their first-order coefficients are fixed multiples of 1/p. Thus the square error is O(RL^C2^{−h₀}). The smooth-part tail has the same conclusion by Cauchy and a higher fixed moment. This proves the error used in (15). It does not use Minkowski followed by Σa^{-1/2}, or multiply an L² error by x^{c₀}.

On a physical list with product P, n_y=P(n/P)_y. The Rankin shift costs P^η≤L^{O_J(1)}, since log P=O_J(L^.46 log L). The fixed divisor moments acquire at most another L^{O(J)} factor. Their tails still save every log power after J is fixed. These are error bounds after the physical family is selected; they do not affect the J-independent first-vector norm bound, which uses the actual bounded model.

## 4. All local tests and rational frequencies — candidate 373–401

**Pass.** H_x may take arbitrary values on smooth parts, with the displayed log-power bound. No continuity or separation of that test is being smuggled in. After n_y≤D₀, the genuine term n=ℓav has coefficient z^d f_z(a)H_x(a), scale Y/(ℓa)≥x^{ε−o(1)}, and Ramanujan factor c_k(haℓ)/φ(k). The model term is n=av; its unweighted rough density cancels the exact 1/V_y in (4), leaving c_k(ha)/φ(k) and the same density evaluated at Yu/(aℓ).

Multiplication by ℓ permutes units modulo k. Therefore c_k(haℓ)=c_k(ha), including h=0 and nonunit a. There is no division by a. The proof includes primes dividing k, repeated small labels, and v sharing long-prime factors with ℓ. The cutoff χ is one because every retained residual logarithm is at least (ε−o(1))L. All errors sum with Σa^{-1}=L^{O(1)} and Σℓ^{-1}=O(1), after paying the local test, rational modulus, smooth derivative, and low-time costs. This proves the exact principal cancellation in (12), rather than a zero-main-term assertion for f_z itself.

## 5. Separate discrete high-time estimate — candidate 403–507

**Pass.** The scale symbols must retain D's definitions:

\[
 H'=U_1U_2\ge\exp(2L^{.39}-O(1)),\quad Y=xH',\quad
 H=H'/L^{C_6},\quad T_0=LY/H=xL^{C_6+1}.
\]

Here write P_s for the *scale* of the small-prime polynomial, not its value P_s(t). Since P_s≤exp(L^.36),

\[
 \frac{T_0}{Y/P_s}=\frac{LP_s}{H}\longrightarrow0.
\]

Knowing only Y=x^{1+o(1)} would not justify this comparison; the source's more precise lower bound on H' does. Both free big products are nonempty in every comparison in `prop:ideal-family`, so this applies to all comparisons, not a selected subset.

The genuine tuple contribution retains a long prime and obeys f_z(p_s p_l u)=z²f_z(u). All coefficient squares, small-prime exceptional-interval counts, and Fourier-tail estimates are unchanged. The sparse Gram matrix still has entries Σ_{n≈R}n^{i(t_i−t_j)}; f_z changes the tested vector, not the kernel. Its scale is ≥x^{ε−o(1)}, so D `cor:sparse-bound` applies. D `lp:prime-polynomial` bounds sums with weight p^{-1}; partial summation converts to the scale-normalized polynomial. The lemma permits all subintervals, logarithmic characters, long-slot scales between x^ε/2 and x^{1−ε}, and times up to x². The retained times and twists fit these bounds after B is increased. Small-mark squares and repeated-slot errors are first controlled on the whole time interval by coefficient mean square.

For the model, covariance removes p_s exactly. On the remaining scale R₀≈Y/P_s, decompose by n_y=a≤D₀, then apply the finite roughness expansion. This gives exactly (14), with μ(e), not μ(e)f_z(e): this expansion counts the unweighted rough part of the model. After n=ae v, the density amplitude is β(ev/ℓ). The normalized coefficient is f_z(a)H_rem(a)μ(e)z^d/(aeV_yℓ). Its absolute reciprocal sum is L^{C_*}; claiming O(1) here would be wrong. The same fixed exponent suffices for total variation of the amplitudes, independently of N.

The omitted aggregate coefficient has square mass O_A(R₀L^{-A}) by §3. Full-interval mean square gives precisely L^{-A}(T₀/R₀+log R₀). This is (15), and is paid before any restriction to exceptional times. No length-dominated mean square is required for the individual divisor scale R'=R₀/(ae), which may be smaller than T₀.

At moderate times, R'=x^{1+o(1)}≥x^{1−o(1)} and k≤L^C. Sum–integral comparison on each residue progression gives normalized error O(L^C(1+|t|)/R'), and logarithmic integration by parts gives O(L^C/|t|). Up to exp(L/(log L)^2) the error is x^{-c}; its squared integral remains x^{-c'} after decreasing the constants. The main integral costs L^{2C_*-B}, not the full interval length times L^{-B}. This verifies (16).

At larger times D `lp:log-phase` requires

\[
 \exp(L/(\log L)^2)\le R'\le2x^5,\quad k\le L^C,\quad
 \exp(L/(2(\log L)^2))\le |t|\le4x^3.
\]

All hold here, also after the retained logarithmic shifts. The lemma is uniform over every residue and every subinterval; partial summation therefore permits the present complex smooth amplitude. One can split e(h ae v/k) directly into residue classes without inverting ae. Its N'/k normalization is compatible with the 1/(ae) coefficient and the polynomial residue cost. This proves (17).

On ordinary times use the collapsed scale Y/P_s≫T₀. On exceptional intervals pay only their number exp(O(L^.9)), which is absorbed by exp(−2L/(log L)^{C19}); their full ambient time length is not paid. Choose high-time thresholds after the group/kernel/test exponents, then choose N for the required low-time accuracy. The preceding derivative bounds are what allow this order. The source local Mellin inequality and bilinear multiplier now bound every comparison for the difference endpoint (18).

## 6. The physical residual, covariance, and fixed progressions — candidate 509–571

**Pass.** D `prop:graph-transfer` and S `cor:transference-pairing` require the first vector to be independent of its marks at a fixed position. They allow dependence on that position. The conjugated first core 𝒲(n)[f_z(n)T_x(n)−𝓑_x(n)], its residue indicator, and its intact extra half damping satisfy this requirement. T_x is bounded on the physical positive-power ranges, and 𝓑_x is eventually bounded by one. The source reciprocal physical-list sum is ≤1. Thus the first norm exponent is independent of J and N, though the threshold may depend on them. The second endpoint retains the original G and divisor-moment norm. No ideal kernel is modified.

For graph list length J+1 and unshared count 1+|C_g|, the shared count is J−|C_g|. Therefore Ω(D_R)=Js−c_ν, with multiplicity. Since all labels are y-smooth and all tuple primes are outside y,

\[
 [f_zT_x-\mathcal B_x](D_Rw)
 =z^{Js-c_\nu}[f_zT_x-\mathcal B_x](w).
\]

The other inert factor 𝒲 is invariant under active labels. This verifies (19), including repeated auxiliary labels and every lower density coefficient. The phase after dividing the common factor is z^{−c_ν}; replacing it by z^{c_ν} fails already at z=i,c_ν=1. All collisions retain the source's absolute exponential errors because the new core is bounded.

Full physical dyads and the Mellin insertion must be restored before shared-label averaging. Their cutoff and measure are then

\[
 \frac1{D_Rw}\Psi\!\left(\frac{w}{xD_C}\right),
\]

so shared labels have harmonic laws and the cutoff no longer depends on them. The original Schur bound handles the Mellin tail. A full small interval supplies fixed-modulus unit mixing. The residue identity is valid even for nonunit r,w: subtracting tw=r and t(w+D_C)=r+1 forces tD_C=1, so exactly one unit t is possible, and it works precisely when w=rD_C. This is why no inverse of r is needed.

The original operator norm consequently controls the raw difference plus **all** comparison differences with their inverse phases. Sections 4–5 supply arbitrary precision for each comparison, including the fixed-residue Fourier shifts to denominators ≤Mk. Their total coefficient, arc, dyad, and pattern costs are fixed log powers. Subtracting them isolates the raw difference and proves PM. This is a valid use of the original residual family; it does not infer a separate raw bound directly from an operator estimate on their sum.

## 7. Summed presieve remainder and principal corrections — candidate 575–674

**Pass.** The nonunit reduction merits retaining all its conditions. In u=ℓav, a=u_y, the long product is a unit modulo rM because c₀<ε and M is fixed. The rough v is a unit at every prime of M. Let g=gcd(b−1,M). Compatibility is exactly

\[
 (a,r)=1,\qquad \gcd(a,M)=g.
\]

Prime by prime, if v_p(g)<v_p(M), then v_p(a)=v_p(g); if v_p(g)=v_p(M), then v_p(a) may be larger. In either case a/g is a unit modulo M/g. Combined with the reduced class modulo r, the congruences specify a reduced class modulo q=rM/g. For primes whose entire M-valuation was removed in g, roughness still excludes those primes from v; being reduced modulo q alone would not do so. Example: M=4,b=1,a=8,r=1 gives q=1, but v remains odd. The candidate keeps roughness throughout and therefore handles this example correctly.

The model u=av has the same q and compatibility conditions, though its residue can differ from the genuine tuple's. Both are reduced. No extra factor g is missing: after fixing a, the scale is R=x/(aℓ) for the genuine term and x/a for the model, and the reduced-class density is divided by φ(q). At the elementary unweighted level, compatibility gives 1/q=g/(rM), which is the correct reduced period in v.

Insert the positive roughness truncation in the progression sum and in its centered natural mean. Only e coprime to q survives a reduced class. For each such e, q≤Mx^{c₀}<(R/e)^{1/3} eventually, and r↦rM/g is injective. The same strict inequality holds at all endpoints used by smooth partial summation. Apply fixed-function BV, sum its errors using Σe^{-1}=L^{O(1)}, and control the discarded envelope by the direct CRT/rounding estimate of §3. The natural-mean envelope is multiplied only by Σq^{-1} or Σφ(q)^{-1}, both logarithmic. This proves the centered rough BV statement actually needed in PR.

Removing additional natural-mean exclusions at primes p|q,p>y costs O(RΣ1/p). The aggregate after division by φ(q) satisfies

\[
 \sum_{q\le Q}\frac1{\varphi(q)}\sum_{\substack{p\mid q\\p>y}}\frac1p
 \le \sum_{p>y}\frac1{p(p-1)}
                \sum_{t\le Q/p}\frac1{\varphi(t)}
 \ll \frac{L^{O(1)}}y.
\]

The inequality φ(pt)≥(p−1)φ(t) also covers p|t. This is a bound over ordinary moduli, with no prime-shift input.

The genuine principal term is (22). For the model the unweighted rough density in a reduced class is exactly

\[
 \frac{V_y}{q\prod_{p\mid q,\ p\le y}(1-1/p)}
 =\frac{V_y}{\varphi(q)}\prod_{p\mid q,\ p>y}(1-1/p).
\]

Multiplication by 1/V_y cancels the rough density factor. The remaining product can be replaced by one using the preceding aggregate bound, with the bounded amplitudes and log-power a-mass. What remains agrees with (22) term by term, including every retained lower density coefficient. Summing over a and ℓ costs L^{O(1)} and O(1); summed rounding is still (9). Constants depending on a fixed inert array or fixed finite collection disappear after x→∞. PR does not assert such independence for growing arrays.

## 8. Positive sieve, Type II, and the decisive aggregation — candidate 676–773

**Pass.** For the positivity argument take Φ≥0 initially. Since |𝓑_x|≤1 eventually,

\[
 |f_zT_x-\mathcal B_x|\le T_x+1.
\]

Consequently all four real weights A₀±Φ𝒲 Re D_x and A₀±Φ𝒲 Im D_x, with the common class indicator, are nonnegative. PR gives each exactly the **same unsigned progression main term** as A₀, namely

\[
 \frac{x}{rM}\left(\int\Phi\right)m_{\mathcal W}(C_x+1)
\]

for sieve divisors coprime to M, with arbitrary-precision summed errors including r=1. This is not an application of positivity to a complex main term. Designating only primes outside M gives densities 1/p and the product

\[
 \prod_{p\le x^\gamma,\ p\nmid M}(1-1/p)
 =\frac M{\varphi(M)}\prod_{p\le x^\gamma}(1-1/p)
\]

eventually. The block sieve level x^{γ(4h+2)} is strictly below x^{c₀}. Subtracting each pair cancels the common main term. After division by xm_𝒲/L the surviving constant involves only fixed M, tuple and cutoff data, not K, array, or h. The source's unsigned upper sieve applied to Φ𝒲, times sup|𝓑_x|, makes the presieved model o(xm_𝒲/L) for each fixed h and array. This proves the claimed passage from D_x to f_zT_x in (24).

For Type II, selecting K inert primes in a gives

\[
 f_z(ah)T_x(ah)=z^K f_z(h)T_x(h).
\]

The remaining unit-modulus factor is outside the original common-h Cauchy square. Its α,β coefficients are unchanged, as are the rough support and both positive-power dyadic scale conditions. P's proof supplies the scalar square estimate under its actual character/Mellin interface; D `maj:long-coefficient` supplies that interface for the original prime-minus-rough coefficient. Multiplying α,β by fixed progression characters only replaces test moduli by lcm(M,k). It does not insert f_z into α. Source clipping, square deletion, convolution truncation, threshold/logarithm stripping, and Fourier tails all apply in absolute value. Sufficient K is chosen after the fixed h,γ and finite j range, independently of inert-band exponents.

Here is the aggregation as an explicit pointwise identity, rather than an appeal to the phrase “common model.” Let 𝒞 be the candidate groups, v=∏m_i, u=v−1, and let 𝓡 be the retained subsets of successes. Set

\[
 R(u,v)=\sum_{S\in\mathcal R}
       \prod_{g\in S}s_g(u,v)\prod_{g\notin S}(1-s_g(u,v)).
\]

Then 0≤R≤1. Its exact signed expansion is

\[
 R(u,v)=\sum_{S\in\mathcal R}
     \sum_{T\subseteq\mathcal C\setminus S}
       (-1)^{|T|}\prod_{g\in S\cup T}s_g(u,v).
\]

Off candidate-square exceptions, the source allocation identity transforms the tuple sum for P=S∪T into

\[
 c_1^{|P|}j^{|P|}
 W_{1,P}(u)W_{1,P}(v)G_P(v).
\]

All original coefficients are independent of the allocation: their thresholds and logarithms use bars removing **all** candidate prime parts, including inactive groups. Both the class condition v≡b (M) and Φ((v−1)/x) depend only on the product. So do 𝒲(v−1) and 𝓑_x(v−1). Thus, with the actual multiplicities of (S,T) and signs retained, reversing allocation and then reversing expansion transforms the **sum** of (25) into

\[
 \sum_{m_1,\ldots,m_j}
  1_{v\equiv b\ (M)}\Phi((v-1)/x)\mathcal W(v-1)
  \mathcal B_x(v-1)R(v-1,v)\prod_i\widetilde a(m_i),
\]

up to the exponentially small candidate-square errors. A fixed number j is treated at a time. No dependence on an active set remains inside 𝓑_x. The factor c₁^{|P|}j^{|P|} is included before undoing allocation; it has not been dropped or bounded separately.

The coefficient ∏ã is positive. On its support, each factor exceeds x^γ, each is W-rough, and each ã(m_i)≤C_γ/(LV(W)). A full rough product box has O(xV(W)^j) tuples and therefore mass O(x/L^j). There are O(L^{j−1}) boxes. Its total mass is O_j(x/L), including the stripped thresholds, by the same support and bounds. The fixed 𝒲 is bounded; the class indicator and R can only decrease positive mass. Therefore the absolute value of the last display is

\[
 \le \|\mathcal B_x\|_\infty\,O_{j,K,\gamma,\Phi}(x/L)
 =o(x/L).
\]

The dependence on γ is harmless because h and hence γ were fixed before x→∞. This proves (26). The arbitrary log cost of 3^{|𝒞|}, j^{|P|}, and the physical family multiplies **only** the PM errors and candidate-square errors, not the final principal-model bound. The latter errors have sufficient accuracy uniformly over active sets. The failed-outcome error was discarded under positive mass before expansion and remains unamplified; there is no attempt to reconstruct or bound it using a signed expansion.

All the active sets contain full small intervals and satisfy PM. N can be selected once after the uniform bounds for their G_P, group counts, finitely many j, and fixed finite array collection. The all-small-prime definition gives the same position model in each of these applications. An active-set-dependent model would destroy the displayed pointwise identity; the exact diagnostic includes an elementary two-coin example of that failure.

This completes composite subtraction. The prime sum now carries f_zT_x, whose absolute value is the bounded T_x. Thus the accepted nonnegative deweighting square applies unchanged: it bounds the first Cauchy factor, while ordinary prime counting bounds the second. The model is no longer part of the deweighting statistic. The resulting limsup is exactly of the form (27). The order is interior data; h and γ; sufficient K; finite B arrays; physical families and high-time exponents; N and precision; x→∞; B→∞; h→∞ with a new fixed K as necessary. This proves (2).

## 9. Signed probability, total mass, and fixed roots — candidate 775–795

**Pass.** Attaching f_z(p−1) to a sampled prime creates a complex factorial measure with total variation dominated by its unsigned version. The interior statement (2), bounded tuple multiplicity, and unsigned endpoint strips give zero against compact interior tests, including the normalization change from log x to log(p−1). No signed monotone sandwich is used.

Multiply the interior measures by ∏t_i/(1−Σ_{j<i}t_j) to obtain size-biased measures. R006/D's unsigned limiting density integrates to one on the open simplex. Compact exhaustion and domination therefore give a zero weak complex-measure limit on the entire cube. At d=1 its total mass is exactly E f_z(p−1), so a separate d=0 analytic estimate is unnecessary. This is weak convergence, not convergence to zero in total variation.

Sorting finitely many draws is continuous. Each ranked coordinate differs from the full ranked coordinate by at most the unseen mass, whose unsigned limiting expectation is 2^{-d}. The test error is at most

\[
 \omega_H(\eta)+2\|H\|_\infty\,\mathbb E R_{x,d}/\eta.
\]

Take x→∞, then d→∞ and η→0. This proves every fixed ranked test for each nonreal mode. Fourier inversion uses only finitely many fixed roots for each m; −1 is supplied by R008 and 1 by R006. Roots arbitrarily close to 1 as m varies pose no problem when m is fixed: their positive exponent .54(1−Re z) need not dominate any fixed log loss, because no such loss remains in the aggregate principal bound. Finite dyadic decomposition and fixed-modulus PNT give the cumulative result. Nothing assumes Ω modulo m is a continuous function of the factor partition.

## 10. Clarifications, limits, and reproducible record

There is no unresolved proof repair in this verdict. The detailed inequalities above expand compressed arguments in the candidate without changing its model or conclusion. Four presentational points should be retained on integration:

1. Start the positive-sieve argument with Φ real and nonnegative. Arbitrary real smooth compact tests are differences of two such tests (use a smooth dominating bump), and complex tests are handled by real and imaginary parts. This proves the candidate's broader cutoff formulation by linearity; the four weights are not themselves nonnegative for complex Φ.
2. In §6, define Y=xH', H=H'/L^{C₆}, and distinguish the small-prime scale P_s from P_s(t). The scale domination is stronger than the shorthand Y=x^{1+o(1)}.
3. The inverse f_z^{-1} in the convolution sense is μf_z. Granville–Shao part (b) needs its membership in C, not a separate inverse-SW assumption. The principal branch remains nonzero throughout.
4. In §9 display the complete signed sum with coefficients (−1)^{|T|}c₁^{|P|}j^{|P|} before reversing allocation. The positive bound is on that combined sum, with the common 𝓑_x. The source rough-box constant can depend on fixed γ as well as j; it vanishes in the first limit and does not alter the later h-limit.

These are explicit conventions or fully supplied elementary clarifications, not a conditional pass awaiting a new lemma. In particular, the moderate-time integral, the aggregate square-error bound, and the aggregate model-mass estimate have been justified here as asymptotic arguments.

The companion check gives no shortcut that would make the new bridge automatic. E's `sh:sign` is supported on active bands and its passage after `sh:small-square-error` uses sign one on the complementary factors. O's printed Elliott theorem is a qualitative ordinary-integer statement for fixed bounded multiplicative inputs. Neither supplies the prime-normalized marked estimate here. R008 removes algebraic-log principal terms specifically at z=−1; it does not remove those for nonreal z. The probability/Fourier consequence is routine once (2) is proved, and is not an additional counted result. Worldwide novelty and significance beyond this source comparison remain a separate task.

Reproduce from the project root:

```sh
python3 frontier/experiments/i10_complex_modes_r2/retrieve.py
python3 frontier/experiments/i10_complex_modes_r2/check.py
python3 frontier/experiments/i10_complex_modes_r2/record.py
```

The exact diagnostics cover 181,888 CRT cases (including 9,549 compatible nonunit cases and 3,015 extra-valuation cases), 56,448 Ramanujan invariances, 972 rough-density normalizations, 3,500 Bonferroni envelope/square checks, 243 density-coefficient identities, 3,000 symbolic position-covariance cases, 243 retained-coin expansions, and 3,888 allocation identities. They test fragile finite algebra only. No prime-count sampling or finite balance calculation is offered as evidence for an asymptotic.

Artifacts:

- [Input hashes](../sources/i10_complex_modes_r2/input-manifest.json), [complete path inventory](../sources/i10_complex_modes_r2/complete-preprint-inventory.txt), and [inventory screen](../sources/i10_complex_modes_r2/inventory-screen.json).
- [Fresh pinned-source retrievals](../sources/i10_complex_modes_r2/retrieval-manifest.json), [primary-source hashes](../sources/i10_complex_modes_r2/literature-manifest.json), and [inspected line ranges](../sources/i10_complex_modes_r2/source-ranges.json).
- [Exact diagnostic output](../experiments/i10_complex_modes_r2/results.json), [final validation](../sources/i10_complex_modes_r2/final-validation.json), and [artifact manifest](../sources/i10_complex_modes_r2/artifact-manifest.json).

All 90 snapshotted input files remained unchanged at final verification. All 14 fresh pinned files, 11 retained candidate files, and 38 retained i07 files match their immutable tree blobs and recorded hashes. This audit used no agents, staging, commits, shared-index changes, or other-project writes. Writes are confined to this review and `frontier/{sources,experiments}/i10_complex_modes_r2/`. Hash checks establish provenance, not truth; the PASS rests on the source-contract and mathematical analysis above.
