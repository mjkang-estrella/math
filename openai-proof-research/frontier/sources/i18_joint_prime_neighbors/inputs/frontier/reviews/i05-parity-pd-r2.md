# Independent review r2: full Liouville parity and prime-predecessor PD

Date: 2026-10-08. Premise: all applicable results in `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted as true, together with the accepted R006 progression theorem and its full probability argument.

**Verdict: PASS.** The candidate's CT, LC, SPR, signed extraction, and signed size-biased argument establish Theorem LP and all its stated squarefree/Möbius consequences under these premises. I found no unresolved analytic gap. In particular, LC is proved using new ordinary-integer Liouville cancellation at low frequencies and the retained long-prime factor at high frequencies. It is not obtained by substituting full Liouville into E's band-sign theorem. The proof does not need a signed constant-term high-frequency estimate.

This is a proof-review recommendation, not parent integration or an upstream truth audit. The target is a substantial additional parity theorem beyond R006 and its routine squarefree corollary. The bounded primary-literature comparison below supports that distinction; it does not certify worldwide priority or establish the assumed corpus independently of the user's premise. No agents, commits, staging, external posts, or shared edits were made. Corrections and clarifications appear only here. All evidence writes are in `frontier/{sources,experiments}/i05_parity_pd_r2/`.

## 1. Exact scope of the passing theorem

For each fixed positive integer M and reduced b modulo M, let p be uniform over class primes in either `(x,2x]` or `[3,X]`. Write V(p) for the decreasing logarithms of the prime factors of p−1, with multiplicity, normalized by log(p−1). Let L have PD(1), λ(n)=(−1)^Ω(n), and B(n)=μ²(n). For every fixed k and continuous complex H on `[0,1]^k`,

\[
 \mathbb E[\lambda(p-1)H(V_1(p),\ldots,V_k(p))]\longrightarrow0.
\]

Together with R006 this implies the joint convergence

\[
 (V_1(p),\ldots,V_k(p),\lambda(p-1),B(p-1))
 \Rightarrow (L_1,\ldots,L_k,S,B),
\]

where S is uniform on `{−1,+1}`, B is Bernoulli with parameter C_{M,b}, and these variables and the partition are mutually independent. For e=v_q(M),

\[
 C_{M,b}=\prod_q(1-\rho_q),\qquad
 \rho_q=\begin{cases}
 [q(q-1)]^{-1},&e=0,\\
 1/q,&e=1,\ b\equiv1\pmod q,\\
 0,&e=1,\ b\not\equiv1\pmod q,\\
 1,&e\ge2,\ b\equiv1\pmod{q^2},\\
 0,&e\ge2,\ b\not\equiv1\pmod{q^2}.
 \end{cases}
\]

The prime 2 is included. Thus E[μ(p−1)H(V(p))] tends to zero, and E[1_{μ(p−1)=s}H(V(p))] tends to `(C_{M,b}/2) EH(L)` for s=±1. Conditional PD assertions apply when the conditioning event has positive limiting probability. A forced square gives C_{M,b}=0 and no squarefree primes in that class. The Liouville conclusion still holds there.

All moduli, tests, tuple dimensions, and separation parameters are fixed before taking real endpoints to infinity. There is no claimed rate, effective threshold, growing-modulus version, other-shift theorem, or arbitrary completely multiplicative sign extension. This is the full maximal theorem established by this candidate; no reduction of its conclusion is necessary.

## 2. Materials read and source integrity

I read AGENTS.md, `sources/upstream.json`, the relevant catalogue entries and complete path-tree metadata, the complete 470-line candidate, its source/validation/artifact manifests and experiment, the full R006 record, the complete 439-line i03 proof, the complete 255-line r4 audit, the parent squarefree/sign warning, and the iteration index. The previous audit supplies context and accepted R006 facts; it is not a verdict on the new parity bridges.

The source abbreviations are these exact directories below `preprints/` at the pin:

- D: `The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/`.
- S: `Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/build/`.
- P: `Primitive-roots-for-every-admissible-integer-base-October-4-2026/build/`.
- T: `Simultaneous-primitive-roots-a-conditional-lower-bound-for-prime-bases-October-4-2026/build/`.
- E: `Prime-Predecessors-with-an-Even-Number-of-Prime-Factors-September-17-2026/build/`.

[Independent verification](../sources/i05_parity_pd_r2/verification.json) checks all 60 cached pinned files against their SHA-256, Git blob, byte count, immutable URL, and the untruncated preprint tree. All pass. Fourteen decisive interfaces were independently downloaded from the pinned raw URLs; all match the cached bytes and tree. All 81 author artifact entries pass. Six cached external-download hashes pass, with the known HTML access page correctly excluded as mathematical evidence; five genuine primary PDFs were downloaded again and match exactly. The failed extra direct literature download is recorded separately from the successful web reading.

[Source ranges](../sources/i05_parity_pd_r2/source-ranges.json) records inclusive line intervals and independent SHA-256 hashes of their exact newline-preserving bytes. These identify the proof interfaces inspected, not just manuscript titles. Especially relevant are:

- D §3, lines 41–133: invariant-F theorem, selected-prime reduction, and `det:cauchy-square`; D §4, lines 1–34: `mem:replacement-interface`; D §5: `maj:long-coefficient` and completion of the scalar square estimate.
- P §8, lines 92–251: the full `lem:marked-coefficient-transfer` statement and proof, including the scalar square and its parameter order.
- D §6: the exact graph family, endpoint norms, stripping and collision errors, multiplier/local Mellin reduction, divisor model, and the entire tuple high-frequency argument. The complete section was read, including its separate constant-part argument to identify what is not available after inserting λ.
- S §2, lines 1260–1283: `cor:transference-pairing`; D §9: `lp:prime-polynomial` and `lp:log-phase`, with their actual scale, modulus, interval and frequency ranges.
- D §7: the complete progression, presieve, proxy, positive coin-partition, allocation, and deweighting arguments; D §8: the full factorial/size-biased/sorting passage.
- E §3: `sh:sign`, `sh:core`, `sh:discrepancy`, and the passage from `sh:small-square-error` to `sh:four-factors`; E's actual main theorem; T's fixed-character criterion; the ordinary two-point companion's actual introductory statements.

For example, the independently verified SHA-256 of D §6 is `09d0d46506b82c0cc8c0f04d5c4ff39abe9b6699b7ab04078e73f759d6c46f1d`; that of P §8 is `97b1d9b0456a5951a25bbd9ee297da2c275a9c63e202aef139ad63e2c834794e`. Complete URLs and the other hashes are in the manifest. Byte checks do not verify a theorem's truth.

The closing [validation record](../sources/i05_parity_pd_r2/final-validation.json) found only a concurrent change to the shared iteration index. The parity candidate, original experiment, R006, its complete proof/audit, and the pin were unchanged. I reread the current index; its ongoing independent research lanes do not change this review's hypotheses. This review did not edit that index.

## 3. Classical input and its precise use — candidate §3

**Pass, with a citation precision correction.** Pintz's equation (1.5), printed page 2 of [arXiv:1004.1067v1](https://arxiv.org/pdf/1004.1067v1), explicitly supplies the Liouville Bombieri–Vinogradov bound with level one half minus a fixed positive amount. Its displayed maximum is unrestricted; the proof here needs only reduced classes. This is a statement about λ on integers. The adjacent discussion distinguishes it from shifted-prime questions.

[Shao, ANT 11 (2017), printed page 961](https://msp.org/ant/2017/11-4/ant-v11-n4-p06-p.pdf), gives an exceptional-modulus formulation, with a centered global mean, and says the statement applies to μ and λ. It is corroboration, not a verbatim second display of the candidate's summed zero-main-term formula. The needed summed formula is already supplied by Pintz. There is no excluded-character proviso to add to the bound being used; ineffective constants are permitted.

Here is the smoothing argument explicitly. For a smooth weight supported in `[cR,CR]`, c>0 fixed, integrate its derivative against the cumulative progression sum. Triangle inequality puts the modulus sum inside that integral. All integration endpoints are comparable to R. The strict exponent margins below ensure the chosen modulus range is inside the BV range at every such endpoint. This uses no sum of endpoint suprema. An inserted phase n^{it} contributes a variation cost O(1+|t|) times the prescribed logarithmic derivative bounds.

For the low-frequency consequence, let g=gcd(a,k), using g=k for a=0, and write n=gv. Then

\[
 n\equiv a\pmod k\quad\Longleftrightarrow\quad
 v\equiv a/g\pmod{k/g},\qquad (a/g,k/g)=1,
 \qquad \lambda(gv)=\lambda(g)\lambda(v).
\]

No condition `(g,v)=1` is needed. If `k≤L^C` and `R≥x^ε`, then `R/g≥x^{ε/2}` eventually. A single modulus k/g lies within a fixed sub-half-power BV range at this scale. Choose its arbitrary accuracy after the modulus, phase and derivative costs. Dividing the result by R gives a factor 1/g and arbitrary negative powers of L. It also covers k=1. This proves precisely the candidate's SWλ, uniformly in its stated positive-power scale range, including nonunit classes. It does not assume cancellation on prime shifts.

## 4. CT: identical scalar determinant square — candidate §4

**Pass.** Write a=∏_{i=1}^K p_i, selecting one prime from each disjoint inert band. Complete multiplicativity and invariance of F₀ give, whenever mn−1=ah,

\[
 \lambda(mn-1)F_0(mn-1)=(-1)^K\lambda(h)F_0(h).
\]

This remains true if any selected p_i divides h. The source square-divisibility deletion is needed for the damping exponent, not for this identity. Its error was already bounded absolutely, with bounded endpoint multiplier, and so is unchanged.

For a real selected-product cutoff ρ, define

\[
 T_Y(h)=\Bigl(\prod_iV_i^{-1}\Bigr)
       \sum_{mn-1=ah}\rho(a/Y)\alpha_m\beta_n.
\]

The signed dyadic sum is `(−1)^K Σ_h λ(h)F₀(h)q^{ω(h)}T_Y(h)`. Consequently

\[
 |S_Y^\lambda|^2\le O(X/Y)\sum_h|T_Y(h)|^2.
\]

The sum on the right is literally D's `det:cauchy-square` and P's `eq:type-ii-cauchy-square`, with α_m conjugate(α_{m′}) β_n conjugate(β_{n′}) and the original common-h incidence. Neither coefficient has acquired λ. All determinant kernels, rough-support conditions, good-state restoration, operator moments and major forms therefore remain the original scalar objects.

P's proof explicitly gives both the scalar minor-transfer error and the scalar major bound for coefficients satisfying its criterion. The new proof uses those bounds after the displayed Cauchy reduction; it does not apply the printed invariant-F theorem directly to λF₀. That distinction closes the apparent hypothesis failure.

For the class mn≡b modulo fixed M, character orthogonality puts χ₀(m) and χ₀(n) into α and β. A tested character χ modulo k combines with χ₀ into a possibly imprimitive character modulo lcm(M,k), with the correct zero extension. Eventually this modulus is at most `L^{A₀+1}`. D's actual `maj:long-coefficient` covers all such characters and the entire required frequency range `|t|≤2XL^B`, including conjugates. Its scalar coefficients depend on x, W, interval and twists, not on the number or exponents of inert bands.

Choose square precision first, then the moment accuracy and arc exponent, then sufficient fixed K, independently of later inert exponents. Major-term accuracy can be chosen after the arc exponent under the coefficient criterion. Fixed χ₀ and the finite character sum cause only allowed fixed costs. This is the same order used in the source and R006. The false assertion that scalar cancellation survives α↦λα is neither needed nor made.

## 5. LC physical lift and stripping — candidate §§5–5.1

**Pass.** The source uses graph list length m_graph=J+1, since ℓ=1. In group g the unshared endpoint count is t_g=1+|C_g|. The number of shared labels in that group is therefore

\[
 m_{\rm graph}-t_g=J-|C_g|.
\]

Summing gives Ω(D_R)=Js−c_ν, where c_ν=Σ_g|C_g|, while Ω(D_C)=c_ν, counting multiplicity. Thus

\[
 \lambda(D_Rw)=(-1)^{Js-c_\nu}\lambda(w)
              =(-1)^{Js}(-1)^{c_\nu}\lambda(w).
\]

Using `(J+1)s−c_ν` here would be wrong. The candidate uses Js correctly. Auxiliary free labels may repeat; Ω counts slots with multiplicity, so repeated primes do not change the formula. Shared-label collision exceptions affect stripping of the marked weights, and still require the source's absolute bounds. The prefactor `(−1)^{Js}` may vary with x, but has modulus one and is divided out before estimating the raw term. No limit for that sign is needed.

Use the first physical vector built from the uncentered `𝒲 f_x`, multiplied by λ(n) and the position residue indicator. This is constant on the mark fiber at fixed n, exactly as required by S `cor:transference-pairing`; it need not be invariant under n↦pn. The second vector has only its norm requirement. The uncentered f_x is bounded on every relevant `x^{1+o(1)}` position range: the number of factors at least x^ε is bounded in terms of ε. Subtracting C_x was not needed for the physical norm proof. The source reciprocal physical-list sum is at most one, and the intact half-damping is at most one. Thus the norm exponent used before selecting J is unchanged and independent of J. The supremum condition is also met.

Keep the original ideal kernels. Transfer bounds their entire signed residual combination paired with these permissible vectors. Only afterwards strip the positions and calculate the new pattern signs. There is no assertion that modifying an ideal kernel by a pattern sign preserves its operator norm.

Reassemble all physical dyads and the full Mellin integral before using residue mixing. The discarded Mellin tail is controlled by the source absolute Schur bound and unchanged norms. After reassembly,

\[
 n=D_Rw,\quad n'=D_R(w+D_C),\quad
 \frac{\Psi(n/(xD))}{n}=\frac1{D_R}\frac{\Psi(w/(xD_C))}{w}.
\]

The new sign is constant in the sampled shared labels. The remaining unsigned cores and marks strip exactly as in D; the `1/D_R` gives the harmonic shared-label probability laws. No cutoff depending on D_R remains. The original absolute collision estimates still apply with |λ|=1.

At least one small group is a full interval, as LC explicitly requires for M>1. All its J padding labels are shared. After removing collision bans, fix w, free and unshared labels, and all but one such shared label. Fixed-modulus prime equidistribution makes the remaining product uniform among units to arbitrary log precision. Do not condition on either endpoint residue event. For a unit d=D_C,

\[
 \frac1{\varphi(M)}\sum_{t\in(\mathbb Z/M)^\times}
  1_{tw=r}1_{t(w+d)=r+1}
   =\frac1{\varphi(M)}1_{w=rd}.
\]

Subtracting the congruences forces td=1, including when r or w is a nonunit. After division by the common sign, the raw pattern has coefficient 1 and each comparison has the additional coefficient `(−1)^{c_ν}`. This gives exactly the candidate's residual equation. It does not yet prove LC; the following independent comparison estimate is essential.

## 6. LC comparison energy — candidate §§5.2–5.3

### Residues and low times

**Pass.** Splitting the two free products into fixed residue classes preserves their separate bounded tests and squared coefficient bounds. The bilinear multiplier argument is unchanged. For the first endpoint the residue projection is additive, so it includes nonunits. Its Fourier energy is bounded by the average of M shifted energies. Rational denominators increase from k to at most Mk; any fixed logarithmic exponent can be increased by one for large x.

Keep `H′≥exp(2L^.39−O(1))`, `Y=xH′`, and set `H=H′/L^C` for the enlarged fixed exponent. The source local Mellin lemma reduces the desired energy to the integrated square of

\[
 Y^{-1}\sum_w\psi_1(w/Y)w^{i(t+\sigma)}\lambda(w)f_x(w)
               H_{\rm marks}(w)e(hw/k),\qquad |t|\le T_0=LY/H.
\]

The coefficient square norm is `≪YL^{O(1)}`. The local Mellin tail and its additive error use only that norm; λ changes neither. The wider arcs change only fixed log costs.

At `|t|≤L^B`, fix a long tuple product ℓ. Since long primes lie outside all marked groups, `H_marks(ℓn)=H_marks(n)`. D's `lem:divisor-model` applies to the possibly arbitrary bounded big-mark tuple test, with divisor support `d′≤exp(O(L^.47))`, reciprocal coefficient mass `≪L^{C₈}`, and arbitrary-saving L² error on the needed dyads. Cauchy at scale Y/ℓ gives normalized error `≪L^{-N}/ℓ`; summing tuples costs only `Σ1/ℓ=O_{d,ε}(1)`. Multiplying by λ does not enlarge this error.

For a retained divisor, write `w=ℓd′v` and `R=Y/(ℓd′)≥x^{ε−o(1)}`. Its contribution is A_{d′}λ(ℓd′)/(ℓd′) times a normalized ordinary-integer λ sum at scale R, with smooth cutoff, log-power phase, and rational additive phase. Splitting that phase into k residue classes and applying the consequence in §3 gives arbitrary pointwise log saving. Pay the factor k, the reciprocal divisor mass, all derivative/twist costs, and the interval length L^B by choosing the classical accuracy last. This proves the required low-time integrated saving. There is no centered main term to cancel, and no prime-shift assumption.

### High times and the sparse Gram estimate

**Pass.** Every small group has t_g=1 in the comparison endpoint, and its bounded tuple test depends only on big marks. Hence the source small-mark extraction remains available. Small-prime squares and repeated long-slot primes have the same squared coefficient errors `≪YL^{O(1)}(exp(−L^.27)+x^{-ε})`. Since `T₀/Y=L/H=o(1)`, the source coefficient-independent mean square makes these errors negligible throughout the retained time interval.

The uncentered tuple is nonempty. After the same harmless repeated-slot relaxation, factor `w=p_s p_l u`, with p_l from the first long slot. Then

\[
 \lambda(w)=\lambda(p_s)\lambda(p_l)\lambda(u)=\lambda(u).
\]

The remaining coefficient is precisely D's `cor:u-coefficient` multiplied by λ(u). Even when p_l divides u this equality is exact, and the marked weight is unchanged because p_l is outside the groups. The residual coefficient retains the fixed divisor-power bound and collapsed squared norm `≪L^C/R₀`.

Rational-phase separation first uses residues for p_s and u, then character orthogonality on the unit p_l variable. It imposes no unit requirement on u. Dyadic decompositions and logarithmic Fourier separation have only fixed log costs. Their tails are handled before the sparse-time restriction, by the coefficient mean square on translated intervals. Retained time shifts are fixed log powers; enlarge B past those shifts and the eventual long-prime threshold. The low-time proof allows every such fixed B.

The residual scale satisfies

\[
 R_0\asymp Y/(P_sN_l)\ge x^{\varepsilon-o(1)}\ge x^{\varepsilon/2},
 \qquad R_0\le x^2
\]

eventually. On `|P_s(t)|≤L^{-A_s}`, the remaining collapsed product has scale Y/P_s and

\[
 (Y/P_s)/(2T_0)=H/(2LP_s)\longrightarrow\infty.
\]

This inequality survives every fixed log enlargement because log P_s≤L^.36 while log H′≥2L^.39−O(1). Ordinary mean square gives a fixed-log integrated bound for the remaining product, and the small factor pays it.

For exceptional unit intervals the source factorial estimate is coefficient-independent and permits residue restrictions and retained twists in the small-prime coefficients. It gives

\[
 |\mathcal J|\le\exp(O(L^{.36}+L^{.73}\log L))\le\exp(O(L^{.9})).
\]

For clarity, the sparse Gram kernel after inserting λ is still

\[
 G_{ij}=\sum_{n\asymp R_0}n^{i(t_i-t_j)},
\]

not a λ-weighted sum. The λ has entered the tested coefficient vector. Separated maximizing points, the ordinary sum–integral estimate at moderate differences, and the accepted `lp:log-phase` at larger differences bound each absolute Gram row by `O(R₀L)`. The latter is used at q=1 on the full integer dyad. Its lower scale condition follows from `R₀≥x^{ε/2}`, its lower frequency condition from `T_mod=exp(L/(log L)^2)`, and its upper frequency condition from `4T₀+O(1)<4x³`. Its exponentially small error absorbs |J|. Thus multiplication by the unchanged coefficient squared norm gives `Σ_{I∈J} sup_I |R(t)|²≪L^{C′}`.

The retained long-prime factor is still a prime sum with a character and a log-power twist, up to a constant sign. D's `lp:prime-polynomial` allows an arbitrary subinterval in its dyad, every character of fixed-log modulus, scales from x^τ/2 to x^η, and times from L^{B₀} to x². Choose τ<ε and η>1−ε. The actual slot dyad lies between x^ε/2 and x^{1−ε}; all retained times are below x². Increasing B covers the lower threshold and shifts. Its arbitrary log saving, multiplied by the small-polynomial supremum and the sparse residual bound, pays all exceptional-time and decomposition costs.

No residual polynomial has been required to possess scalar Liouville cancellation at high times. No signed version of `cor:constant-high` has been used. There is no constant part because f_x has not been centered. This is exactly why d≥1 is sufficient and necessary for the route as written. The unchanged multiplier/Parseval argument now bounds each comparison separately; subtracting them from the residual equation proves LC.

## 7. SPR and the nonnegative sieve — candidate §6

**Pass.** Use the source represented-union expansion, including repeated arrays, before handling λ. Its retained divisors and the positive first-omitted Bonferroni envelope have size `≤exp(O_K(L^.22))`. Their reciprocal coefficient masses are O(1) and `O(C_*^{h₀+1}/(h₀+1)!)`, respectively. Their ordinary coefficient masses are x^{o(1)}.

The envelope is estimated absolutely by the unsigned CRT count. For fixed ℓ,d′,r the compatible progression has at most its smooth main term plus O(1). Summing the main errors costs at most `x(Σ1/ℓ)(Σ_{r≤x^{c₀}}1/r)` times the factorially small envelope mass. The total rounding error is

\[
 x^{1-\varepsilon+c_0+o(1)}=o(xL^{-A})
\]

for every fixed A. This rounding sum is done before declaring the truncation error negligible. No L² error is multiplied by x^{c₀}.

Now fix ℓ,d′ and put a₀=ℓd′. Eventually `(a₀,M)=1`. If `(r,M)>1`, the conditions r|u+1 and u+1≡b modulo M conflict with b reduced. If `(r,a₀)>1`, they conflict with u=a₀v. Those terms are zero, including every overlap case. Otherwise `(r,M)=1` and `(r,a₀)=1`, and v is in one class a modulo rM with

\[
 a\equiv-a_0^{-1}\pmod r,\qquad
 a\equiv(b-1)a_0^{-1}\pmod M.
\]

It follows exactly that `gcd(a,rM)=gcd(b−1,M)=g`. Since g is fixed and coprime to r, writing v=gt gives a reduced class modulo rM/g. These moduli are distinct as r varies. Complete multiplicativity separates λ(a₀g) without requiring `(g,t)=1`.

At `R=x/a₀≥x^{ε−o(1)}`, the moduli satisfy

\[
 rM/g\le Mx^{c_0}\ll (R/g)^{1/3},\qquad c_0<\varepsilon/8.
\]

The strict power gap also holds at every cumulative endpoint in the fixed smooth support. Apply ordinary-integer BVλ with exponent 1/3 to this subset of moduli; triangle inequality bounds it by the sum over all eligible moduli. Smooth partial summation is uniform in the fixed tuple/divisor parameters because the rescaled cutoff is the same fixed Φ. The resulting bound for this pair is `≪_A R L^{-A}` (the additional 1/g can be dropped). Sum it with |A_{d′}|, using `Σ_ℓ1/ℓ=O(1)` and `Σ_{d′}|A_{d′}|/d′=O(1)`. This proves SPR without circular prime-shift information.

For parity presieving use a_±=Φ𝒲f_x(1±λ)/2 times the class indicator. Both are nonnegative. Their exact sum/difference identities and the unsigned progression estimate plus SPR give half the unsigned model to each, with summed arbitrary-log remainders, including the r=1 total mass. Sieve only by primes outside M. The model factor is

\[
 \frac1{2M}\prod_{q\le z,\ q\nmid M}(1-1/q)
 =\frac1{2\varphi(M)}\prod_{q\le z}(1-1/q)
\]

for each parity. D's block sieve accepts density 1/q≤1/2, has constants uniform in even depth h, and uses moduli at most z^{4h+2}<x^{c₀}. Subtraction cancels the identical main terms. The surviving error after dividing by m_𝒲 is `O_{M,d,ε,Φ}(e^{-h}/γ)`, independent of K,h and the chosen array. The bound `C_x=O_{d,ε}(1)` pays the model tuple mass. Array-dependent remainder constants vanish in the x-limit, even if the fixed mark mean is small.

## 8. Signed extraction and parameter order — candidate §7

**Pass.** Each modification is applied before the point where positivity is needed, or bounded in absolute value:

1. Presieved composites have a bounded number j of prime factors for fixed γ. Large prime squares have integer error O(x/z). The new factors |λ(u)| and the class indicator do not enlarge it.
2. Telescope to the original positive prime-minus-rough proxy. CT applies to the bounded clipped f_x, whose inert-band invariance holds globally because the long slots are disjoint from those bands. The companion coefficient remains rough and has the same divisor-power bound; truncation, smooth cutoff replacement, and Mellin separation are absolute. Fixed characters impose the product class. α is still the original discrepancy, not λα.
3. The candidate-free threshold/logarithm replacement is an absolute o(x/L) estimate under the positive tuple mass, with only a bounded factor `𝒲f_x`. It remains valid with λ(u).
4. Discard failed coin outcomes while their weights are a nonnegative partition. The source uniform failure estimate is then multiplied only by a bounded factor for the already fixed K. The later `L^{O(1)}` signed active-set expansion does not multiply this qualitative error. Every retained active set contains full small and big prime intervals and therefore satisfies LC's additional full-small-interval requirement.
5. With v=u+1 fixed, allocation of its active primes changes neither u nor λ(u) nor the progression condition. These factors stay outside the allocation sum. The exact identity `j^{ω_P(v)}(q₀/j)^{ω_P(v)−s_P}=j^{s_P}q₀^{ω_P(v)−s_P}` leaves precisely the original invariant G_P(v_*). Candidate-square deletions have exponential savings sufficient after all log-power expansion losses.
6. LC at r=b−1 and Ψ(t)=tΦ(t), followed by multiplication by x, bounds every expanded term to arbitrary accuracy. Choose that accuracy after the finite-log expansion cost. This eliminates composites.

The unsigned nonnegative deweighting square Z_B can be upper-bounded by the original unrestricted prime estimate. Cauchy's other factor for λf_x is bounded by the ordinary prime count and bounded f_x. Hence the final normalized limsup is bounded by

\[
 C_{M,d,\varepsilon,\Phi}\frac{e^{-h}}{\gamma}
       +C_{d,\varepsilon,\Phi}\sqrt{C_K/B}.
\]

Fix interior data and c₀; choose h, γ=c₀/(4h+3), the finite factorization lengths, sufficient K, and any finite B disjoint arrays. Take x→∞ first, then B→∞, then h→∞ with a new sufficient fixed K for each h. Arbitrarily many finite disjoint arrays fit into the inert exponent interval. No growing parameter is hidden in a fixed-array application. This establishes the signed interior statistic Iλ through real x.

## 9. Signed probability and recovery of total parity — candidate §8

**Pass.** Define the signed factorial measure by inserting λ(p−1) before averaging labelled factor balls. For every measurable set its total variation is bounded by the unsigned factorial measure. Iλ gives its vanishing on admissible interior rectangles. Cutoff removal uses bounded tuple multiplicity and fixed-class PNT. Changing log x to log(p−1) uses the unsigned mass of thin endpoint strips; it must not use monotone sandwich inequalities for a signed sum. Repeated numerical-prime corrections are bounded absolutely by the source square exception count, divided by the class-prime count, and vanish. A compact grid then proves convergence to zero for every compactly supported continuous interior test.

For size-biased sampling let ν^λ_{x,d} be the signed law of the first d draws, with the same sign attached to the entire sampling experiment. On the open simplex it equals the signed factorial measure multiplied by

\[
 w_d(t)=\prod_i\frac{t_i}{1-\sum_{j<i}t_j}.
\]

Moreover `|ν^λ_{x,d}|≤ν_{x,d}` as measures on the entire cube, including exhaustion events. The full R006 proof establishes that the unsigned ν_{x,d} converges to density `h_d(t)=∏_i(1−Σ_{j<i}t_j)^{-1}`, whose integral over the open simplex is one. This is a size-biased tightness statement, stronger than merely citing the ranked marginal law.

Choose a compactly supported cutoff χ with limiting unsigned integral greater than 1−η. For any continuous H on the cube, the signed integral of χH tends to zero, and

\[
 \left|\int(1-\chi)H\,d\nu^\lambda_{x,d}\right|
 \le \|H\|_\infty\int(1-\chi)\,d\nu_{x,d}
 \le2\eta\|H\|_\infty
\]

eventually. This proves weak convergence to the zero signed measure on the whole cube. For d=1 its total mass is exactly Eλ(p−1): every predecessor under consideration has positive total factor mass one. Thus the total parity mean is recovered without an analytic d=0 correlation theorem. Padding for larger d creates no issue because domination also controls its boundary mass.

Sort the first d draws and pad zeros. Each ranked coordinate differs from the true coordinate by at most the unseen mass R_{x,d}. The unsigned expectation tends to 2^{-d}. Multiplication by λ cannot enlarge the approximation error `ω_H(η)+2||H||∞ ER_{x,d}/η`. For fixed d the sorted test is continuous and its signed expectation tends to zero. Take x→∞, then d→∞, then η→0. This proves LP for every finite ranked continuous test, complex tests included. A fixed finite dyadic decomposition, followed by removal of its vanishing initial prime proportion, gives the cumulative version.

Parity itself is never asserted to be continuous in the normalized factors. This tightness argument is sufficient and does not borrow the conclusion it seeks.

## 10. Squarefreeness, prime 2, and four joint limits — candidate §9

**Pass.** For fixed Y the condition excluding q²|p−1 for q≤Y is a finite union of reduced classes modulo `lcm(M,∏_{q≤Y}q²)`, up to finitely many primes. R006 and the newly established LP apply to each fixed class. This gives respectively the unsigned squarefree-truncated PD mean and zero signed mean.

The local factors in §1 follow by counting reduced lifts. When q∤M, there is one bad class among q(q−1). When v_q(M)=1 and b≡1 modulo q, one of the q lifts is bad; otherwise none is. At exponent at least two, badness is already fixed by b modulo q². CRT factors these finite local counts. For q=2 the unconditioned bad probability is 1/2; p≡1 modulo 4 is forced nonsquarefree, while p≡3 modulo 4 has no 2-square obstruction. These cases must not be replaced by an odd-prime formula.

For Y<q≤x^{1/4}, the interval Brun–Titchmarsh bound gives `≪x/[q(q−1)log x]` for p≡1 modulo q². Its reciprocal tail is O(1/Y). The interval form is displayed in the introduction of [Ford's primary author paper](https://www.ford126.web.illinois.edu/wwwpapers/sigphi.pdf). For q>x^{1/4}, counting all integers gives `O(x^{3/4}+√x)=o(x/log x)`. A fixed progression restriction only increases the normalized bound by a fixed factor O(φ(M)). Hence the square-tail limit is uniform enough for bounded λ and H. Take x→∞ at fixed Y, then Y→∞.

We obtain the four moments

\[
 EH(V)\to EH(L),\quad E[\lambda H(V)]\to0,\quad
 E[BH(V)]\to C_{M,b}EH(L),\quad E[\lambda BH(V)]\to0.
\]

The exact identities `1_{λ=s,B=1}=B(1+sλ)/2` and `1_{λ=s,B=0}=(1−B)(1+sλ)/2` give each of the four joint atoms, with limits `(C_{M,b}/2)EH(L)` and `((1−C_{M,b})/2)EH(L)`. They prove mutual independence, not just two marginal independences. The Möbius claims follow from μ=λB. If a square is forced, B is identically zero in the class; otherwise the finite local factors are positive and the convergent tail product is positive.

The unsigned squarefree-conditioning result by itself is the parent's routine baseline. It is not counted as the new analytic achievement.

## 11. Independent computation and adversarial checks

The copied [author reproduction](../experiments/i05_parity_pd_r2/reproduce_author.py) writes only into this review's directory. Its entire `results.json` matches the original byte for byte. This reproduces the reported 2,000 pattern-sign cases, 344,498 signed-orbit cases, 6,050 reassemblies, 267 determinant checks, 939 divisor/nonunit checks, 999 positive parity splits, 11,880 allocation checks, and the finite prime screen through 10⁶. Individual-dyad bias examples and all rejected-shortcut examples reproduce.

The independently written [adversarial script](../experiments/i05_parity_pd_r2/independent.py) gives [these results](../experiments/i05_parity_pd_r2/independent-results.json):

- 458 actual common-h determinant rows from incidences mn−1=ah, with rational complex coefficients, verify the unchanged square; the input includes 526 incidences with selected-prime/residual overlap.
- 2,336 source-slot sign cases, including 2,248 cases with repeated labels, verify the Js−c_ν count.
- 416,000 ordinary nonunit residue-reduction cases pass, including 1,505 compatible cases with gcd(g,residual)>1.
- 93,888 SPR CRT cases pass: 19,834 incompatible `(r,M)>1` cases, 22,878 incompatible `(r,ℓd′)>1` cases, and 13,651 compatible nonunit-residue cases.
- 9,830 exact local square-density cases pass, including prime 2, prime-power moduli and 202 forced-zero survival cases.
- 188 labelled size-biased sampling and sorting cases, with equal-mass distinct balls, and 12 four-moment joint inversions pass.

These tests can falsify an algebraic formula or implementation. They do not prove BV, transference, endpoint energy, asymptotics, or novelty. The PASS rests on the source-based argument above. In particular, empirical sign balance is not used in the proof verdict.

## 12. Novelty comparison and corrections for integration

The actual E sign is supported on its active groups. Its proof uses ε(m)=ε(p)=1 for the factors outside those groups, and its discrepancy hypothesis concerns α. Full λ would invalidate that substitution. Its actual final theorem asserts infinitely many squarefree even-parity predecessors. The present proof obtains equal full Liouville densities and positive squarefree densities of each sign, with the entire joint PD law in every fixed progression. Those conclusions do not follow by reading E's final theorem or R006's marginal PD law.

The ordinary two-point companion assumes bounded multiplicative factors over ordinary integer averages. A prime indicator is not a multiplicative factor. Its qualitative o(X) statement does not yield the prime-normalized cancellation, and its quantitative fixed-form Liouville statement is not the variable-divisor estimate used here. No direct duplicate was identified in the inspected companion interfaces.

[Lichtman's Theorem 1.1, v2](https://arxiv.org/pdf/2009.08969v2), averages over a growing shift range with log H/log log X→∞; Remark 1.7 permits λ as well. This does not isolate shift −1. A fresh search also located [Lichtman–Teräväinen, *On the Hardy–Littlewood–Chowla conjecture on average*, Forum Math. Sigma 10 (2022), Theorem 1.2 and Corollary 1.4](https://doi.org/10.1017/fms.2022.54). They improve the shift range to a fixed logarithmic power but still allow exceptional shifts. Their theorem does not supply fixed-shift LP or parity/PD independence. The primary PDF was inspected through the web tool; direct urllib download returned 403, recorded without claiming retained PDF bytes.

There is an overlapping public [Carella v1 claim](https://arxiv.org/pdf/2206.12956v1), so absence of earlier claims would be false. I inspected its Lemma 8.1 and §10. With Q=Σμ² and S=Σμ, the exact counts are `(Q+S)/2` and `(Q−S)/2`. Lemma 8.1 prints the same plus sign for both; §10 then removes the unresolved signed sum. The corrected identities substituted into S=N_+−N_− give only S=S. Thus that inspected argument does not establish a duplicate. This conclusion concerns v1 only, not every later version or all literature.

The new work here is CT plus the uncentered signed LC energy argument and SPR, followed by signed extraction and dominated probability passage. It goes beyond routine squarefree truncation. The accepted corpus supplies unusually strong analytic contracts; the conclusion must continue to be presented as a deduction under those premises. The bounded search is not worldwide-priority certification.

For integration, retain these explicit clarifications, all supplied in this review without changing the author report:

1. Cite Pintz (1.5) for the summed zero-main-term BVλ formula. Describe Shao p.961 as corroborating the classical result in a different formulation, not as literally the same display.
2. D labels such as `cor:sparse-bound`, `cor:long-prime-saving`, `cor:stripped`, and `cor:bilinear-multiplier` are proof equations, not separately stated corollaries. The general pairing and ideal-family propositions are the operator contracts; the inspected scalar/energy proof equations supply the ensuing estimates.
3. State `m_graph−t_g=J−|C_g|` before the sign formula, and note explicitly that the common `(−1)^{Js}` need not converge.
4. In smoothing BV, keep the compact support away from zero, the strict modulus exponent margin at every cumulative scale, and the sum-inside-integral argument. No maximum-over-endpoints strengthening is used.
5. Keep LC restricted to nonempty long tuples, full-small-interval mixing for progressions, the original ideal kernels and unsigned positive proxies, and the order x→∞, then array count, then sieve depth.
6. Distinguish zero weak signed limit from total-variation convergence to zero; the latter is not asserted and does not follow. Domination by unsigned probability measures supplies the boundary control that is actually needed.

None of these is an unresolved analytic repair or an extra hypothesis. With these precision points preserved, I recommend accepting the full LP and joint consequence as a completed substantial deduction under the stipulated corpus. Parent acceptance, a separate finding commit, and any further novelty review remain the parent's actions.
