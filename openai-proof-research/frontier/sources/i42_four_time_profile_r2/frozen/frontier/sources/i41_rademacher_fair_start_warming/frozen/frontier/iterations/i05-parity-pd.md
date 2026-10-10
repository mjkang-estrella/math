# Iteration 05: full Liouville parity and Poisson–Dirichlet independence

Date: 2026-10-08. Immutable premise: `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

**Author verdict: a completed candidate proof under the accepted corpus, requiring fresh independent review before acceptance.** This report claims a new full-Liouville signed interior estimate, and derives cancellation, equal parity densities, and joint independence from it. No new parity-distribution hypothesis is imposed. The claim is substantially stronger than the E final infinitude theorem and the routine squarefree-conditioning baseline. It is not a claim of established unconditional mathematics independently of the stipulated corpus or of worldwide priority.

The initially suggested common-sign shortcut does not work as stated: E's sign is supported only on the active prime bands. The successful candidate route is different: put **full Liouville on the first physical endpoint only**. Its sign on the shared product is determined by the number of shared labels, and can be tracked separately in every comparison pattern. Use an **uncentered nonempty long-prime tuple**, whose low-frequency mean is small by classical Liouville distribution in progressions. This avoids the unproved full-Liouville version of D's constant-term high-frequency estimate.

Read: AGENTS.md, the pin, the relevant catalogue entries and complete preprint tree, the complete iteration index, R006 with its complete proof and independent audit, and the source interfaces below. The parent's in-flight qualification of E is incorporated. The parent squarefree baseline was read and is credited in §9. No agents, staging, commits, accepted-finding edits, or shared-index changes were made. All writes are in this report and `frontier/{sources,experiments}/i05_parity_pd/`.

## 1. Exact candidate theorem

For a prime p≥3 let V(p)=(V₁(p),V₂(p),…) be the decreasing sequence of logarithms of prime factors of p−1, counted with multiplicity and divided by log(p−1), with zero padding. Let L=(L₁,L₂,…) have PD(1). Write λ(n)=(−1)^Ω(n) and B(n)=μ²(n).

**Theorem LP.** Assume the pinned corpus contracts identified in §2 and the accepted R006 progression law. For every fixed positive integer M, every reduced class b modulo M, every fixed k≥1, and every bounded continuous complex H on [0,1]^k,

\[
 \frac{1}{\pi(X;M,b)}
 \sum_{\substack{3\le p\le X\\p\equiv b\ (M)}}
 \lambda(p-1)H(V_1(p),\ldots,V_k(p))\longrightarrow0.
 \tag{LP}
\]

The same holds in (x,2x], normalized by its class-prime count. All limits are through real endpoints; all displayed parameters are fixed before the limit. In particular each Liouville sign has relative density 1/2 in every fixed reduced progression, and conditioning on either sign retains PD(1).

For a prime q and e=v_q(M), define

\[
 \rho_q(M,b)=
 \begin{cases}
 1/[q(q-1)],&e=0,\\
 1/q,&e=1,\ b\equiv1\pmod q,\\
 0,&e=1,\ b\not\equiv1\pmod q,\\
 1,&e\ge2,\ b\equiv1\pmod{q^2},\\
 0,&e\ge2,\ b\not\equiv1\pmod{q^2},
 \end{cases}
 \qquad C_{M,b}=\prod_q(1-\rho_q(M,b)).
 \tag{local}
\]

The product is positive exactly when no prime square dividing M is forced to divide b−1. The prime 2 is included.

**Joint consequence.** With p uniform among the primes in the class up to X (or in a terminal dyad),

\[
 (V_1(p),\ldots,V_k(p),\lambda(p-1),\mu^2(p-1))
 \ \Longrightarrow\ (L_1,\ldots,L_k,S,B),
 \tag{joint}
\]

where S is uniform on {−1,+1}, B is Bernoulli(C_{M,b}), and the partition, S, and B are mutually independent. This includes the degenerate B=0 case. In particular,

\[
 \frac1{\pi(X;M,b)}\sum_{\substack{p\le X\\p\equiv b\ (M)}}
       \mu(p-1)H(V(p))\to0,
 \qquad
 \frac1{\pi(X;M,b)}\sum_{\substack{p\le X\\p\equiv b\ (M)\\\mu(p-1)=\pm1}}
       H(V(p))\to\frac{C_{M,b}}2\,\mathbb EH(L).
 \tag{Mobius}
\]

The harmless p=2 term is omitted whenever V(p) would be undefined. For M=1 the squarefree density is the classical product ∏q(1−1/[q(q−1)]), approximately 0.3739558; each Möbius sign therefore has density approximately 0.1869779. No growing-modulus uniformity, convergence rate, effective threshold, or assertions about other fixed shifts are claimed.

## 2. Contracts, companions, and the early prior-art screen

The manifest `../sources/i05_parity_pd/manifest.json` records paths, immutable raw URLs, SHA-256 and Git-blob hashes, compared with the **complete** `sources/preprints-tree.json` (`truncated=false`). Prefixes mean the following directories below `preprints/` at the pin:

- D: `The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/`.
- S: `Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/build/`.
- E: `Prime-Predecessors-with-an-Even-Number-of-Prime-Factors-September-17-2026/build/`.
- P: `Primitive-roots-for-every-admissible-integer-base-October-4-2026/build/`.
- T: `Simultaneous-primitive-roots-a-conditional-lower-bound-for-prime-bases-October-4-2026/build/`.

Decisive actual statements and proof interfaces:

1. D `03-determinant.tex`, `thm:type-II`, `det:cauchy-square`; D `04-memory.tex`, `prop:minor-moment`; D `05-major-arcs.tex`, `prop:major-term`, `maj:long-coefficient`. The initial invariance is used to remove F from a Cauchy square; the remaining square is a scalar expression in α,β and label products.
2. P `08-type-ii.tex`, `lem:marked-coefficient-transfer`, including its proof and `eq:type-ii-cauchy-square`. This gives the same square estimate for coefficients with the required character/Mellin cancellation. T's fixed-character/lcm maneuver and R006 §4 supply fixed progression restrictions without changing the predecessor factor.
3. D `06-correlations.tex`, `prop:graph-transfer`, `prop:ideal-family`, `cor:stripping-normalization`, `cor:stripped`, `cor:shared-collision`, `cor:bilinear-multiplier`, `lem:local-mellin`, `lem:divisor-model`, `cor:sparse-bound`, `cor:long-prime-saving`. Its final `thm:two-sided` is centered and unsigned; we do **not** invoke it for a signed endpoint. §5 below proves the needed replacement from the lower-level contracts.
4. S `02-transference.tex`, `cor:transference-pairing`: the first vector is independent of its mark list **at a fixed position**. Position dependence is allowed. The second vector has a norm condition. Multiplication by λ(position) is therefore permitted; no statement about mark-conditional randomness of λ is needed.
5. D `02-preliminaries.tex`, `lem:prime-estimates`, `lem:moment-bounds`, `lem:block-sieve`, and `09-long-prime-appendix.tex`, `lp:prime-polynomial`, `lp:log-phase`. D's sparse Gram bound uses the unweighted log-phase lemma for the Gram kernel, and is coefficient-independent.
6. D `07-extraction.tex`, `lem:progressions`, `ext:proxy-replacement`, `ext:stripped-coefficient`, `ext:success-probability` through `ext:success-chebyshev`, `ext:allocation-core`, `ext:allocation-identity`, `ext:prime-deweight-square`. The relevant discarded errors are absolute before the signed expansion.
7. D `08-poisson-dirichlet.tex` and R006 full proof §6 establish unsigned size-biased tightness, not just the marginal ranked law. §8 below uses that positive law to dominate a separately proved signed measure.

E's actual `sh:sign` offers only 1 or ε_P(n)=(−1)^{Σ_{q∈P}v_q(n)}. The sentence following `sh:small-square-error` uses ε_P(m)=ε_P(long prime)=1 when passing to `sh:four-factors`; `sh:discrepancy` controls α, not λα. E's `sh:core` is a specified invariant convolution with a prime slot. Its main theorem gives infinitely many squarefree predecessors of even parity, via a thin constructed weight with an even number of ordinary prime slots. Neither its final theorem nor its common-sign correlation states (LP). The proof here does not extend `sh:correlation` by substitution.

The full-tree/catalogue screen located D/E/S and the ordinary two-point correlation companion. The latter's introduction (`thm:q-affine`, `thm:elliott`, `cor:affine`) concerns averages over integers of bounded multiplicative factors. A prime indicator is not multiplicative, and its qualitative o(X) theorem does not supply o(X/log X) after restricting to primes. Its quantitative fixed affine estimate is not an estimate for the marked variable-modulus sums needed here. No reliance on such a restriction is made. P/T concern primitive-root families, not this joint parity law. This is a focused companion screen, not a line-by-line audit of all 719 manuscripts.

**Prior art was checked before choosing the single-endpoint result.** Lichtman's [*Averages of the Möbius function on shifted primes*, arXiv:2009.08969v2](https://arxiv.org/pdf/2009.08969v2), Theorem 1.1, is averaged over shifts, with log H/log log X→∞; its published version is QJM 73 (2022), 729–757. It does not isolate the shift −1. Pintz's [arXiv:1004.1067v1](https://arxiv.org/pdf/1004.1067v1), p.2, distinguishes ordinary-integer Liouville distribution from shifted-prime parity. These comparisons establish that the target is stronger than the inspected classical estimates, not that no other proof exists. A competing public Carella claim was located and is examined in §11; it is not silently omitted.

## 3. Classical input: Liouville in ordinary arithmetic progressions

We use only the following classical, **unshifted-integer** estimate. For every fixed θ<1/2 and A>0,

\[
 \sum_{q\le R^\theta}\max_{(a,q)=1}
 \left|\sum_{n\le R,\ n\equiv a\ (q)}\lambda(n)\right|
 \ll_{\theta,A} R(\log R)^{-A}.
 \tag{BVλ}
\]

It is stated directly in Pintz, arXiv:1004.1067v1, equation (1.5) at θ=1/2−ε, with Vaughan's Möbius estimate credited. Shao, [*Gowers norms of multiplicative functions in progressions on average*, ANT 11 (2017), p.961](https://msp.org/ant/2017/11-4/ant-v11-n4-p06-p.pdf), separately records the classical BV statement for μ and λ. We use the reduced-residue consequence only, even though Pintz's displayed maximum is unrestricted. This is not a shifted-prime conjecture or a new assumption.

Two precise consequences suffice:

(a) Smooth compactly supported dyadic weights can be inserted by partial summation. One may interchange the sum over moduli with the integral of the absolute cumulative-sum bound. All cumulative scales used are comparable with R. No maximum-over-endpoints strengthening is being assumed.

(b) For any fixed ε,C,B,A>0, R between x^ε and x², k≤(log x)^C, any residue a (including a nonunit), and a fixed-support smooth ψ whose derivatives and a phase |t|≤(log x)^B have fixed logarithmic costs,

\[
 R^{-1}\sum_{n\equiv a\ (k)}\lambda(n)\psi(n/R)n^{it}
 \ll (\log x)^{-A}.
 \tag{SWλ}
\]

Indeed put g=gcd(a,k) (g=k if a=0) and n=gv. Then v lies in the reduced class a/g modulo k/g, and λ(n)=λ(g)λ(v) exactly, without requiring gcd(g,v)=1. Apply (BVλ) to this single modulus at scale R/g≥x^{ε/2}, choosing its saving after all logarithmic costs and partial summation. The factor 1/g only improves the normalized bound. Smooth derivative costs from n^{it} are fixed log powers. Constants are uniform in all the displayed ranges. This derivation also handles k=1.

## 4. First bridge: covariance in the one-sided determinant estimate

**Lemma CT.** In D `thm:type-II` or P `lem:marked-coefficient-transfer`, replace the predecessor function F₀(u) by λ(u)F₀(u), where |F₀|≤1 and F₀(qu)=F₀(u) for every inert-band prime q. Retain all the original α,β, rough support, dyadic-scale and coefficient-interface hypotheses. The same conclusion and order of choices hold, including fixed-character twists used by R006.

**Proof.** Expand one chosen divisor prime from each of the K disjoint inert bands. For their product a and mn−1=ah,

\[
 \lambda(mn-1)F_0(mn-1)=(-1)^K\lambda(h)F_0(h).
 \tag{CT-sign}
\]

This is exact, even if a selected prime also divides h: λ is completely multiplicative and a has K prime factors counted with multiplicity. The damping replacement off selected-prime squares has the identical absolute error `det:squareful-error`, since the new multiplier has modulus at most one. On a selected-product dyad, the sum is (−1)^K times

\[
 \sum_h\lambda(h)F_0(h)q^{\omega(h)}
 \sum_{mn-1=ah}c(a)\alpha_m\beta_n.
\]

Cauchy discards the outside factor of modulus ≤1. Its expanded square is **exactly** D `det:cauchy-square`, or P `eq:type-ii-cauchy-square`; no λ occurs in α or β, in the determinant kernel, or in any physical vector of that subsequent determinant argument. Apply the accepted scalar-square bounds. The fixed sign has modulus one; the norm exponents, precision and required K are unchanged. This proves CT.

For the class mn≡b modulo fixed M, use R006's character expansion on mn. The coefficients become αχ₀ and βχ₀, while F₀ stays invariant. Their scalar test characters have modulus at most lcm(M,k), still an arbitrary fixed logarithmic range. P's coefficient criterion therefore applies to the same scalar square. This proves the progression version of CT. In particular this argument never assumes that the coefficient discrepancy survives multiplication by λ(m); that false shortcut is tested in §10.

## 5. Second bridge: an uncentered signed correlation

Retain exactly D's long-slot and group hypotheses: fixed d≥1 and ε>0; ordered distinct prime slots I₁,…,I_d with lower endpoints ≥x^ε and product of upper endpoints ≤x^{1−ε}; the fixed inert array W; active small/big groups in the ranges [.27,.36] and [.39,.46] of logarithmic exponents, each with Θ(log log x) groups and harmonic mass in a fixed positive compact interval; fixed damping q₀∈(0,1); and G(n)=G(n_*) with |G(n)|≤(log x)^C τ(n_*)^C. Big groups are full prime intervals. Require at least one small group to be a full prime interval for the progression assertion, as in R006. Put

\[
 f_x(n)=\sum_{\boldsymbol\ell}\mathbf1_{\ell_1\cdots\ell_d\mid n},
 \qquad F_x^\lambda(n)=\lambda(n)\mathcal W(n)f_x(n).
\]

**Lemma LC.** For every fixed modulus M, every residue r modulo M, every fixed smooth compactly supported Ψ, and every fixed A>0,

\[
 \sum_{w\equiv r\ (M)}\frac{\Psi(w/x)}w
 F_x^\lambda(w)G(w+1)W_1(w)W_1(w+1)
 \ll_{A,M,\mathrm{fixed\ data}}(\log x)^{-A}.
 \tag{LC}
\]

The assertion is uniform over admissible slots, active groups and G with the stated bounds. It is an uncentered **nonempty tuple** theorem. No d=0 or constant-term signed energy is claimed.

### 5.1 Physical vectors and exact stripping

Let s be the number of active groups, and let J be the fixed padding count in D. In a pattern ν put c_ν=Σ_g|C_g|. Its shared product D_R has exactly Js−c_ν prime factors with multiplicity, and its free product D_C has c_ν. Consequently

\[
 \lambda(D_Rw)=(-1)^{Js}(-1)^{c_\nu}\lambda(w)
              =(-1)^{Js}\lambda(D_C)\lambda(w).
 \tag{single-sign}
\]

The prefactor (−1)^Js is common to every pattern for that x. The additional (−1)^cν is constant on the entire pattern, not a function of any sampled label. The identity remains true if auxiliary labels repeat. Collisions affecting the marked-weight stripping, as distinct from this exact sign identity, are discarded by the original absolute errors.

Use D's physical vectors with W f_x instead of the centered W(f_x−C_x), multiply the first by λ(n)1_{n≡r(M)}, and the second by 1_{n′≡r+1(M)}. The first vector is independent of its mark list at fixed n. f_x is bounded on every position range x^{1+o(1)}, since each slot prime is ≥x^ε. The source physical list-norm proof applies verbatim in absolute value, with an exponent independent of J; the second core has the same fixed divisor bound. Thus D/S's general pairing contract controls the **whole signed residual operator with its original kernels**. We have not changed the ideal operator or inferred a norm bound for a newly signed kernel family.

After summing all physical dyads and restoring the full Mellin integral (with the original negligible Schur-bounded tail), set n=D_Rw and n′=D_R(w+D_C). The cutoff and measure become

\[
 D_R^{-1}\Psi(w/(xD_C))/w.
\]

The invariant unsigned core W f_x and G strip as in D; the only new factor is (single-sign). The measure 1/D_R makes shared labels independent harmonic draws after removal of collision restrictions. Since the sign factor is constant in these labels, R006's uniform mixing over a full small interval remains valid. For every unit d modulo M and all w,r,

\[
 \frac1{\varphi(M)}\sum_{t\in(\mathbb Z/M)^\times}
  \mathbf1_{tw=r}\mathbf1_{t(w+d)=r+1}
 =\frac1{\varphi(M)}\mathbf1_{w=rd}.
 \tag{orbit}
\]

Thus transference gives (after dividing by (−1)^Js)

\[
 \frac1{\varphi(M)}\left(R_\lambda+
              \sum_{\nu\ne0}(-1)^{c_\nu}C_{\nu,\lambda}\right)
   =O_A((\log x)^{-A}).
 \tag{residual}
\]

Here Rλ is the left side of (LC); each Cν,λ is the corresponding stripped D comparison with λ(w), the uncentered f_x, and restriction w≡rD_C modulo M. For M=1 no mixing is needed. Errors are bounded absolutely exactly as in R006: bounded signs do not change their divisor-moment costs. In particular no mixing is performed on an individual physical dyad, and no conditional equidistribution after imposing the residue tests is asserted.

It remains to bound the individual comparisons. This is essential: (residual) alone does not isolate Rλ.

### 5.2 Comparison energy: low times

Expand the source comparison kernels into separated bounded tests on the two free products. The extra pattern sign has modulus one. Their bilinear multiplier estimate is unchanged. Split free products into their fixed residues modulo M. The remaining residue restriction on w is fixed; as in R006, additive Fourier expansion changes rational denominators from k to at most Mk. For a first-endpoint sequence U and a residue a, with Fourier convention Û(α)=Σ_w U(w)e(−αw),

Û_a(α)=M⁻¹Σ_{j mod M}e(−ja/M)Û(α−j/M),

so |Û_a(α)|²≤M⁻¹Σ_j|Û(α−j/M)|². A major-arc center h/k shifts to a rational with reduced denominator at most Mk. If k≤L^C, enlarge the energy denominator bound to L^{C+1} and its width from L^C/H′ to L^{C+1}/H′. Its Mellin cutoff increases by a fixed log power. The proof below allows any such fixed exponent; H′≥exp(2L^.39−O(1)) still dominates LP_s times every fixed log power. Residues a need not be units. This makes the use of progression restrictions explicit.

The first comparison endpoint is now

\[
 \mathcal U_\lambda(w)=\psi_1(w/Y)w^{i\sigma}
                  \lambda(w) f_x(w)H_{\rm marks}(w),
 \quad H_{\rm marks}=\mathcal W W_{\mathbf t}^{\mathbf b},
 \tag{Uλ}
\]

where the bounded tuple test b uses only big marks. Y=xH′=x^{1+o(1)}, H=H′/(log x)^C, H′ is a product of two nonempty big free products, and H/(L P_s)→∞ for every small-prime scale P_s. Its global squared norm has the same bound YL^{O(1)} as D.

D's local Mellin lemma reduces the local Fourier energy at h/k to the integrated square of

\[
 Y^{-1}\sum_w\mathcal U_\lambda(w)e(hw/k)w^{it},
       \qquad |t|\le T_0=LY/H=xL^{O(1)}.
 \tag{energy-target}
\]

The Mellin tail and additive error use only coefficient squares and retain arbitrary saving. We prove (energy-target)'s integral is O_A(L^{-A}).

For |t|≤L^B, fix a tuple product ℓ and write w=ℓn. All tuple primes are outside the marked groups. Use D `lem:divisor-model` at scale Y/ℓ:

H_marks(n)=Σ_{d′|n} A_{d′}+E(n), with d′≤exp(O(L^.47)), Σ|A_{d′}|/d′≤L^{C₈}, and Σ_{n∼R}|E(n)|²≪_N R L^{−N} for arbitrary N.

The normalized error after the tuple sum is O(L^{−N}Σ_ℓ1/ℓ), by Cauchy after renaming N. Multiplication by λ does not change this bound. In a model term put n=d′v. Its normalized contribution is

\[
 \frac{A_{d'}\lambda(\ell d')}{\ell d'}
 \left[\frac1R\sum_v\lambda(v)\psi_1(v/R)
       (\ell d'v)^{i(t+\sigma)}e(h\ell d'v/k)\right],
 \quad R=Y/(\ell d')\ge x^{\varepsilon-o(1)}.
\]

Split the additive phase into the k residue classes and apply (SWλ), including nonunits, to each. The factor (ℓd′)^{i(t+σ)} has modulus one. Choose the classical saving after B, k's exponent, derivative bounds and C₈. Sum using Σ_ℓ1/ℓ=O_{d,ε}(1). This proves arbitrary pointwise log saving on the entire low-time interval; choose the saving again to pay its length L^B. There is **no centered main term** here, because the unshifted Liouville sums have zero main term.

### 5.3 Comparison energy: high times

Follow D's tuple-part argument, without its constant-part argument. Remove the single mark from a small group; small-prime square exceptions have squared coefficient mass ≪YL^{O(1)}exp(−L^.27). Allowing repeated numerical long-slot primes costs ≪YL^{O(1)}x^{−ε}. These bounds, and their integrated versions by the ordinary mean-square estimate, are unchanged by λ.

In the remaining tuple part factor w=p_s p_l u, where p_l is the first long-slot prime. Complete multiplicativity gives

\[
 \lambda(w)=\lambda(p_s)\lambda(p_l)\lambda(u)=\lambda(u).
\]

Equivalently, put the two factors −1 into the small and long prime polynomials. The long polynomial is still precisely a prime sum with a character and a log-power twist, up to a constant sign. The residual coefficient is the original `cor:u-coefficient` times λ(u). It has the same divisor-power bound and collapsed squared coefficient norm. Unlike E's discrepancy argument, **there is no α(m) polynomial whose discrepancy is changed**.

After residue separation, dyadic decomposition and Mellin separation, the polynomial is P_s(t)P_l(t)R(t). All Fourier-tail estimates depend on coefficient squares and are unchanged. The residual scale is at least x^{ε−o(1)}. Where |P_s|≤L^{−A_s}, the remaining product has scale Y/P_s≫T₀ and ordinary mean square proves the required bound.

On the exceptional unit intervals J of the small polynomial, D's coefficient-independent factorial estimate gives

\[
 |\mathcal J|\le\exp(O(L^{.36}+L^{.73}\log L))\le\exp(O(L^{.9})).
\]

D `cor:sparse-bound` applies to R with its new λ-coefficients: its proof bounds the Gram entries Σ_{n∼R₀} n^{i(t_i−t_j)}, not a λ-weighted phase sum, and only uses Σ|c_n|²≪L^C/R₀. Therefore

\[
 \sum_{I\in\mathcal J}\sup_{t\in I}|R(t)|^2\ll L^{C'}.
\]

For L^B≤|t|≤2T₀ the accepted long-prime lemma gives |P_l(t)|≪L^{−A_l}, after choosing B above its threshold and the retained twist exponents. Its slot scale lies between x^ε/2 and x^{1−ε}; choose the lemma's fixed τ<ε and η>1−ε. All frequencies are <x². Take A_l after the small-polynomial supremum and all fixed costs. This bounds the exceptional-time integral by L^{−A}. The low-time argument was available for every such final B, so there is no circular parameter choice.

This establishes arbitrary log saving in (energy-target), hence the local Fourier energy. D's unchanged minor-arc multiplier bound, Parseval and the second endpoint's global norm bound then control every Cν,λ. Sum their fixed log-power costs and subtract in (residual), proving LC.

**Crucial limitation avoided:** the analogous high-frequency estimate for a bare λ-weighted constant term is not furnished by D's `cor:constant-high`, which is an unweighted log-phase estimate after the divisor model. We neither use that estimate with λ nor assert a d=0 version of LC. The later probability argument recovers the total parity mean from d≥1.

## 6. Signed progression remainder and presieving

Fix the interior tuple data, fixed M,b with gcd(b,M)=1, and a nonnegative smooth compact cutoff Φ. Choose 0<c₀<ε/8. If H is any of the fixed finite-array weights allowed in D `lem:progressions`, then

\[
 \sum_{r\le x^{c_0}}
 \left|\sum_{\substack{u\ge1\\r\mid u+1\\u+1\equiv b\ (M)}}
        \Phi(u/x)\lambda(u)f_x(u)H(u)\right|
 \ll_A xL^{-A}.
 \tag{SPR}
\]

**Proof.** Use precisely D's represented-union expansion and Bonferroni truncation for H. The retained divisors satisfy d′≤exp(O_K(L^.22)), reciprocal coefficient mass O(1), and the positive discarded envelope has factorially small reciprocal mass. The absolute envelope error is bounded using the unsigned CRT count, as in D/R006, including its total rounding error x^{1−ε+c₀+o(1)}. Thus the signed envelope error saves every log power; an L² error multiplied by x^{c₀} is not being used.

Fix a tuple product ℓ and a retained d′. If gcd(r,M)>1 there is no solution, since b is reduced. If gcd(r,ℓd′)>1 there is no solution either. Otherwise u=ℓd′v gives a single residue a modulo rM; eventually ℓd′ is a unit modulo M. Here R=x/(ℓd′)≥x^{ε−o(1)}. Although a need not be a unit modulo M, gcd(a,rM)=gcd(b−1,M)=g is fixed. Put v=gt and reduce to a unit class modulo rM/g. The sign λ(ℓd′gt) separates exactly. As r varies, these moduli are distinct, bounded by Mx^{c₀}< (R/g)^{1/3} for large x. Apply the smooth version of (BVλ) with θ=1/3. Its bound for the fixed (ℓ,d′) is ≪_A R L^{−A}, allowing constants depending on M. The fixed g only improves the size.

Finally sum over tuple and divisor coefficients using Σ_ℓ1/ℓ=O(1) and Σ|A_{d′}|/d′=O(1). Choose the classical precision after any fixed costs. This proves (SPR). The same reasoning also proves its version without f_x, but that version is not needed for a signed correlation claim.

To presieve at z=x^γ, with γ=c₀/(4h+3) and fixed large even h, use the two **nonnegative** weights

\[
 a_\pm(u)=\Phi(u/x)\mathcal W(u)f_x(u)
                        \frac{1\pm\lambda(u)}2\,
                        \mathbf1_{u+1\equiv b\ (M)}.
\]

D/R006's unsigned progression estimate plus (SPR) gives each exactly half the unsigned model main term, with summed errors saving every log power. Sieve only by primes not dividing M; the local densities are still 1/q. The block-sieve remainders are allowed because z^{4h+2}<x^{c₀}. Subtract the two sieve estimates. Their main terms cancel, leaving

\[
 \limsup_{x\to\infty}\frac L{x m_{\mathcal W}}
 \left|\sum_{\substack{u+1\equiv b\ (M)\\P^-(u+1)>z}}
       \Phi(u/x)\lambda(u)\mathcal W(u)f_x(u)\right|
 \ll_{M,d,\varepsilon,\Phi}\frac{e^{-h}}\gamma.
 \tag{presieveλ}
\]

The surviving constant is independent of K, h, and the individual fixed array, exactly because the two nonnegative model masses are half the original mass. All array-dependent remainder constants vanish in the x-limit. This avoids applying positivity to a signed measure.

## 7. Signed extraction and removal of marks

We prove the new signed interior statistic

\[
 \sum_{p\equiv b\ (M)}\Phi((p-1)/x)\lambda(p-1)f_x(p-1)
       =o(x/L).
 \tag{Iλ}
\]

Subtract composites from (presieveλ) by the following steps.

1. A presieved composite has j prime factors, 2≤j≤2/γ; large-factor square exceptions cost O(x/z) times fixed constants. Both |λ|=1 and the class indicator preserve every absolute error.
2. Telescope its j prime variables to D's **original unsigned positive proxy** a(m)=1_{m>z}1_{P⁻(m)>W}/[V(W)log m]. Apply CT with the normalized clipped f_x as F₀. It is invariant under all inert-band primes. The companion β is rough, with the same divisor-power bound; its truncation, dyadic splitting and logarithmic Fourier separation use the original absolute estimates. Fixed characters impose the product class as in §4. The scalar discrepancy is unchanged α, not λα. Choose K after γ, j, and required precision, independently of the inert exponents.
3. Replace thresholds and logarithms in a(m) by the candidate-free bars exactly as in D `ext:stripped-coefficient`. The error is absolute o(x/L). The multiplier λ(u) is bounded and does not alter it.
4. Use D's positive coin partition and its uniform failed-outcome estimate under the original positive rough tuple mass. Discard failures **before** the signed expansion. Multiplication by λ(u) preserves the o(x/L) error. Expand the retained terms afterward; there are only L^{O(1)} active sets, each with Θ(log L) full small/big intervals. Thus every active set supplies LC's full-small-interval hypothesis.
5. For a fixed active set P and v=u+1, all allocations of its primes among the j factors keep v and u=v−1 fixed. Hence both λ(u) and 1_{v≡b(M)} stay **outside** the allocation sum. The original identity

   j^{ω_P(v)}(q₀/j)^{ω_P(v)−s_P}=j^{s_P}q₀^{ω_P(v)−s_P}

   is unchanged. Its core is exactly D `ext:allocation-core`, G_P(v)=G_P(v_*), with the same L^{C_j}τ(v_*)^{C_j} bound. It contains no parity sign or progression indicator. Candidate-square exceptions can be removed/restored with their exponential absolute saving after the polynomial active-set cost.
6. Each expanded term is a fixed log-power scalar times

\[
 \sum_{u+1\equiv b\ (M)}\Phi(u/x)\lambda(u)\mathcal W(u)f_x(u)
                    W_1(u)W_1(u+1)G_P(u+1).
\]

   Apply LC with r=b−1 and Ψ(t)=tΦ(t), then multiply by x. Choose its arbitrary log accuracy after the fixed expansion costs. Every composite contribution is o(x/L). No prime-endpoint identity λ(p)=−1 is used to change these unsigned proxies.

Consequently (presieveλ) holds with the sum restricted to class primes. Fix a sufficient K and choose B disjoint inert arrays as D does. Its **unsigned nonnegative** square estimate `ext:prime-deweight-square` bounds the class-restricted sum of

Z_B(u)=(B⁻¹Σ_a W_a(u)/m_a−1)²

by O((x/L)C_K/B) in the normalized limsup. The other Cauchy factor for λ(u)f_x(u) is O((x/L)^{1/2}), since |λ|=1 and f_x is bounded. Therefore

\[
 \limsup_{x\to\infty}\frac Lx
 \left|\sum_{p\equiv b\ (M)}\Phi((p-1)/x)\lambda(p-1)f_x(p-1)\right|
 \le C_M e^{-h}/\gamma+C\sqrt{C_K/B}.
\]

Fix the interior and progression data; choose h, then γ and all j; choose K; choose any finite B arrays; take x→∞; then B→∞; finally take h arbitrarily large. Since γ⁻¹=(4h+3)/c₀, the right side tends to zero. This proves (Iλ) through all real x.

## 8. A signed measure argument, not continuity of parity

Let p be uniform over the class primes in a dyad, and let μ_{x,d} be the unsigned factorial measure of d labelled prime-factor balls. Define the signed factorial measure σ_{x,d} by inserting λ(p−1). Its total variation is dominated by μ_{x,d} on every set.

From (Iλ), smooth dyad approximation, fixed-progression PNT, and the same bounded tuple multiplicities as D §8,

\[
 \int\varphi\,d\sigma_{x,d}\to0
 \quad(\varphi\in C_c(\mathcal D_d)),\qquad
 \mathcal D_d=\{t_i>0,\ \sum_i t_i<1\}.
 \tag{signed-interior}
\]

Here are two details needed for signed tests. The normalization change log x→log(p−1) is controlled in **absolute value** by the unsigned factorial mass of thin endpoint strips, whose R006 limit tends to zero with the strip width. Signed monotone sandwiches are not used. Likewise repeated numerical prime corrections have absolute size O(x^{1−a/2})/N_M(x)=o(1) on an interior compact set. A fixed grid and |σ|≤μ give the passage from rectangles to compact continuous tests.

Conditionally on the balls, sample d balls without replacement with probability proportional to remaining mass. The unsigned law ν_{x,d} has, by R006's full proof §6 / D §8, limit with density

h_d(t)=∏_{i=1}^d(1−t₁−⋯−t_{i−1})⁻¹

on D_d, of total mass one. Define ν^λ_{x,d} by inserting the same λ(p−1) into this random sampling experiment. On compact interiors,

\[
 d\nu^\lambda_{x,d}(t)=
 \prod_i\frac{t_i}{1-\sum_{j<i}t_j}\,d\sigma_{x,d}(t),
 \qquad |\nu^\lambda_{x,d}|\le\nu_{x,d}.
\]

Thus compactly supported continuous tests converge to zero by (signed-interior). Given η>0 choose χ∈C_c(D_d), 0≤χ≤1, with ∫χh_d>1−η. Unsigned convergence gives ∫(1−χ)dν_{x,d}<2η eventually. For **every** continuous H on [0,1]^d,

|∫H dν^λ_{x,d}|≤|∫χH dν^λ_{x,d}|+2η||H||∞→at most 2η||H||∞.

Let η→0. Hence ν^λ_{x,d} converges weakly to the **zero signed measure** on the whole cube. Taking d=1 and H=1 already proves the total mean of λ(p−1) tends to zero: the total mass of ν^λ is that mean, even if the finite ball collection is exhausted and padded. This is how the missing d=0 correlation is avoided.

For ranked tests, sort the first d sampled balls and pad zeros. Their ranked coordinates differ from the true V_i by at most the remaining mass R_{x,d}. R006's unsigned size-biased law gives E R_{x,d}→2^{−d}. Multiplication by λ does not increase the test error, so for every η>0 it is at most

ω_H(η)+2||H||∞ E R_{x,d}/η.

For fixed d the sorted test is continuous, and its signed expectation tends to zero by the preceding paragraph. Take x→∞, d→∞, then η→0. This proves the dyadic (LP). A finite dyadic decomposition and fixed-progression PNT prove the cumulative version. At no point is parity treated as a continuous function of normalized factors, or inferred from marginal laws.

## 9. Squarefreeness and Möbius: consequences of the new signed theorem

The unsigned squarefree/PD assertion alone is the **routine parent baseline**, not the new contribution. We reproduce only the deduction needed to combine it with (LP).

For fixed Y let B_Y(n)=1 if q²∤n for every prime q≤Y. In a fixed reduced class modulo M, B_Y(p−1) selects a finite union of reduced classes modulo lcm(M,∏_{q≤Y}q²), apart from finitely many exceptional primes. Apply (LP) in each such class, with its own fixed modulus, to get

\[
 N_M(x)^{-1}\sum_{\substack{x<p\le2x\\p\equiv b(M)}}
       \lambda(p-1)B_Y(p-1)H(V(p))\to0.
\]

Unsigned R006 in the same classes gives limit E H(L)∏_{q≤Y}(1−ρ_q(M,b)). CRT proves these exact local factors, including q|M and q=2. All moduli are fixed before x grows.

The uniform square tail needed to pass Y→∞ is

\[
 \limsup_{x\to\infty}\frac{\#\{x<p\le2x:\exists q>Y, q^2\mid p-1\}}
                            {\pi(2x)-\pi(x)}\ll1/Y.
 \tag{square-tail}
\]

For Y<q≤x^{1/4}, Brun–Titchmarsh bounds each progression by ≪x/[q(q−1)log x]; sum the reciprocal tail. For q>x^{1/4}, count all integers: Σ_{q≤√(2x)}(x/q²+1)=O(x^{3/4}+√x)=o(x/log x). The interval Brun–Titchmarsh inequality used is displayed in Ford's [primary author paper *An explicit sieve bound and small values of σ(φ(m))*](https://www.ford126.web.illinois.edu/wwwpapers/sigphi.pdf), introduction, with Montgomery–Vaughan attribution. Dividing by N_M(x) instead costs only a fixed φ(M) factor. Bounded λ and H preserve the same error.

First take x→∞, then Y→∞. We obtain E[λ B H(V)]→0 and E[B H(V)]→C_{M,b}EH(L). Together with (LP) and unsigned R006, the identities

1_{λ=s,B=1}=B(1+sλ)/2,
1_{λ=s,B=0}=(1−B)(1+sλ)/2

prove all four joint limits, hence (joint). Since μ=λμ², (Mobius) follows. This proves positive-proportion squarefree predecessors of each parity whenever C_{M,b}>0, with the exact relative densities. If C_{M,b}=0 the event is eventually impossible; no false positive-density assertion is made for classes such as p≡1 mod4 or p≡1 mod9.

## 10. Falsifications, safeguards, and independent-review priorities

The exact finite script is `../experiments/i05_parity_pd/check.py`; results are in the adjacent `results.json`. It tests pattern signs (including repeated auxiliary labels), signed two-residue orbit averaging, biased individual physical dyads versus exact reassembly, the unchanged determinant Cauchy square, signed divisor-model algebra and nonunit reduction, the nonnegative parity split for sieving, and the allocation identity with λ(u) outside it. A prime sieve to 10⁶ is an additional local-obstruction and sign-count screen, **not evidence for an asymptotic proof**. Numerical asymptotic estimates are not used anywhere above.

Explicit rejected shortcuts:

- Active P={3,5} and prime endpoint 7: ε_P(7)=+1 but λ(7)=−1. E's prime endpoint cannot be substituted for full Liouville's endpoint sign.
- A completely multiplicative sign with arbitrary prime-dependent values need not be constant on a label-count pattern. The proof specifically uses λ(q)=−1 for every prime q; it does not extend to arbitrary signs.
- For Möbius, D_R=2,w=2,w′=3 gives μ(D_Rw)μ(D_Rw′)=0 but μ(w)μ(w′)=1. We never lift μ directly. It is recovered as λ times a locally approximable squarefree indicator.
- Scalar cancellation is not invariant under a Liouville twist: α₂=1, α₄=−2 gives Σα_m/m=0 and Σλ(m)α_m/m=−1. This is a finite algebraic counterexample to the proposed automatic preservation of discrepancy, not to any accepted theorem's full hypotheses. CT deliberately retains the original α.
- A full sign on only one endpoint cannot be erased without tracking c_ν. Dropping (−1)^cν changes the signed comparison combination. We keep the original ideal operator and track this factor only **after** transference.
- Transference bounds the residual combination, not the raw term separately. The new low/high endpoint proof is indispensable.
- D's centered constant-part high-time argument has no automatic λ analogue. We only use nonempty tuples and recover total signed mass by unsigned probability tightness.
- Signed sums cannot be bounded by subset positivity. Every discarded error is bounded in total variation; presieving uses the two explicitly nonnegative weights a±.
- Marginal PD and marginal parity would not by themselves imply independence. The signed factorial measures prove the joint assertion, with domination controlling the boundary.

**Most vulnerable steps for fresh independent review:**

1. Check CT against the literal scalar-square statements, including the αχ₀ interface and K/band-exponent order. It is the same square, not a presumed extension of a theorem whose printed invariant-F hypothesis fails.
2. Check (single-sign), the pattern-dependent sign, mark independence and reassembly. The ideal family must stay unchanged until after its accepted norm estimate is applied.
3. Check the new low-frequency proof using (BVλ)/(SWλ), particularly residue gcd reduction, uniformity at R≥x^{ε−o(1)}, and summation over divisor coefficients.
4. Check the high-time coefficient-independent sparse Gram bound with the λ-twisted residual. No λ-weighted Gram kernel is being estimated. Verify that a long prime slot remains present, with all scale/frequency inequalities intact.
5. Check the SPR use of BV after a positive error envelope, including rM/g and the fixed positive gap c₀<ε/8. A generic L² error could not just be multiplied by the number of sieve moduli.
6. Check unchanged positive proxy replacement/coin allocation, order of failed-error removal, and the uniform surviving deweighting constant.
7. Check signed size-biased tightness and sorting. Zero interior signed mass requires domination by the **unsigned size-biased** probability law of total limiting mass one; raw factorial mass is not finite near zero.

The author found no unresolved estimate after these checks, but each bridge is new and has not yet received the independent review the parent intends to commission. A counterexample or contract failure at one of these points would invalidate LP; finite tests do not exclude such a failure.

## 11. Final prior-art and significance assessment

Targeted searches were repeated after the proof route was fixed, for shifted-prime Möbius/Liouville cancellation and joint parity/PD laws. The source/search record is `../sources/i05_parity_pd/research-log.json`. Only inspected primary manuscripts support the comparisons; search snippets and secondary status pages are not proofs.

Lichtman v2 / the published QJM theorem averages over a growing shift range. Pintz (1.5) and Shao p.961 provide the ordinary-integer BV input, not prime-predecessor cancellation. Ford–Konyagin–Luca/Bharadwaj–Rodgers, already screened in R006, concern the factorization law and do not make microscopic parity a continuous test. E supplies only infinitude for μ(p−1)=+1, using a restricted band-supported sign and specially constructed even ordinary-slot support. D's final marginal PD and R006's progression PD have no parity term. The candidate's signed interior estimate and its full parity extraction are additional work beyond those statements.

**Overlapping claim, not priority clearance.** Carella's [*Result on the Mobius Function over Shifted Primes*, arXiv:2206.12956v1](https://arxiv.org/pdf/2206.12956v1), Theorem 1.1, claims shifted-prime Möbius cancellation. In its Lemma 8.1 and §10, the sign-count identity is mishandled: if Q=Σμ²(p+a) and S=Σμ(p+a), the exact counts are N_+=(Q+S)/2 and N_−=(Q−S)/2. Substitution in S=N_+−N_− yields S=S, not cancellation. Its displayed common plus sign and subsequent removal of S cannot justify its claimed conclusion. The finite values Q=10,S=4 give N_+=7,N_−=3 and immediately falsify that common-plus formula. This is a precise defect in the inspected v1 proof; it is not a claim about every version, every later repair, or the nonexistence of other valid proofs. The record also preserves inaccessible literature requests rather than counting them as reviewed sources.

The proposed advance is full parity cancellation and joint PD independence in each fixed progression, then exact positive squarefree parity densities. The new analytic content is CT plus LC and SPR, assembled through the signed extraction. It is not just the parent's squarefree baseline, a parameter change, a negative record, or a hypothesis labeled as a theorem. **Recommendation to the parent: commission fresh independent review of §§4–8 before promotion.** No worldwide-first certification, publication, or priority registration is claimed.

## 12. Integrity and reproducibility

The manifest contains 60 pinned manuscript files verified against both SHA-256 and Git-blob entries of the complete tree; seven key interfaces were freshly re-downloaded from immutable URLs. Primary PDF downloads include exact version numbers where available; failed requests and an HTML access page masquerading as a PDF are marked and not used as mathematical evidence. Relevant rendered source pages and extracted text are retained for checking the classical statements. R006 and its proof/audit were not edited.

Run `python3 frontier/experiments/i05_parity_pd/check.py` for finite checks, and `python3 frontier/sources/i05_parity_pd/verify.py` for the recorded file-integrity checks. The latter reports mutable shared-input changes separately; such a change is not a manuscript-integrity failure. Final exact case counts and artifact hashes are recorded in `validation.json` and `artifact-manifest.json` alongside the source manifest. These checks certify finite identities and byte integrity only.
