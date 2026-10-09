# R008 — Full parity and Poisson–Dirichlet independence for prime predecessors

Date: 2026-10-08. **Validated substantial deduction under the user's accepted corpus.** Immutable premise: `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, together with the accepted [R006 progression law](R006-progression-PD-primitive-root-density.md). The independent analytic audit passes without an unresolved gap. The separate [final novelty/significance review](../reviews/i05-parity-novelty-r3.md) supports a substantial, nonroutine advance beyond R006. The parent accepts that qualified assessment as the second substantial discovery; worldwide priority remains unverified.

The result gives equal even/odd parity densities for the number of prime factors of p−1, counted with multiplicity, independently of its limiting ranked factor sizes and squarefreeness. This is one finding: the Möbius-sign and squarefree consequences share the same new signed estimate.

The [complete proof](../iterations/i05-parity-pd.md), [independent audit](../reviews/i05-parity-pd-r2.md), and [parent verification](../sources/i05_parity_pd_r2/parent-verification.json) are part of this record. The clarifications below govern the source labels, smoothing and limit conventions in the original report, which is preserved as the reviewed artifact.

## 1. Exact theorem

For p≥3 prime, let V(p)=(V₁(p),V₂(p),…) be the decreasing logarithms of the prime factors of p−1, counted with multiplicity, divided by log(p−1), and padded with zeroes. Let L=(L₁,L₂,…) have PD(1). Write λ(n)=(−1)^Ω(n) and B(n)=μ²(n).

For every fixed positive integer M, every reduced class b modulo M, every fixed k≥1, and every continuous complex H on [0,1]^k,

\[
 \frac{1}{\pi(X;M,b)}
 \sum_{\substack{3\le p\le X\\p\equiv b\pmod M}}
 \lambda(p-1)H(V_1(p),\ldots,V_k(p))\longrightarrow0.
 \tag{LP}
\]

The same statement holds on each terminal dyad (x,2x], normalized by its class-prime count, as real x tends to infinity. All parameters and tests are fixed before the limit.

For each prime q let e=v_q(M) and set

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
\]

The prime 2 is included. If p is uniform over the class primes in either sampling convention, then

\[
 (V_1(p),\ldots,V_k(p),\lambda(p-1),B(p-1))
 \Rightarrow (L_1,\ldots,L_k,S,B),
\]

where S is a fair sign, B is Bernoulli(C_{M,b}), and the three components are mutually independent. Consequently

\[
 \mathbb E[\mu(p-1)H(V(p))]\to0,\qquad
 \mathbb E[\mathbf1_{\mu(p-1)=s}H(V(p))]
 \to\frac{C_{M,b}}2\mathbb EH(L),\quad s=\pm1.
\]

Here H(V) abbreviates the same finite-coordinate test. For M=1, each Möbius sign has prime-relative density one half of ∏q(1−1/[q(q−1)]), approximately 0.1869779. Each Liouville sign has density 1/2. Conditioning on a sign retains PD(1); squarefree or Möbius-sign conditioning requires C_{M,b}>0. When a square is forced by the class, C_{M,b}=0, and the squarefree component is identically zero; LP still holds.

No rate, effective threshold, growing-modulus uniformity, other-shift theorem, or arbitrary multiplicative-weight extension is asserted. The accepted corpus is a premise, not an externally established conclusion of this project.

## 2. Exact inputs and the additional argument

The [author manifest](../sources/i05_parity_pd/manifest.json) and [independent source ranges](../sources/i05_parity_pd_r2/source-ranges.json) record immutable URLs, hashes and inspected lines. Prefixes below designate directories under `preprints/` at the pin:

| Prefix | Directory |
|---|---|
| D | `The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/` |
| S | `Weighted-Dilation-Graphs-Smooth-Shifted-Primes-and-Totient-Fibers-September-24-2026/build/` |
| P | `Primitive-roots-for-every-admissible-integer-base-October-4-2026/build/` |
| T | `Simultaneous-primitive-roots-a-conditional-lower-bound-for-prime-bases-October-4-2026/build/` |
| E | `Prime-Predecessors-with-an-Even-Number-of-Prime-Factors-September-17-2026/build/` |

The decisive accepted interfaces are D §§3–5 and P §8 (`lem:marked-coefficient-transfer`) for the scalar determinant square; S §2 (`cor:transference-pairing`) and D §6 (`prop:graph-transfer`, `prop:ideal-family`) for physical vectors and the original ideal kernels; D §6's divisor model, local Mellin and sparse-energy proof; D §9's long-prime and unweighted log-phase lemmas; and D §§7–8's positive extraction and probability arguments. T's fixed-character/lcm device and R006 supply progression handling. Labels such as `cor:sparse-bound`, `cor:long-prime-saving`, `cor:stripped` and `cor:bilinear-multiplier` are proof equations, not separately stated corollaries.

Classically, [Pintz (1.5), page 2](https://arxiv.org/pdf/1004.1067v1) supplies, for every fixed θ<1/2 and A>0,

\[
 \sum_{q\le R^\theta}\max_{(a,q)=1}
 \left|\sum_{\substack{n\le R\\n\equiv a\pmod q}}\lambda(n)\right|
 \ll_{\theta,A} R(\log R)^{-A}.
 \tag{BVλ}
\]

This concerns ordinary integers. [Shao, page 961](https://msp.org/ant/2017/11-4/ant-v11-n4-p06-p.pdf), corroborates the classical result in an exceptional-modulus, centered-mean formulation; it is not a second verbatim statement of this formula. Smooth weights have fixed compact support away from zero. Put the modulus sum inside the partial-summation integral, and preserve a strict exponent margin at every comparable cumulative scale. This does not assume a sum of maxima over endpoints. For a nonunit residue a modulo k, write g=gcd(a,k), n=gv and use λ(gv)=λ(g)λ(v), with no coprimality requirement between g and v. BVλ then gives arbitrary logarithmic saving at positive-power scales for fixed-logarithmic moduli and Mellin twists.

E's sign is restricted to active prime bands and its proof uses sign +1 on factors outside them. Its conclusion is infinitude of squarefree even-parity predecessors. Full λ cannot be substituted into that theorem. The following signed correlation and extraction are the additional work.

## 3. Signed determinant and correlation estimates

**CT.** In the selected-prime determinant reduction, a contains exactly K inert-band primes and mn−1=ah. If F₀ is the original bounded invariant factor, then

\[
 \lambda(mn-1)F_0(mn-1)=(-1)^K\lambda(h)F_0(h).
\]

The remaining factor has modulus at most one and lies outside the Cauchy square. The expanded nonnegative square is literally D `det:cauchy-square`, also P `eq:type-ii-cauchy-square`, with the original α and β. Thus their accepted scalar bounds apply. The damping's selected-prime-square error remains absolute. Fixed progression characters multiply α and β and combine with tested characters modulo lcm(M,k), within the same fixed-logarithmic range. No Liouville twist of a coefficient discrepancy is assumed.

**LC.** Use the exact data and uniformity in [complete proof §5](../iterations/i05-parity-pd.md#5-second-bridge-an-uncentered-signed-correlation): d≥1 long slots with primes at least x^ε and upper-endpoint product at most x^{1−ε}; the specified inert marking weight 𝒲; disjoint active small groups at exp((log x)^.27) through exp((log x)^.36) and big groups at exponents .39 through .46; the source number/mass/damping bounds; full big intervals and at least one full small interval; and the original invariant second core G(n_*) with its fixed divisor-power bound. Let f_x be the uncentered long-tuple divisor count. For every fixed M, residue r including nonunits, fixed smooth compactly supported Ψ on (0,∞), and A>0,

\[
 \sum_{w\equiv r\pmod M}\frac{\Psi(w/x)}w
 \lambda(w)\mathcal W(w)f_x(w)G(w+1)W_1(w)W_1(w+1)
 \ll_{A,M,\mathrm{fixed\ data}}(\log x)^{-A}.
\]

Insert λ and the two endpoint residues in the physical vectors, keeping the original ideal kernels. The first vector remains independent of marks at each fixed position, and its norm bound is unchanged. In a comparison pattern, graph list length J+1 and unshared count 1+|C_g| give J−|C_g| shared primes in group g. Hence the shared product D_R has Ω(D_R)=Js−c_ν, where c_ν=Σg|C_g|. The sign is

\[
 \lambda(D_Rw)=(-1)^{Js}(-1)^{c_\nu}\lambda(w).
\]

The common factor may vary with x and need not converge. Divide it out. Reassemble all physical dyads and the full Mellin integral before averaging shared labels. Then the measure becomes D_R^{-1}Ψ(w/(xD_C))/w, with no shared-label dependence left in its cutoff. One full small interval gives uniform unit-residue mixing; the new sign is constant over those labels. The raw pattern plus its signed comparisons is controlled by the unchanged graph pairing.

Each comparison still needs a separate energy bound. Fixed residue Fourier shifts only enlarge the logarithmic denominator exponent. At low Mellin frequencies, the divisor model and BVλ give arbitrary saving in the uncentered tuple term. At high frequencies retain one long prime and one small marked prime: λ(p_s p_l u)=λ(u). The residual coefficient retains its divisor bound and square norm. The sparse Gram kernel is the original unweighted sum Σn n^{i(t_i−t_j)}; λ changes the tested coefficient vector, not this kernel. The small-prime factor handles ordinary times and the accepted long-prime saving handles the sparse exceptional intervals. All scales and frequencies remain in D §9's ranges. This proves LC after subtracting the comparison terms. There is no signed constant term and no d=0 analytic claim.

## 4. Progression remainders and prime extraction

The signed progression remainder SPR is proved before presieving. Expand the inert marked weight using the represented-union divisor model. Bound the positive first-omitted Bonferroni envelope by unsigned CRT counts, summing its rounding errors to x^{1−ε+c₀+o(1)} with c₀<ε/8. This avoids multiplying an L² error by a power-sized number of moduli.

For retained long-tuple product ℓ and divisor d′, put u=ℓd′v. Conditions r|u+1 and u+1≡b mod M are incompatible if (r,M)>1 or (r,ℓd′)>1. Otherwise v is in one class modulo rM whose gcd is g=gcd(b−1,M). Write v=gt and apply BVλ at scale R/g=x/(ℓd′g) to the distinct moduli rM/g. Their sizes are strictly below (R/g)^{1/3}. Reciprocal coefficient masses are bounded, giving the required summed arbitrary-logarithmic remainder.

Apply the positive block sieve separately to weights Φ𝒲f_x(1±λ)/2 in the class. Each has half the unsigned model; subtraction removes the main term. The normalized error is O(e^{-h}/γ), uniformly in the later marking arrays, with γ=c₀/(4h+3).

The prime-minus-rough proxies stay unsigned and positive. CT removes the relevant composite discrepancy. Threshold, square and smooth-cutoff errors are absolute. Failed coin outcomes are discarded while the weights form a nonnegative partition, before the later signed expansion costs. Allocation of active primes keeps u+1 fixed, so λ(u) and the class condition stay outside the exact allocation identity. Each surviving active set has a full small interval and satisfies LC. Apply it with r=b−1 and Ψ(t)=tΦ(t) to eliminate composites.

Unsigned nonnegative deweighting bounds suffice because |λ|=1. The final limsup is bounded by

\[
 C_{M,d,\varepsilon,\Phi}e^{-h}/\gamma
 +C_{d,\varepsilon,\Phi}\sqrt{C_K/B}.
\]

Choose h, then sufficient fixed K and any finite B disjoint arrays; take x→∞, then B→∞, then h→∞, choosing a new sufficient fixed K at each depth. This yields the signed interior factorial statistics. Nothing grows inside an application requiring fixed parameters.

## 5. Probability passage and squarefree consequence

The signed factorial measure, obtained by attaching λ(p−1) to each sample, is dominated in total variation by the unsigned measure. Interior cancellation passes to signed size-biased laws by multiplying by ∏i t_i/(1−Σj<i t_j). The unsigned size-biased law from the full R006 proof has limiting mass one in the open simplex. Compact cutoffs and domination therefore give weak convergence of the signed law to zero on the entire cube. This is **weak** convergence, not convergence to zero in total variation.

At d=1 its total mass is exactly Eλ(p−1), proving full parity cancellation without a d=0 correlation estimate. Sorting d draws approximates every fixed ranked coordinate within the unseen mass. Its unsigned expectation tends to 2^{-d}; domination controls the signed approximation error. Take x→∞ at fixed d, then d→∞, to obtain LP. Finite dyadic decomposition and a negligible initial prime proportion give the cumulative version.

Excluding q²|p−1 for finitely many q is a finite union of fixed reduced classes. Apply R006 and LP separately to every such class. Reduced-lift counts give exactly ρ_q above. Brun–Titchmarsh bounds the remaining q≤x^{1/4} tail by O_M(1/Y) after prime normalization; counting integers handles q>x^{1/4} with o(x/log x) error. Let x→∞ and then Y→∞. The four resulting moments are EH, EλH, EBH and EλBH, with limits EH(L), 0, C_{M,b}EH(L), 0. The identities B(1+sλ)/2 and (1−B)(1+sλ)/2 give all four joint atoms, proving mutual independence. Finally μ=λB.

## 6. Validation and contribution status

The independent audit passes CT, LC, SPR, extraction, probability and squarefree consequences. The parent read the full review, checked the decisive source interfaces, reproduced both experiment suites, and retained the six integration clarifications in this record. The reviewer output adds 458 determinant rows with overlap, 2,336 pattern-sign cases, 416,000 nonunit reductions, 93,888 sieve CRT cases, 9,830 local square-density cases, 188 size-biased cases and 12 joint-moment inversions, all without failures. Author output reproduces byte-for-byte.

All 60 cached pinned sources, 14 independently downloaded interfaces, 38 reviewer artifacts, 25 source-range hashes and five re-downloaded primary PDFs pass parent integrity checks. Only the shared iteration index changed among reviewer inputs. These checks test finite identities and integrity; the asymptotic proof rests on the written source-based argument and independent AI review, not numerical balance, human peer review or formal proof-assistant certification.

The proof reviewer judges the signed analytic extension substantial beyond the source infinitude theorem and R006's unsigned law. The final review separately checks that assessment against stronger corpus interfaces and current primary literature; its conclusions and version corrections are incorporated below.

## 7. Final significance assessment and a named conjecture consequence

The [final review](../reviews/i05-parity-novelty-r3.md) inspected the complete path inventory and relevant catalogue entries, then retrieved 36 pertinent pinned files. In particular, the ordinary two-point companion's quantitative theorem controls two Liouville factors at fixed affine forms with one fixed logarithmic exponent; its general multiplicative-function theorem has only qualitative integer-average cancellation. Their stronger lower-level interfaces do not directly yield the present signed prime statistic. A prime indicator or von Mangoldt weight does not satisfy those multiplicative-input hypotheses. The reviewed D/E/S interfaces likewise require the additional signed comparison and extraction argument documented above.

Primary comparisons include Lichtman's shift-averaged theorem, the published Lichtman–Teräväinen logarithmic-shift-range improvement, Tao–Teräväinen's hybrid theorem under a Siegel-zero assumption and restricted scales, and Wang's September 2026 dynamical theorem still averaging over shifts. None of those inspected statements directly supplies LP. The substantive advance is the coordinated signed interior estimate at prime normalization; the squarefree product and probability inversion remain routine consequences.

**Updated overlapping-claim comparison.** The latest version listed in [Carella's arXiv history](https://arxiv.org/abs/2206.12956) at inspection is v3, dated 25 July 2022. Its actual [Theorems 1.1–1.2, page 4](https://arxiv.org/pdf/2206.12956v3), explicitly assume Hypothesis 2.1, a distribution hypothesis for signs on shifted primes (page 6). This differs from ordinary-integer BVλ and is not supplied by the cited classical input. The original v1 criticism is retained as historical evidence, not used as a substitute for this current-version comparison. Earlier overlapping claims exist; no worldwide-first claim is made.

**Moree–Hommersom Conjecture 1 follows under the same premises.** Their [primary manuscript, pages 20–21](https://arxiv.org/pdf/math/0307352v1), defines μ_S(n) to ignore primes in a fixed finite S and to vanish if n has a square factor outside S. For fixed nonnegative valuations e_q at q∈S, R008 implies

\[
 \sum_{\substack{p\le X\\v_q(p-1)=e_q\ (q\in S)}}\mu_S(p-1)
 =o(\pi(X)).
\]

Indeed let B_S indicate squarefreeness outside S. On the valuation event,

\[
 \mu_S(p-1)=(-1)^{\sum_{q\in S}e_q}\lambda(p-1)B_S(p-1).
\]

At each fixed Y, the valuation event and square exclusions for q≤Y outside S specify finitely many reduced classes modulo lcm(∏q∈S q^{e_q+1}, ∏q≤Y,q∉S q²), apart from finitely many primes. Apply LP with H=1 in each class. The unsigned square tail is O(1/Y) in normalized limsup; let X→∞ and then Y→∞. This handles e_q≥2 because square exclusions are only outside S. It is one consequence of R008, not another counted finding.

[MathDB 377990](https://mathdb.com/p/377990/parity-conjecture-for-the-mobius-function-on-shifted-primes) records precisely this conjecture and its primary attribution. The parent checked the formulation and found no posted solution or refreshed progress summary on the inspected page. This is named-problem relevance, not MathDB endorsement, proof certification or a numerical importance ranking.

The parent read the full final review, checked the actual Carella v3 hypotheses and Moree–Hommersom definition/conjecture, and verified all 52 downloaded files, including 36 pinned sources, 34 source-range hashes and 25 page extracts. The [verification record](../sources/i05_parity_novelty_r3/parent-verification.json) separates identity checks from correctness and priority. No new proof-critical issue was found. The inventory screen was not a line-by-line audit of every corpus manuscript.

**Parent decision:** accept LP and its joint consequences as the second substantial, plausible new deduction under the stipulated corpus and bounded prior-art assessment. The exact Moree–Hommersom implication strengthens its demonstrated significance. Worldwide priority, independent truth of the corpus, external human peer review and formal proof certification are not established. No publication or priority registration has been attempted.
