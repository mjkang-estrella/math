# I83 — Focused Catalan finite irrationality measure continuation

Research report, 2026-10-10. **C81: GAP. No substantial nomination.** This investigation does not prove or refute the existence of constants \(\mu,C>0,b_0\) such that
\[
 |G-a/b|\ge Cb^{-\mu}\quad(a\in\mathbb Z,\ b\in\mathbb Z,\ b\ge b_0),
 \qquad G=\sum_{k\ge0}\frac{(-1)^k}{(2k+1)^2}.
\]
Effectivity is not required. Eight accepted findings remain eight. The results below are technical partials, explicit unsuccessful constructions, and sufficient criteria with their missing hypotheses exposed. An evidence PASS is not a proof of C81.

All pinned statements **and lower proof operations** at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` remain true premises. This report audits their applicability and new deductions, not their truth. External papers are comparison sources, not stipulated axioms. No children, shared-ledger edits, staging, commits, or publication occurred. The only written domains are this report and the assigned I83 source/experiment directories.

## 1. Original I81 audit — before, and separate from, new constructions

**Scoped verdict: PASS ORIGINAL WITHOUT REPAIRS for I81 Theorems A and B, and its conditional finite-exponent criterion.** This is an independent research-agent audit under the pinned operations. It does not confer a substantial-contribution verdict, validate every unrelated screen in I81, or turn an evidence program into analytic proof. The original report, diagnostics, source records, development log, verifier and final parent wrapper were read; the original verifier was reproduced against seal `181eef41b4660773b4a8431177e7e979490f69431bc66b538e2b7986bcb3888e`. Nothing in the original artifact domain was repaired or rewritten.

Here C denotes the pinned `Catalans-constant-is-irrational-September-24-2026/build` directory in the reused corpus. Exact local paths and LF-delimited passage hashes are in `passages.json`; source labels below are literal TeX labels.

### A: varying-rational specialization

Write the filtered matrix as \(M_N(X)=V_N+XU_N\), with rational coefficient matrices, \(n=48N,H=65N\), and \(D_N(X)=\det M_N(X)\). Contact cancellation in C/foundations, `eq:contact`, `eq:rational-decomposition`, `eq:rational-raw-entry`, makes this identity valid as a polynomial in X, not merely after an assumption that G is rational.

* **Uniform two-adic loss.** In the original proof the only fixed-rational dependence is through \(e_1=4X-M_s(0,0)\), \(e_2=-M_s(0,1)\). For \(X=a/b\), both valuations are bounded below by \(-v_2(b)-c\), with c fixed. The expansion through E and B columns uses at most n such losses. Coefficient-vector repetitions, distinct raw column indices, and minimization in `eq:two-adic-quadratic` do not depend on X. Thus the loss is \(-505n^2/4608-O(n\log n)-n v_2(b)\), with uniform O constant. Zero discrepancies delete summands.
* **Bad odd denominator primes.** The coarse entry estimate in C/odd-primes, proof of `prop:finite-lower`, has an absolute constant and a separate \(-v_p(b)\). Good primes above \(2\sqrt H\) retain both denominator layers. At bad primes in that range one pays at most \(n(3C_0+v_p(b))\); their weighted sum is \(O(n\log b)\), since both \(\sum_{p\mid b}\log p\) and \(\sum_pv_p(b)\log p\) are at most \(\log b\). Primes above H cost only the b-part. The omitted small-prime bound is \(O(n\sqrt H\log H)=o(n^2)\), independent of a,b. Weighted PNT for the fixed nonnegative loss function yields exactly
  \[
  \log|D_N(a/b)|\ge -A n^2-o(n^2)-k n\log b,
  \quad A=8609/4608+(505/4608)\log2,
  \]
  whenever the specialized determinant is nonzero. One must not reuse a fixed-G asymptotic error without this accounting; I81 did not do so.
* **Nonvanishing at the rational test point.** C/nonvanishing, `eq:nonvanishing-triangular-unit`, `eq:nonvanishing-raw-bridge` through `eq:nonvanishing-factorization`, uses X only through the term \(4X\sum P_i c_{(i-j)/2}\). For p integral X that term vanishes after multiplication by \(p^2\) and reduction. The three fixed 48 by 48 matrices and their denominators give a fixed exceptional set E. Therefore \(v_pD_p(a/b)=-96p\) for p outside E and p not dividing b. The triangular change has determinant a power of 2; it contributes no new odd exceptional primes.
* **Prime scale.** For X₀=K log(2b), the sum of log p over [X₀,2X₀] outside E is \((1+o(1))X₀\). If all those primes divided b, it would be at most log b. K>2 excludes that possibility eventually. Increasing a single fixed K also absorbs \(kn\log b\) into the positive quadratic gap. No progression uniformity or first-prime-above-b shortcut is involved.
* **Real derivative.** The Chebyshev coefficient norms are at most \(3^{d+1}\); the two binomial filters cost \(2^{2N}\) and \(2^{4N}\). The rational parts of moments are uniformly bounded real numbers by their actual integral values and the bounded c kernels in `eq:rational-decomposition`. Hence affine entry coefficients have size \(\exp(O(N))\). The differentiated permutation expansion has n·n! terms, giving \(\sup_{[-2,2]}|D_N'|\le\exp(O(n^2))\). This is a crude upper bound, not a small-cofactor assertion.

The source real upper exponent is \(B=2.290939875-\tfrac12\log2\), with B>A. At the selected prime scale the real value at G is less than half the rational lower bound. The mean value theorem gives \(\exp(-O((\log(2b))^2))\). Finitely many reduced fractions in [-2,2] are absorbed using the stipulated irrationality; outside this interval distance exceeds one; reduction only strengthens the bound. These steps justify original A with its original existential constants. They do **not** yield any fixed finite exponent.

### B: the actual central row

At r=g=4N, \(D_r=0\), \(P_r=(1-t)^{2N}t^{63N-1}\). The first filtered column is exactly the M integral with \(s^{7N}(1-s)^{4N}\). All differences i−j in I81's double sum are nonnegative. Inserting the arcsine moment formula and doing the finite binomial sums gives
\[
 u_N={4\over\pi}\int_0^1 {t^{52N-1}\big((1-t)^{6N}-(1+t)^{6N}\big)\over\sqrt{1-t^2}}dt<0.
\]
The exponent 52N−1, rather than 56N−1, includes the factor \(t^{-4N}\) from the column difference. Thus no vanishing coefficient is divided out. The endpoint interval [1−1/N,1] gives \(|u_N|\ge2^{-112}64^N/\sqrt N\) for N≥2. The kernel majorant has mass at most 8. This yields the original error bound with
\[
 \eta={7^7 4^4\over16\,11^{11}},\qquad
 |G-r_N|\le2^{115}\sqrt N\,\eta^N,\qquad r_N=-v_N/u_N.
\]
For odd N the paired integrand is positive; for even N the ratio comparison in I81 is strictly negative. Consequently r_N−G has sign \((-1)^{N+1}\), so neighbors are distinct. The recurrence arrays also justify an exponential common denominator (a fully explicit coarse multiplier is supplied in §2 below). This validates the original \(b_N\le\exp(C_2N)\), not an unproved small numerical value of C₂.

### Original conditional criterion

If, additionally, \(b_N\le e^{\tau N}\) eventually with \(0<\tau<\kappa_0=-\log\eta\), choose \(\tau<\kappa'<\kappa_0\). For
\[
 N\ge {\log(2b)+\tau\over\kappa'-\tau}
\]
large enough, both neighboring errors are at most \(1/(2b e^{\tau(N+1)})\). At least one neighbor differs from a/b, and rational spacing gives
\[
 |G-a/b|\ge(2b e^{\tau(N+1)})^{-1}\ge c b^{-\kappa'/(\kappa'-\tau)}.
\]
The ceiling costs a fixed factor. Finite initial scales are harmless. This proves the criterion precisely as a **conditional** statement. Original B has not paid \(\tau<9.982888\ldots\). Its six large denominators do not refute this asymptotic inequality, much less C81. No repair is needed to the original criterion.

## 2. Route 1 — explicit integer lattice extraction, and the missing direction bound

### 2.1 An explicit common denominator

Let \(L_H=\operatorname{lcm}(1,\ldots,H)\). For every affine coefficient of every source filtered entry, the following coarse multiplier suffices:
\[
 \mathcal E_N=2^{H+2}L_H^5,\qquad H=65N.                 \tag{L1}
\]
Here is a direct proof, making the exponential height cost explicit. For an odd prime p put \(\ell=\lfloor\log_p H\rfloor\). Factorial carries bound \(0\le v_p\binom{2j}{j}\le\ell\) for 2j≤H. Thus H* at even indices has valuation in [0,ℓ], H* at odd indices in [−2ℓ,0], and m has valuation at least −2ℓ. The explicit boundary formulas give losses at most 4ℓ for even k⁻, 3ℓ for odd k⁻, and 5ℓ for k⁺. Diagonal reduction adds summands with loss at most 3ℓ, and Z⁰ has loss at most 2ℓ. Summation does not multiply a local loss. At 2, even H* has valuation in [−H,0], odd H* in [0,H], so the displayed formulas give loss at most H+2 floor(log₂H)+1, including the factor 3/2 and the coefficient 4c. The 2-part in (L1) exceeds this. Integer polynomial and column coefficients preserve all these bounds. No prime above H occurs.

Therefore (L1) clears U_N and V_N **coefficientwise**, unlike a denominator bound on det M_N. PNT gives
\(\log\mathcal E_N=(65\log2+325+o(1))N\).
This is deliberately wasteful, but fully paid. For the central pair use the smaller computable number
\(E_N=\operatorname{lcm}(\operatorname{den}u_N,\operatorname{den}v_N)\), which divides \(\mathcal E_N\), and put
\[
 w_N=(A_N,B_N)=(E_Nu_N,E_Nv_N)\in\mathbb Z^2.
\]
From the central integral, \(|u_N|\le4\,64^N\), \(|F_N|\le8\,4^N\), and 0<G<1. Thus
\[
 H_N:=\max(|A_N|,|B_N|)\le12\,64^N\mathcal E_N=e^{(h+o(1))N},
 \quad h=65(5+\log2)+\log64.                         \tag{L2}
\]

### 2.2 A completely explicit construction that really gives small integer forms

**Technical extraction lemma.** For every N≥1 one can compute integers Q_N>0,P_N, and integers z₀,z₁ such that
\[
 (Q_N,P_N)=z_0w_N+z_1w_{N+1},\quad
 0<|Q_NG+P_N|<2^{1-N},                              \tag{L3}
\]
with \(\max(|Q_N|,|P_N|)\le2^{N+1}d_N^2\), where
\[
 d_N=|A_NB_{N+1}-A_{N+1}B_N|>0.
\]
In particular heights are \(\exp(O(N))\), with an actual proved O constant obtainable from (L2). This is not an inference from the smallness of the source determinant.

**Proof and algorithm.** The original alternating approximants imply d_N>0. Form the integer matrix W_N with columns w_N,w_{N+1}. Its adjugate shows \(d_N\mathbb Z^2\subset W_N\mathbb Z^2\), with every combination coefficient explicitly recoverable.

Set M=2^N d_N. Pigeonhole, or the bounded-denominator continued fraction algorithm, produces integers 1≤q≤M,p with \(|qG-p|<2/M\). This is computable without assuming any irrationality measure: use a rational Euler interval for G of width less than \(1/(4M^2)\), take its midpoint, and take its last continued-fraction convergent whose denominator is at most M. If the rational expansion ends first, take its exact value. The next convergent otherwise has denominator >M, so the midpoint linear error is <1/M; interval error adds <1/(4M). Because 0<G<1, choose such p with |p|≤2M. Put \((Q_N,P_N)=d_N(q,-p)\). Irrationality of G makes this linear form nonzero. The displayed bounds follow directly. If Δ=det W_N=±d_N, the actual integer coefficients are
\[
 (z_0,z_1)^T=\operatorname{adj}(W_N)(Q_N,P_N)^T/\Delta,
 \qquad \max|z_i|\le3\max(H_N,H_{N+1})M.
\]
Finally d_N≤2H_NH_{N+1}, proving exponential height growth. This also pays the heights of the rational combination of the original integrals, not only the final pair. ∎

The Euler interval just used has an efficient exact construction. Its jth positive difference is
\[
 d_j={4^j(j!)^2\over(2j+1)!}\sum_{k=0}^j{1\over2k+1}
     =\int_0^1(1-t^2)^j(-\log t)dt\in(0,1].
\]
The integral formula follows by differentiating a beta integral, or elementary integration by parts. Euler's geometric expansion gives
\(G=\sum_{j\ge0}d_j/2^{j+1}\), so truncation at J has error in [0,2⁻ᴶ]. The recurrence for the first prefactor is multiplication by (2j+2)/(2j+3); no floating constant is used in (L3).

**What remains.** If these selected integer pairs satisfied, for some fixed k and all sufficiently large N,
\[
 \operatorname{rank}_{\mathbb Q}\{(Q_j,P_j):N\le j\le N+k\}=2,           \tag{L4}
\]
then C81 would follow. Indeed if \(|Q_j|\le e^{hj}\), \(|Q_jG+P_j|\le e^{-sj}\), choose N so that b e⁻ˢᴺ≤1/2. One pair in the block has \(Q_j a+bP_j\ne0\). Hence
\[
 1\le |Q_j|b|G-a/b|+b|Q_jG+P_j|,
 \qquad |G-a/b|\ge c b^{-1-h/s}.                   \tag{L5}
\]
Constants and ceilings only change c. Neither the rank of the **input** pairs nor the finite output checks prove (L4). An exceptionally good rational approximant can be selected again, with scalar multiples, over arbitrarily long ranges. Pigeonhole constructions of this kind work for every irrational, including Liouville numbers; they cannot themselves imply finite irrationality measure. I81 A only bounds the allowable persistence on a log-squared scale, which does not close (L4). This is a precise selection/noncoincidence gap, not a claim that no other extraction can work.

### 2.3 Adjugates of the actual source matrix

Here the following attempted construction is also literal. Choose a large prime p for which D_p(0)≠0, as proved by the source's rational-specialization operation. Set \(\widehat V=\mathcal E_pV_p\), \(\widehat U=\mathcal E_pU_p\). For any i,
\[
 e_i^T\operatorname{adj}(\widehat V)
       (\widehat V+G\widehat U)e_i
   =\det\widehat V+G\,e_i^T\operatorname{adj}(\widehat V)\widehat Ue_i.   \tag{L6}
\]
This is a nonzero **integer** linear form: its constant coefficient is a nonzero integer, and irrationality handles a nonzero G coefficient. If the entries of the two integer matrices have size at most H, its two coefficients have size at most n!Hⁿ. With n=48p and log H=O(p), this is \(e^{O(p^2)}\), already the wrong height scale for the desired linear-decay argument. The available entry norm bounds only give an equally large upper bound on (L6); they do not make it small.

The source's \(e^{-Bn^2}\) determinant does not bound this adjugate expression. Cofactors of \(M_p(G)\) would instead have coefficients in Q[G], generally of degree n−1; treating them as rational combination coefficients is invalid. Also the source prime nonvanishing is for **rational substitutions**, and does not prove \(D_p(G)\ne0\). No positivity hypothesis for this signed two-sheet matrix has been established here.

There is a useful exact quantitative formulation of what a Brown/Minkowski repair would need. Suppose one constructs rational P_N,Q_N for which
\(A_N=P_NM_N(G)Q_N=V+GU\), U,V integral, A_N invertible. Put d=|det A_N| and K=max(|U_ij|,|V_ij|). Minkowski supplies nonzero c∈Zⁿ with \(\|A_Nc\|_\infty\le2d^{1/n}\). Every output coordinate is an integer linear form; one is nonzero. Its coefficient height is bounded by
\[
 2nK\,\|A_N^{-1}\|_\infty d^{1/n}.                 \tag{L7}
\]
This follows by multiplying the output bound by A_N⁻¹, then bounding row coefficients. Thus an actual sufficient arithmetic/analytic package is
\[
 d^{1/n}\le e^{-sN},\qquad
 2nK\|A_N^{-1}\|_\infty d^{1/n}\le e^{hN},          \tag{L8}
\]
plus a rank-two bounded-block selection like (L4). The determinant clearing cost, actual nonvanishing at G, inverse norm, and output rank are separate obligations. With \(\log|\det P_N\det Q_N|\le a n^2\), the first inequality would follow from a<B; coefficientwise clearing (L1) is far too expensive to give that. The source's sharper determinant valuation is not automatically such a simultaneous coefficient lattice. These missing estimates are not silently replaced by (L1).

This is classical machinery, not claimed novel. Brown's *Mellin transforms, transfinite diameter and rational approximations of integrals*, arXiv:2604.20741v1, §7.1–7.4, actually performs the integer-linear-form extraction with left/right denominator matrices and nonzero determinant. Its §1.5 explicitly leaves numerator bounds for further work. Zudilin 1507.05697v2, Proposition 2 and §2, constructs polynomial forms of increasing degree instead. Neither theorem states C81 or pays (L8) for the pinned signed matrix.

## 3. Route 2 — an independent hypergeometric family with exact arithmetic deficit

This route uses the actual Eskandari 2609.26354v1 construction, not the central source row. Define
\[
 \psi(x,y)={xy(1-x)(1-y)\over1-xy},\qquad
 d\omega={dx\,dy\over\sqrt{x(1-y)}(1-xy)},
 \qquad J_n=\int_{[0,1]^2}\psi^n d\omega=u_nG-v_n.
\]
Its maximum is T=φ⁻⁵, where φ=(1+√5)/2, and its finite measure has total mass 8G. The precise source denominator statements are
\(16^nu_n\in\mathbb Z\), \(16^nL_{2n}^2v_n\in\mathbb Z\).
The terminating sum in equations (2.2)–(2.3) specifies
\[
 u_n=8(-1)^n16^{-n}\binom{2n}{n}^{\!2}
 {}_3F_2(-n,-n,n+\tfrac12;\tfrac12,\tfrac12;1).
\]
Every term of the terminating hypergeometric sum is positive. These are source statements checked in the actual paper, including the argument producing the factor 16 saving; they are not extrapolated from the pinned row's denominators.

Choose any fixed α≥0 and the **even** integer \(m_n=2\lfloor\alpha n/2\rfloor\). The explicit candidate is
\[
 J_{n,m}=\int\psi^n(1-16\psi)^m d\omega
        =\sum_{i=0}^m(-16)^i\binom miJ_{n+i}
        =u_{n,m}G-v_{n,m}.                          \tag{H1}
\]
The source proves
\[
 E_{n,m}=16^nL_{2n+2m}^2,\qquad E_{n,m}u_{n,m}, E_{n,m}v_{n,m}\in\mathbb Z.\tag{H2}
\]
The common coefficient signs in u imply \(\operatorname{sign}u_{n,m}=(-1)^n\). Since m is even, J_{n,m}>0. Therefore the fractions v/u alternate strictly about G, and neighbors are distinct. Independence at the level needed for rational-spacing is paid by signs, without presuming functional independence or linear independence of two numerical periods. The integrals lie in Q+QG by the verified family identity; **there is no extra π² period in this particular family**.

Put R=16φ⁵ and
\[
 U(\alpha)=\log R+\alpha\log(1+R)-\log16,
\quad D(\alpha)=\log16+4(1+\alpha),
\]
\[
 M(\alpha)=\max\left\{
 {1\over16(1+\alpha)}\left({\alpha\over1+\alpha}\right)^\alpha,
 T(16T-1)^\alpha\right\}.                         \tag{H3}
\]
The 0⁰ convention is 1. The paper proves \(n^{-1}\log|u_{n,m_n}|\to U\), \(n^{-1}\log E_{n,m_n}\to D\), and an upper bound by log M for \(n^{-1}\log J_{n,m_n}\). For this **even** sequence the upper bound is actually a limit, as follows directly from positivity:

**Laplace lower bound.** For α>0, choose an interior point with ψ not 0 or 1/16 and whose value \(\psi|1-16\psi|^\alpha\) is arbitrarily close to M. Such a point exists because the image of the interior under ψ contains (0,T], the interior critical maximum realizes T, and neither maximizer in (H3) is a zero. On a sufficiently small positive-measure neighborhood, logs are bounded and m_n/n→α uniformly in the expression for the exponent. Integrating over this neighborhood bounds the liminf below by log M minus an arbitrary error. The elementary sup bound gives the matching limsup. For α=0 take m_n=0 and a neighborhood of a maximizer of ψ. Consequently
\[
 \lim {1\over n}\log(E_{n,m_n}J_{n,m_n})
       =D(\alpha)+\log M(\alpha).                 \tag{H4}
\]

This gives a rigorous obstruction to the **specified clearing**, stronger than a finite numerical check. In fact for every α≥0,
\[
 D(\alpha)+\log M(\alpha)
 \ge4(1+\alpha)-\log(1+\alpha)
       +\alpha\log{\alpha\over1+\alpha}
 \ge\log(e^4-1)>0.                               \tag{H5}
\]
For the second inequality differentiate: the derivative is \(4+\log(\alpha/(1+\alpha))\), with unique minimum at \(\alpha=1/(e^4-1)\); substitution gives log(e⁴−1). At zero take the continuous limit. Thus the unreduced integer forms from (H2) **grow**, for every fixed α in this construction. This is not a disproof of C81, nor of a beneficial hidden gcd.

Here is exactly how much gcd improvement would suffice. Set
\[
 g_n=\gcd(Eu_{n,m_n},Ev_{n,m_n}),\quad
 (q_n,p_n)=(Eu/g_n,Ev/g_n),
\]
changing both signs if needed. If, for some γ and all sufficiently large n,
\[
 \log g_n\ge\gamma n,
 \qquad \gamma>D(\alpha)+\log M(\alpha),           \tag{H6}
\]
then the primitive integer forms decay exponentially and their heights grow at most exponentially. Specifically, for arbitrary small ε>0 take
\(s=\gamma-D-\log M-\varepsilon>0\),
\(h=D+U-\gamma+\varepsilon\) (enlarge to any positive upper exponent if necessary).
The sign argument supplies neighboring noncoincidence, so (L5) proves C81 with any exponent larger than \(1+h/s\). Equivalently the reduced-fraction denominator exponent must be strictly below the error-decay exponent \(U-\log M\). At α≈3.31765 the clearing-growth deficit is about 14.93384 per n, the height bound about 39.64883, and the sequence-quality lower bound about 0.623347. None of these is an upper irrationality measure. (H6) is not established, and finite samples cannot settle it.

### 3.1 Overconvergence is accounted for, rather than inferred

For the unmodified family the actual generating function of remainders is
\[
 \mathcal J(z)=\sum_{n\ge0}J_nz^n=\int {d\omega\over1-z\psi}.
\]
It is holomorphic on \(\mathbb C\setminus[\phi^5,\infty)\): on each compact subset, the inverse kernel is uniformly bounded on 0≤ψ≤T and ω is integrable. Thus the original remainder series overconverges beyond the negative dominant singularity of the u-series. For rational α=r/s and a subsequence n=2sk,m=2rk the same argument gives an explicit Stieltjes generating function with kernel
\(1-z\psi^{2s}(1-16\psi)^{2r}\), cut starting at \(M(\alpha)^{-2s}\). Its denominator multipliers grow with exponent \(2sD(\alpha)\) per k. This analytic improvement does not remove that cost.

The actual CDT main paper, arXiv:2408.15403v2 (218 pages), Remark 11.1.17, pp.163–164, compares the classical Catalan hypergeometric family and Zagier case E. It gives the denominator types \(16^nL_{2n}^2\) and \(L_n^2\), respectively, and records failures of the requisite analytic/arithmetic comparison: \(e^4>\phi^5\) and \(e^2>4\). These are statements about those two families and the discussed method, not an impossibility theorem for all Catalan constructions. The modified family (H1) has its own paid calculation (H3)–(H5); no conductor-three result was transferred to it.

## 4. A direct holonomic compatibility check, including the real extra period

To inspect an actually independent conductor-four family, take the ICM footnote's differential operator and its specified rational germs:
\[
 \mathcal L=x(1+16x)^2\partial_x^2+(1+16x)^2\partial_x-4,
\]
\[
 A=\sqrt{1+16x}\,{}_2F_1(\tfrac12,\tfrac12;1;-16x),\qquad
 \mathcal LB=1+16x,\quad B(0)=0,
\]
so B′(0)=1. A has integer coefficients: both factors in its displayed series have integer coefficients. The cited source states \(L_n^2[x^n]B\in\mathbb Z\); this is a denominator contract, not a consequence of mere holonomicity. The exact recurrence is
\[
 n^2b_n+(32(n-1)^2-4)b_{n-1}+256(n-2)^2b_{n-2}
   =[n=1]+16[n=2].                                \tag{Q1}
\]
The analogous homogeneous recurrence has a₀=1,a₁=4. Forty coefficients and their claimed caps were checked exactly. That is a transcription test, not a proof of the infinite cap. Both germs are holonomic; applying two derivatives to \(\mathcal LB=1+16x\) gives a homogeneous rational differential operator for B.

The real compatibility issue can be treated without assuming any independence of numerical constants and without trusting the sign of the printed connection identity. Put w=1+16x and
\[
 C=\sqrt w\,{}_2F_1(\tfrac12,\tfrac12;1;w),\qquad
 D=-{w\over4}{}_3F_2(1,1,1;\tfrac32,\tfrac32;w).
\]
Direct substitution in the differential equations shows \(\mathcal LC=0\), \(\mathcal LD=w\). Consequently on 0<w<1,
\[
 B=D+\alpha A+\beta C                                  \tag{Q2}
\]
for constants α,β. Here A and C are independent solutions, since at w=0 A has a nonzero √w log w term and C has a nonzero √w term without a logarithm. Their independence follows from the Euler integral for the zero-balanced Gauss function, or its elementary Frobenius expansion.

**The second coefficient is nonzero and fixed:** \(\beta=\pi^2/16\). Indeed the nth coefficient of \({}_3F_2(1,1,1;3/2,3/2;w)\) is \((n!)^2/(3/2)_n^2=\pi/(4n)+O(n^{-2})\). Thus D has logarithmic coefficient π/16 at w=1. C has logarithmic coefficient −1/π there, while A and B are regular. Cancellation of that logarithm forces β=π²/16. This argument uses only the defined functions and their local series; the value of α is unnecessary.

**Technical functional-independence lemma.** The functions 1,A,B are linearly independent over C(x).

To prove it, suppose p+qA+rB=0 with rational-function coefficients in C(x). Substitute (Q2). Near w=0, the coefficient of the logarithm forces q+αr=0: rational coefficients have integral Laurent powers, and neither D nor C has a logarithm there. Then p+rD+βrC=0. The first two terms have integral Laurent powers at w=0, while a nonzero rC has half-integral powers and nonzero leading coefficient. Since β≠0, r=0, hence p=q=0. ∎

This pays functional independence for this particular family, rather than deriving it from G's irrationality. But it does **not** pay the overconvergence needed for a G approximation theorem. Even after the A component is cancelled, \(D+\beta C\) retains a square-root branch at w=0. Passing to a quadratic covering may remove that branch but changes the arithmetic germs and analytic map; its denominator cap and conformal size must be recomputed. Applying \(C\partial-C'\) kills C but introduces nonrational, logarithmic coefficients at x=0; applying \(\mathcal L\) kills both homogeneous periods, including the wanted one. Neither is a free rational one-period reduction.

The printed ICM equation (5.10) identifies α with a multiple of G; its two-adic equation (5.11) lacks the π² term. An optional floating check of the **printed real normalization** at x=−1/32 produced a substantial residual, retained in `optional-source-diagnostics.json`. This is not a certified correction of that paper, and no assertion identifying α with G is used in a new proof here. The robust extra-period obstruction and independence lemma above were proved without that identification. The 2002 recurrence companion also has a normalization mismatch between its displayed integral factor and Eskandari's J₀=8G convention; it is retained, not silently mixed into (H1). These external-source diagnostics do not challenge any pinned premise and do not affect the original A/B verdict.

For comparison, CDT main Theorem 2.5.1 actually assumes a Q(x)-independent m-tuple of rational germs with a specified column-monotone denominator array b. Its denominator penalty is
\[
 \tau(b)=m^{-2}\sum_{i=1}^m(2i-1)\sigma_i,
\]
and its meromorphic pullbacks along a common φ must satisfy the stated conformal-size condition. For already holonomic functions the condition is \(|\phi'(0)|>e^{\tau(b)}\); the upper dimension quotient is the Bost–Charles double integral divided by \(\log|\phi'(0)|-\tau(b)\). For the independent 1,A,B germs with caps 0,0,2, one gets τ=10/9. To derive a contradiction one would still need a common admissible φ whose quotient is <3. Independence and this formal τ computation alone supply no such φ, and retaining A keeps its logarithmic singularity. For rational approximations to a connection constant, even a small nonzero logarithmic coefficient fails exact meromorphic extension; a quantitative stability version is a further obligation.

This report read the actual main theorem and its denominator definitions, the functional zero estimate Lemma 3.2.14 and discussion §3.3, the conductor-three construction Proposition 11.1.8, the Catalan remark, and §15.3. It does not claim to have read all 218 pages or proved the general holonomy theorem. **No new result above invokes that theorem.** Its §15.3 explicitly leaves the quantitative linear-form transition to substantial additional work. The ICM's more quantitative formulation also requires norm and functional-approximation inputs; the missing conductor-four package is not supplied by its conductor-three example.

## 5. Stronger-companion and discovery-history check

The full pinned domain was reused, not downloaded or duplicated: 13,223 tree entries, 749 manuscript directories, 10,373 blobs, comprising the 9,340-file I14 corpus and I79's 776 PDF text representatives plus 257 other bodies. The original outside PDF bytes and Git bindings remain checked. `corpus-search-definition.json` enumerates the exact 10,373 local representatives and exact regex/flags; JSON match records preserve filename, LF line number and the entire matched text, including PDF formfeeds. The 3,014-record broad multiset is retained. Its `G.function` alternative proved overly broad; separately named filters retain 414 and then 85 records without overwriting the broad search. `history-search-definition.json` covers 183 explicit files and has 147 records. This is finite lexical evidence, not semantic exhaustiveness or a priority certificate.

The original I81 title/history searches and all its failures remain bound. Earlier rotation, quadrature, rational shifts, single-fold normal forms and undecidability reductions are spent. The present task did not reopen them, the excluded prime/Selmer branches, or I80. The current four shared ledgers were snapshotted; only their later drift is informational.

The strongest directly relevant pinned companion is the full Catalan source itself: its two local denominator layers, fixed prime-scale matrices and real energy gap are already lower operations. Its single directory and every file are bound. The complete π companion is also bound and its separated-weight interpolation theorem, determinant translation, final order of choices and already printed series consequences were examined. Its translated centers are logarithmic periods \(2\pi i\), with an exponential/logarithmic analytic identity. No analogous identity for G is supplied by substituting the parameter G. In particular \(\mu(\pi)=2\) does not give a bound for linear forms involving G and π².

The actual content search additionally led to the elliptic-square, quaternionic-division and E×CM Zilber–Pink companions. Their full bodies are bound; the theorem statements and applicable lower interfaces were inspected. Elliptic-square Theorem 2.1 requires exact common analytic equations at selected embeddings, a sum of local proximity, small positive local logarithms, and nonidentity on **every** algebraic branch in its descent. Quaternionic Theorem 3.1 and its ordinary-point zero lemma have the same relevant distinction. A real inequality \(|G-a/b|\ll b^{-\mu}\) is not those exact equations, and no fixed rational algebraic parameter representing its residual was constructed. Their period methods therefore do not automatically upgrade C81. This is an applicability rejection, not an audit of those stipulated results. Other retained hits concern Catalan combinatorics, holonomic D-modules in Langlands, an Euler-product bound for L(2+it,χ), or unrelated g-functions; they are not arithmetic companions for the target.

The current primary comparison is bounded but uses actual text:

* **[Zudilin 1507.05697v2](https://arxiv.org/abs/1507.05697v2)**, Proposition 2 and §§2,5,6: determinant polynomial forms and their denominator obstruction; integer-linear-form heights are not a conclusion.
* **[Eskandari 2609.26354v1](https://arxiv.org/abs/2609.26354v1)**, all construction/asymptotic sections: the exact independent family in §3 above. Its 0.62 result is sequence quality. It cites earlier Viola–Marcovecchio work of similar quality; this report does not claim priority for the family or the idea of polynomial combinations.
* **[Brown 2604.20741v1](https://arxiv.org/abs/2604.20741v1)**, §§1.1–1.5, 3.1,7.1–7.5: genuine small integer forms with left/right clearing matrices; numerator control is left open in the paper. The arXiv record and publisher lead were retained; only the downloaded v1 formulas are used here.
* **[CDT 2408.15403v2](https://arxiv.org/abs/2408.15403v2)**, actual relevant pages specified above, plus the original ICM PDF: functional rank, refined denominator penalties, analytic continuation, conductor-four obstruction, and the nonautomatic quantitative step.
* **[Sun 2609.04176v1](https://arxiv.org/abs/2609.04176v1)**, Theorem 1.1 and §§1,9: a newly located external irrationality claim, whose final displayed comparison is \(S\log q-\delta B^2+o(B^2)\) under a fixed rationality assumption. It does not state an all-denominator finite measure, and its rational-parameter uniformity was not proved here. No result from it is used as a premise or counted as an independent verification of irrationality.
* **[Zudilin math/0201024v3](https://arxiv.org/abs/math/0201024v3)**, recursion and integral normalization checked as a supplementary lead; because the normalization reconciliation was not completed, this paper supplies no proof premise for (H1).

All newly fetched primary bodies, headers, final URLs, times, versions and SHA-256 digests are retained; all ten new HTTP responses succeeded. Inherited primary bindings include the original seven responses and their extraction warnings. No failed retrieval is hidden. The missing optional Python package and the two normalization diagnostics are retained separately. The search does not establish absence of a stronger theorem elsewhere or worldwide novelty.

## 6. Exact remaining bridges, evidence, and verdicts

C81 would follow from any of the following **unproved** packages:

1. For the actual small integer forms (L3), a uniformly bounded block containing two nonparallel output pairs, as in (L4), or another quantitative noncoincidence/size-lower-bound replacement. Input rank alone is insufficient.
2. A source-matrix arithmetic transformation and analytic inverse estimate satisfying (L8), actual nonvanishing at G, and controlled independent output forms. The determinant denominator and a small determinant alone do not provide this.
3. For (H1), a primitive-coefficient saving satisfying the exact inequality (H6), or another explicit one-period family whose paid denominator cost is below its real decay. For the published multiplier of (H1), (H5) rules out decay for every fixed α.
4. A conductor-four real holonomic construction with all rational-germ caps, analytic covering and norm bounds, exact functional independence, the extra real period addressed, and a quantitative approximation theorem. The functional-independence lemma in §4 supplies only one part.

The lattice, explicit coarse denominator, even-power growth obstruction, and local functional-independence argument are technical author proofs. The latter uses only explicit differential equations/local expansions, not a numerical identity for G. No complete substantial theorem is nominated.

`diagnostics.py` reproduces three actual lattice forms using exact rational arithmetic and Euler intervals with 1,297, 2,175 and 3,045 terms. Their Q bit lengths are 1,288, 2,162 and 3,035; lattice indices, integer combinations, error enclosures and coefficient bounds are checked. Neighbors happen to have different directions in these three samples; this is **not** (L4). It independently checks 20 closed Euler difference terms, four central coefficient denominators against (L1), and 40 holonomic coefficient caps. Six floating rate rows illustrate (H3); the proof of (H5), not those samples, establishes the asymptotic obstruction. Optional source diagnostics are explicitly floating and prove no analytic correction.

`verify.py` is offline and read-only. It checks the exact uniquely owned path set, all owned bytes, immutable references, the complete pinned domain and original outside Git hashes through the immutable I81 verifier, search match multisets including formfeeds, exact passage hashes, primary response/PDF replay bindings, version observations, and exact diagnostic output. It compares current shared ledgers with snapshots informationally. It does not fetch, extract to files, write results, modify prior wrappers, or reseal. The single `seal.json` excludes only itself, avoiding self-reference; no mutable result file is excluded. Acquisition scripts are sealed but never called by verification. The seal's digest is delivered separately.

Run from any directory:

```
python3 -B /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/experiments/i83_catalan_finite_measure/verify.py
```

**Original I81 A/B/criterion verdict:** PASS ORIGINAL WITHOUT REPAIRS, scoped as above. **New partials:** technical author proofs, awaiting any parent-requested independent review. **Strong target:** GAP, unproved and unrefuted. **Contribution:** no substantial nomination, no count increment. **Evidence:** provenance/replay only. Parent alone integrates and decides further review.
