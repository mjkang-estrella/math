# A concrete classical reduction of the held Mittag-Leffler claim

Root investigation, 2026-10-29 UTC. **Recommendation for independent review: exclude as a routine classical corollary if this bridge survives.** This is not an assertion that a prior paper explicitly states the conjecture. No credit or acceptance decision is made here. The existing literal Lean certificate is unchanged.

## Exact endpoint

For every (0<\alpha\leq1/2),
\[
 F_\alpha(t)=|E_\alpha(i\sqrt t)|^2
 =E_{2\alpha,1}(-t)^2+tE_{2\alpha,1+\alpha}(-t)^2
\]
is completely monotone on (t>0). This is the full arXiv Conjecture 3 / MathDB 370772 endpoint. The journal conjecture page remains unread. This note addresses the outstanding classical-subsumption objection, not that source-access gap.

## Primary bodies actually obtained and read

1. Papadopoulos, *The half-normal specification for the two-tier stochastic frontier model*, J. Productivity Analysis 43 (2015), 225–230, DOI 10.1007/s11123-014-0389-8. Author-hosted 14-page preprint, April 2014 URL, retained as `sources/papadopoulos-2014.pdf`. Pages 5–6 visually read: equations [2], [3], [4], and the displayed skew-normal/Owen-T identity. Independent normal and unequal half-normal components are explicit. This is **not** the separately titled 2015 report “The double half-normal distribution and its extensions,” whose repository is challenge-blocked and was not read.
2. Patefield–Tandy, *Fast and Accurate Calculation of Owen's T-Function*, JSS 5(5) (2000), publisher PDF, `sources/patefield-tandy-2000.pdf`. Page 1 visually read: equation (1) gives the positive Gaussian integral below and attributes the function to Owen (1956). The original 1956 body has not been read.
3. Mainardi–Pagnini–Gorenflo, *Mellin transform and subordination laws in fractional diffusion processes*, FCAA 6(4) (2003), 441–459; author preprint arXiv:math/0702133. `sources/mainardi-2003.pdf`, printed page 15 visually read: theorem (6.3), proof (6.4)–(6.8), and the exact half-Gaussian specialization (6.9).
4. Mainardi–Mura–Pagnini, *The M-Wright function in time-fractional diffusion processes: a tutorial survey*, arXiv:1004.2950 (2010), DOI 10.1155/2010/104505. `sources/mainardi-2010.pdf`. Printed pages 12 and 16 visually read: the literal Mittag-Leffler series and Laplace pair (4.7), subordination (4.18), half-Gaussian (4.19). The text also proves the moment and transform formulas. The obvious printed sentence “reduces to exp(z) for nu>0” on page 12 is a typo; no part of this argument uses it.

All four predate the 2025 conjecture. The 2013 Pagnini survey reproduces the same subordination in (2.13), but its publisher robot challenge was respected; it is unnecessary because the actual 2003 and 2010 bodies were obtained.

## Published half-normal formula yields a Gaussian mixture

Let (U\sim N(0,\sigma_0^2)), (V=\sigma_1|Z_1|), (W=\sigma_2|Z_2|), independently, all scales positive. Put (s^2=\sigma_0^2+\sigma_1^2+\sigma_2^2), (\theta_j=\sigma_j/\sigma_0), and define the positive quantities
\[
 \omega_1=s\sqrt{1+\theta_2^2}/\theta_1,\quad
 \omega_2=s\sqrt{1+\theta_1^2}/\theta_2,
 \quad\lambda_1=(\theta_2/\theta_1)\sqrt{1+\theta_1^2+\theta_2^2},
 \quad\lambda_2=(\theta_1/\theta_2)\sqrt{1+\theta_1^2+\theta_2^2}.
\]
Papadopoulos [2] says that (D=U+V-W) has density
\[
 f_D(x)=\frac2s\phi(x/s)
 [G(x;0,\omega_1,-\lambda_1)-G(x;0,\omega_2,\lambda_2)],
\]
where the displayed identity after [3] is

\(G(x;0,\omega,\lambda)=\Phi(x/\omega)-2T(x/\omega,\lambda)\).

Since (T) is even in its first variable and odd in its second, and \(\Phi(z)+\Phi(-z)=1\), the **symmetrized** density is exactly
\[
 \bar f_D(x)=\frac{f_D(x)+f_D(-x)}2
 =\frac4s\phi(x/s)
 [T(x/\omega_1,\lambda_1)+T(x/\omega_2,\lambda_2)]. \tag{A}
\]
The two scales need not agree. Patefield–Tandy (1) gives
\[
 T(h,a)=\frac1{2\pi}\int_0^a
 \frac{\exp[-h^2(1+u^2)/2]}{1+u^2}\,du. \tag{B}
\]
Substituting (B) into (A) is a positive mixture of functions \(e^{-A x^2}\), with (A>0). Multiplying each by its normalizing factor makes it a centered Gaussian probability mixture: the total mass is one by Tonelli and the fact that \(\bar f_D\) is a probability density. Its characteristic function at \(\sqrt t\) is therefore a probability Laplace transform, hence completely monotone in (t>0).

This uses the **general** [2] formula, not just the equal-scale special case [4]. Ignoring unequal scales would leave a real gap when mixing over M-Wright scales.

## Direct check of the zero-noise case; no unproved closure premise

Here is a self-contained verification that avoids relying on a limiting-class assertion. Write the half-normal densities as
\(2\sqrt{a/\pi}e^{-a x^2}1_{x\geq0}\) and
\(2\sqrt{b/\pi}e^{-b x^2}1_{x\geq0}\), (a,b>0).
Completing the square in their convolution gives, for (x\geq0),
\[
 f_{V-W}(x)=\frac{2\sqrt{ab}}{\sqrt{\pi(a+b)}}
 e^{-abx^2/(a+b)}\operatorname{erfc}\!\left(\frac{a x}{\sqrt{a+b}}\right).
\]
For negative (x), exchange (a,b). Thus, with
\(C=\sqrt{ab}/\sqrt{\pi(a+b)}\),
\(c=ab/(a+b)\), \(d_1=a/\sqrt{a+b}\), \(d_2=b/\sqrt{a+b}\),
\[
 \bar f(x)=C e^{-c x^2}
 [\operatorname{erfc}(d_1|x|)+\operatorname{erfc}(d_2|x|)]. \tag{C}
\]
The elementary special case of (B),
\[
 \operatorname{erfc}(d|x|)=\frac2\pi\int_0^\infty
 \frac{e^{-d^2x^2(1+u^2)}}{1+u^2}\,du,
\]
also follows by differentiating in (|x|>0) and using the value one at zero. Therefore
\[
 \bar f(x)=\frac{2C}{\pi}\sum_{j=1}^2\int_0^\infty
 \frac{e^{-A_j(u)x^2}}{1+u^2}\,du,
 \qquad A_j(u)=c+d_j^2(1+u^2)>0.
\]
Its mixing weight on the centered Gaussian density
\(\sqrt{A_j/\pi}e^{-A_jx^2}\) is
\(2C/[\sqrt\pi\sqrt{A_j}(1+u^2)]\,du\).
The weights are nonnegative and sum to one. Fourier transformation gives
\[
 \mathbb E\cos(\sqrt t(V-W))
 =\frac{2C}{\sqrt\pi}\sum_{j=1}^2\int_0^\infty
 \frac{e^{-t/(4A_j(u))}}{\sqrt{A_j(u)}(1+u^2)}\,du. \tag{D}
\]
This is a fully explicit probability Laplace mixture. It agrees with (A) as normal noise vanishes, but no limit is needed to justify it.

## Literal M-Wright specialization

Mainardi–Pagnini–Gorenflo (6.9), with \(\beta=2\alpha\), (0<\alpha<1/2), says exactly
\[
 M_\alpha(x)=\int_0^\infty
 \frac{e^{-x^2/(4\tau)}}{\sqrt{\pi\tau}}M_{2\alpha}(\tau)\,d\tau,
 \qquad x>0. \tag{E}
\]
The densities (M_\nu) have mass one and are nonnegative. Hence (X_\alpha) is a half-normal scale mixture, with conditional density in (E). Two independent copies have independent mixing scales; condition on both. By (D) their **conditional symmetrized difference** is a centered Gaussian mixture. Integrating the mixing measures retains that property. Although the conditional difference is generally not symmetric, the unconditional iid difference is symmetric; alternatively its real characteristic function is already the average in (D). There is no illicit replacement of a difference by a random-sign symmetrization of one input.

The published transform pair (4.7) gives
\(\mathbb E e^{-zX_\alpha}=E_\alpha(-z)\) for positive real (z).
Both sides are analytic on \(\Re z>0\), so the identity theorem extends this there. Taking \(z=\varepsilon-iu\), \(\varepsilon\downarrow0\), uses dominated convergence for the expectation and continuity of the entire Mittag-Leffler function. Thus \(\mathbb E e^{iuX_\alpha}=E_\alpha(iu)\).
The iid difference therefore has characteristic function \(|E_\alpha(iu)|^2\). Equations (D)–(E) prove the desired complete monotonicity. For \(\alpha=1/2\), (X_\alpha) is a single half-normal law, covered directly by (D).

All mixtures here are probability measures. Even when the final mixing rates are unbounded, derivatives at (t>0) are justified by boundedness of \(r^k e^{-tr/2}\) for fixed (k,t>0\). This yields all derivative signs, not merely finite-difference evidence.

## Eligibility judgment and strongest objection

Root's recommendation is **routine-corollary exclusion**, pending independent review. The outstanding “half-normal mixture difference” issue is now reduced explicitly to a published formula for the very distribution in question, one symmetrization, and the defining positive integral for Owen T. The other ingredient is a published theorem about the exact M-Wright objects. It is stronger evidence than merely observing that generic Gaussian-mixture closure might exist. The alternative direct calculation confirms no analytic gap is hiding in the old formulas.

Strongest contrary case: neither body says “the difference of iid half-normal scale mixtures is a Gaussian scale mixture,” and neither states the 2025 conjecture. One could treat symmetrization plus the Fourier conversion as a small new theorem and count the specialization. The reviewer must adjudicate this at full strength against the campaign's ban on routine classical corollaries; absence of an earlier explicit final statement alone is insufficient. No worldwide-priority conclusion is asserted.

The present work does not invalidate the existing 155-declaration Lean proof. It may invalidate discovery eligibility. Its considerable formalization effort is not itself discovery credit.

## Verification and limits

`check_classical_bridge.py` independently compares Papadopoulos [2] with direct convolution, verifies unequal-scale symmetrization, compares (D) with the literal (E_{1/2}) product, checks probability normalization, and checks the subordination moments. **180/180 diagnostics pass**, largest scaled error (8.08\times10^{-14}\); diagnostics are not proofs. A first JSON-write attempt failed on a NumPy boolean after the mathematical assertions had passed; explicitly converting to Python scalars fixed only serialization. Optional fitz/bs4 imports were unavailable; Poppler and standard-library parsing were used instead.

Actual journal Conjecture 3 body remains unread. The corrected BEUN repository REST API returns the exact article metadata but **zero bundles / attachments**. Its open-access label denotes DOI/arXiv links, not a retrieved journal body. ScienceDirect and De Gruyter challenges, and the separate 2015 report's Anubis barrier, were respected. No browser tab or credentials were used. This is not a new current-registry clearance; the recent live registry review remains separate.
