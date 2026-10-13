# R020 — Global dimension-free stability of binary-information contraction

**Accepted as the fourteenth substantial finding.** The complete all-rectangle statement passes [I304 independent proof review](../reviews/i304-global-soft-proof.md) unchanged, and [I303 independent contribution review](../reviews/i303-global-soft-contribution.md) as SUBSTANTIAL. The parent read and authenticated the final evidence. Validation is a written mathematical review under the stipulated corpus, not a formal proof certificate or external human peer review.

## Exact theorem

Let X be uniform on {-1,1}^n, n>=1. For u:{-1,1}^n->[-1,1], define

    psi(t)=((1+t)log(1+t)+(1-t)log(1-t))/2,
    I(u)=E psi(u)-psi(Eu),
    d_a(u)=min_(1<=i<=n, s in {-1,1}) E|u-s a X_i|².

Let T_r be independent bit noise with correlation r. For every

    0<a0<=a1<1,       0<r0<=r1<1,

there is a finite constant C depending only on these four endpoints such that, for every finite n, a in [a0,a1], r in [r0,r1], and every u with exactly I(u)=psi(a),

    d_a(u)<=C [psi(ra)-I(T_r u)].

Arbitrary bias, endpoint values, rare spikes, support and complexity are included. No initial closeness, singleton lower bound, or condition r1*a1<1/sqrt(2) is imposed. The constant is existential and independent of dimension.

The power one on the deficit is sharp for squared L2 distance. Equivalently, the power one-half is sharp for L2 distance.

## Proof and dependency chain

The stipulated input is the sharp soft binary-information contraction and its production/joining machinery in [OpenAI family 119 at the fixed revision](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-binary-information-contraction-on-the-discrete-cube-September-24-2026). Internal stability deductions are independently proved rather than stipulated. The [complete proof](../experiments/i304_global_soft_proof/analysis.md) checks the following chain.

1. Put F(psi(t))=t atanh(t). The production surplus R(s)=D(T_(exp(-s))u)-F(I(T_(exp(-s))u)) is nonnegative. An exact integrating-factor formula controls earlier information deficits by the final deficit, including initial endpoint values by positive-time limits.
2. The constrained entropy Hessian is positive away from the signed-coordinate family. Splitting a perturbation into small values and rare large values, then applying hypercontractivity to the latter, gives uniform local L2 coercivity without excluding spikes or endpoints. Retained losses in the source's joining argument give equality rigidity and compactness for pair laws on a fixed square. Together with production integration, this pays the entire sector having a fixed positive singleton coefficient.
3. The remaining diffuse sector is excluded using an unrestricted Gaussian strictness argument. For a scalar Gaussian equality candidate w, set

       k=r atanh(ra)/atanh(a),
       b=exp(psi(a))-1,
       q=Var(w)/(1-(Ew)²).

   Biased likelihood-ratio Jensen gives q>=b, and a separate all-amplitude scalar calculation gives

       k>r²(1-b)/(1-r²b).

   The equality Euler equation and an admissible translation yield, with D>0 the weighted derivative energy,

       G''(0)<=D[k(1-r^(-2))+(1-k)(1-q)]<0.

   This contradicts minimization. The positive mean term is retained and paid; it is not discarded. Smoothing and tail estimates justify differentiation, and an equality-preserving noise split removes the initial smoothing assumption.
4. Classical law-preserving Gaussian rearrangement reduces arbitrary dimension to monotone scalar kernels. Their compactness gives a uniform positive Gaussian gap on every compact open parameter rectangle. Fixed-degree truncation and Lindeberg replacement transfer both information budgets from a purported diffuse cube sequence, with clipping and mean errors controlled. This contradicts that gap. A fixed scalar compactness argument, rather than compactness of growing-dimensional spaces, supplies uniformity.
5. Quantitative soft sorting transfers the increasing-kernel estimate back to arbitrary u. The local, marked and diffuse sectors therefore give the displayed global linear bound.

For sharpness, fix interior a,r and use the exactly normalized two-coordinate perturbation u=c(epsilon)X1+epsilon X2, where I(u)=psi(a). Then d_a(u)=epsilon²+O(epsilon⁴), while the deficit is K(a,r)epsilon²+O(epsilon⁴) with K(a,r)>0. No larger power of the deficit can work. [The calculation](../iterations/i302-parent-sharpness-note.md) is independently checked in I304 Section 10 and is supporting evidence for this one finding.

## What is substantial, and what is credited

Translations and second variation are classical; [Heilman–Tarter](https://arxiv.org/pdf/2011.05583v2), Lemma 5.1 and equations (9)–(11), are a concrete predecessor. The new operation identified by I303 is the entropy-specific, bias-aware, all-amplitude comparison that pays the positive mean term and excludes the full scalar Gaussian equality obstruction. Ordinary Gaussian EPI compares with a different curve and does not provide the required high-amplitude gap.

Sorting, the local Hessian method, source optimizer margins, compactness, rearrangement, invariance, likelihood-ratio Jensen and hyperbolic identities are credited ingredients, not additional findings. The restricted S295 theorem retained a TECHNICAL contribution verdict; it is neither counted separately nor relabelled substantial. The full theorem resolves the same S128 target by supplying its missing unrestricted Gaussian step.

## Validation and limits

- I304: full proof PASS unchanged, analysis SHA256 `c9a10e576923b20a4570762b1817d143d1da71c5e332a6a7e80a6bb66f01b9c5`; separate supporting sharpness PASS.
- I303: full contribution SUBSTANTIAL, analysis SHA256 `788dfb0bb9e39bef772c4793f48c3537acf2b80e6c0237c402f8d8d53455ae99`.
- The parent verified the final output hashes, source identities and recorded passages; details are in the [proof disposition](../iterations/i304-global-soft-proof-parent-disposition.md) and [contribution disposition](../iterations/i303-global-soft-contribution-parent-disposition.md).
- No effective C, uniform bound as parameters approach zero or one, optimal Gaussian information curve, or worldwide priority is claimed. The new endpoint target in I313 remains separate and unresolved in general dimension.

This acceptance receives its own commit. **Fourteen accepted; six remain toward twenty.**
