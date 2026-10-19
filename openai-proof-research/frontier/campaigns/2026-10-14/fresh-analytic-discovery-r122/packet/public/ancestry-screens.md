# Earlier-operation comparisons

No target was frozen during these screens. None of the failures below is claimed to refute a full mathematical target.

## 368: simultaneous forward/inverse Sobolev approximation

Both low- and high-exponent source introductions were inspected. In the actual low-exponent smoothing section, `sm:smoothing` already treats every locally bi-Lipschitz homeomorphism in (W^{1,p}), every finite (p), arbitrary bounded three-dimensional domains, fine continuous value tolerance, and the exact target domain. The relative topological tools and finite normalized libraries precede the choice of exceptional-set resolution.

The insertion estimate `sm:inverse-value-bound` controls (G^{-1}\circ h_Q-\mathrm{Id}) through the reference map (H)'s local bi-Lipschitz constant and value errors. It expressly does not require an inverse-Lipschitz bound for the current (G). This is strong inverse **value** control, not an integral bound for (D(G^{-1})). The distinction was checked in the actual proof, not guessed from its name.

The whole authored I331 `i331_bi_sobolev/analysis.md` was read. It already asks the same general simultaneous (W^{1,2}) approximation question and studies the inverse-energy density

\[
 \Phi(A)=\frac{|\operatorname{cof}A|^2}{|\det A|}.
\]

Under the stated finite-distortion/change-of-variables hypotheses, inverse Sobolev energy is the integral of this density. Forward convergence alone does not control its limsup near degenerating determinants. I331 also contains the stronger locally bi-Lipschitz finite-library route, where inverse derivative bounds are fixed before the mesh scale and an existing bi-Sobolev approximation theorem is the compatible antecedent. It records why one source collapse example has divergent inverse energy and is therefore not an admissible counterexample to the general question.

No new same-map limsup inverse-energy construction was found. No rescaled or restricted version of I331 was restarted. The external proofs cited inside I331 were not newly read in r122, so its text is historical evidence of prior work, not independent primary proof clearance.

## 374: transport with weights or changing source

The source's complete finite-stability and gradient sections were read. `finite:potentials` couples the two finite target measures with fixed masses, uses monotonicity to prevent collisions along the interpolating sites, differentiates cell masses and intercepts, solves a graph-Laplacian equation in its zero-sum range, and applies the moment derivative inequality. This yields linear (L^2) potential control. `gradient:interpolation` combines a finite-difference term proportional to (h^{-2}\|u_0-u_1\|_2^2) and a convex-slice boundary error proportional to (h), giving exponent (1/3). `gradient:extension` performs the full finite-target approximation and Fenchel identification.

The actual r12 candidate was read in its hypotheses, weighted-cell calculus, midpoint coupling, derivative-moment, potential, gradient and final-assembly passages, with a truncation in the initial combined display subsequently repaired for the opening. It already handles a fixed compactly supported log-concave source positive in the interior without a positive lower density bound. Its triangular conditional-CDF midpoint construction yields weighted domination; its slice difference direction follows the side on which the weight does not decrease. These are actual prior operations, not just a title about weighted transport. The candidate's author status or claimed novelty is not adopted.

Changing the source measure during the target interpolation changes the differentiated cell masses and the moment identities. The fixed-mass intercept argument does not automatically give a quantitative solution for that extra source derivative. No full all-source estimate and no independently justified constant dependence were obtained. A weighted fixed-source restatement would recycle the stronger historical proof. The r12 body was read after initial varying-source feasibility, before any freeze; its independent primary proof chains were not reread.

## 373: larger marginal number and Riesz costs

The actual local obstruction, final construction and Riesz sections were read, with a partial read of the strict-certificate body. The construction combines a central two-branch choice, separated satellite roles, a strict dual contact certificate and a common marginal density. The Riesz version works through the same geometric Hessian/transversality mechanism, not merely replacing the symbol (1/r) in a final formula.

The actual r54 `original-scope.txt` already freezes all (N\ge3), all (d\ge2), all positive Riesz exponents, smooth compact density with smooth square root, and equal infima with Monge nonattainment. Its scope includes the regular two-rotated-((N-1))-gon construction. Thus adding spectator sites or changing the exponent would not be a fresh direction. That entire author proof and its external primary clearance were not reread here; this round uses the existing full-scope record to avoid duplication, not to certify it.

## 148: entropy rate with dependent symbols

The source introduction and its exact main statement distinguish entropy of the random affine product from symbolic word entropy; exact affine collisions are allowed. Source proof architecture needs an actual convolution factorization after the relevant low-entropy conditioning. General stationary dependence does not supply that factorization for free.

The actual r113 operation comparison and full `regenerative-calculation.md` were read. That calculation already proves, for any dependent finite-alphabet group-valued word process and integrable random clocks (S,T),

\[
 |H(G_S)-H(G_T)|\le H(S,T)+\mathbb E|S-T|\log|A|.
\]

It reconstructs one product from the other and the intervening word by group cancellation, without needing injective coding or a stopping-time assumption. In an iid regeneration-block representation, it obtains (h_{\rm word}=\ell h) with an explicit sublinear clock error. Finite-state bridges conditioned on endpoints and transition counts are also treated there; their exact block probabilities are constant on each count class. A source tail conditioned on an endpoint is not the unconditional stationary tail, and the historical note makes that distinction explicit.

The strongest compatible regeneration reduction was therefore already available. For unrestricted stationary ergodic dependence, an exact conditional convolution or a replacement uniform high-(q) small-ball input remains missing. This round did not build either. The primary Comets–Fernández–Ferrari and Jordan–Rapaport bodies discussed in r113 were not downloaded or reread here. No generic dependent-entropy theorem is claimed from a historical report, and no finite-state or regenerative renaming is nominated.
