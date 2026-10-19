# Source371: geometric feasibility before selection

No theorem is frozen or claimed here. The exploratory full question was stable self-similar blowup on an arbitrary fixed smooth closed connected Riemannian 12-manifold, with the source's sufficiently large odd (p), an open set of physical (H^k) data, and the same local profile. Neither a local-chart solution nor a finite-dimensional manifold of data would answer that question. All calculations below preceded any target selection; no selection occurred.

## Exact source operation

The source fixes (a=1/(p-1)>0), a profile (Q), and (s_0=6-a). Its labels `lin:symbol-hypotheses`, `lin:Y`, `lin:YL`, `lin:spatial` give

\[
 |D^jQ|\le C_j\langle y\rangle^{-2a-j},\quad
 |D^j\mathcal V|\le C_j\langle y\rangle^{-2-j},\qquad
 \|v\|_Y^2=\|v\|_{\dot H^{s_0}}^2+\|v\|_{\dot H^k}^2.
\]

The expanding-torus low norm uses ((L^{-2}+|n/L|^2)^{s_0}), not the homogeneous norm alone. A constant has norm proportional to (L^a). `lin:local-derivatives` bounds local (D^jv) by (R^{\max(s_0-j,0)}\|v\|), and `lin:symbol-norm` gives (R^{6-\beta-s_0}+R^{6-\beta-k}) for an annular symbol of order (-\beta). The proof includes a discrete-to-continuous Fourier localization estimate `lin:J-bound`; localization of a fractional norm is not simply pointwise restriction.

`lin:compact-error` estimates potential terms and lower-order commutators by a small multiple of the global norm plus a fixed local (L^2(B_R)) norm. The leading high-order potential coefficient is independent of the derivative order; constants that grow with (k) belong to the lower-order compact terms. `lin:k-choice` then fixes (k). `lin:observation` establishes

\[
 \frac{d}{ds}\|v(s)\|^2\le-c\|v(s)\|^2+C\|v(s)\|_{L^2(B_R)}^2.
\]

The exact free squared-norm rates are (-a) and (6-k-2a). The regularized zero mode is included. `linear:decay` supplies the whole-space stable evolution and fourteen phase/center/time coordinates. The spectral classification is an operative stipulated input, not a new deduction of this round; its full spectral proof was not separately reread.

The important transfer in `linear:torus` does **not** claim global propagator convergence in operator norm. For a fixed slab it obtains local compactness in space and weaker time regularity; distributional limits are identified with the whole-space mild evolution. Crucially, the global energy inequality is integrated before passage to the limit. Formula `lin:escaped-norm` keeps the norm that may escape to infinity charged by the dissipative term. The resulting upper bound has the form

\[
 D(M)=e^{-cM}+C\int_0^M e^{-c(M-s)}e^{-2\eta s}\,ds\longrightarrow0.
\]

First choose (M), then (L). This gives stable contraction and a small finite-coordinate defect. Normalization supplies (pi_LE_L=I). Thus the source has already paid the key compatibility between a local limit and a global stable estimate.

`nl:residual-formula` gives cutoff-profile forcing (O(L_s^{-2-a})). Polynomiality for odd (p), the uniform algebra estimate, and the fixed-slab linear bounds give `nl:step`. The discrete Lyapunov–Perron graph uses a weighted sequence norm with factor (2^n), and phase/center/time variation supplies an open physical neighborhood. These operations were read in the complete linear and nonlinear section bodies. The source already addresses the apparent finite-codimension/open-set issue on the torus.

## Strongest compatible geometric construction tried

Keep a fixed physical manifold ((M,g)) and put (g_L=L^2g). There is no globally defined Euclidean dilation vector field on (M); the construction should use time-dependent norms and local moving coordinates, not invent one.

For even integer (k), consider

\[
 N_{0,L}(v)^2=\|(L^{-2}-\Delta_{g_L})^{s_0/2}v\|_{L^2(g_L)}^2,
 \qquad N_{k,L}(v)^2=\|(-\Delta_{g_L})^{k/2}v\|_{L^2(g_L)}^2.
\]

Since (Delta_{g_L}=L^{-2}Delta_g), these equal respectively (L^{12-2s_0}\|(1-Delta_g)^{s_0/2}v\|_{L^2(g)}^2) and (L^{12-2k}\|(-Delta_g)^{k/2}v\|_{L^2(g)}^2). For the free physical equation (partial_sv=iDelta_{g_{L_s}}v-av+ibv), (L_s=Le^{s/2}), the spectral operators commute exactly with the free evolution. Differentiation gives the same rates (6-s_0-2a=-a) and (6-k-2a). This exact calculation avoids pretending that a changing second-order principal part is bounded (H^k\to H^k).

In normal coordinates (x=y/L) at a fixed point, on a sufficiently small fixed physical ball,

\[
 g^{ij}(y/L)-\delta^{ij}=O(L^{-2}|y|^2),\qquad
 b_L^j(y)=O(L^{-2}|y|),
\]

where (Delta_{g_L}=g^{ij}(y/L)\partial_i\partial_j+b_L^j\partial_j) in the rescaled coordinates. The corresponding differentiated estimates hold to each fixed finite order with constants depending on the metric and chosen chart. Applied to the fixed profile, the annular defect obeys

\[
 |D^j((\Delta_{g_L}-\Delta)Q)|\lesssim_g L^{-2}R^{-2a-j}
 \quad(1\le R\lesssim L).
\]

For a dyadic annular piece, the Euclidean low/high symbol estimate therefore gives

\[
 L^{-2}\bigl(R^{-a}+R^{6-2a-k}\bigr).
\]

Both dyadic sums converge uniformly in their upper cutoff for fixed (a>0) and the source's large (k); the bounded central piece is (O_g(L^{-2})). Ordinary cutoff terms retain the smaller (O(L^{-2-a})) bound. Thus the geometric forcing has a plausible **larger but still summable** (O_g(L^{-2})) budget, rather than the exact torus exponent. On discrete slabs (L_n=Le^{nM/2}), the source's sequence weight is compatible with this budget once (2e^{-M}<1). No uniformity as (a\downarrow0), over arbitrary metrics, or in infinitely many metric derivatives is asserted.

This calculation is a local-symbol calculation, not a proof of all global spectral-norm estimates. To transport it to the displayed (N_L), one needs uniform chart/spectral localization estimates. It also does not turn the variable metric perturbation of the entire equation into a small bounded perturbation: it was applied to (Q), not to arbitrary (v\in H^k).

## What the full question still requires

The proposed norm package must actually prove uniform (L^infty), algebra, fractional localization, symbol, and local-derivative bounds on ((M,L^2g)). It must prove a global compact-observation inequality for all perturbations, with the high-order leading potential bound and all metric commutators assigned correctly. A local estimate of ((Delta_{g_L}-Delta)Q) cannot replace it. One then needs continuity in the moving center and frame, compatibility of local cutoffs with the global evolution and normalized spectral coordinates, and the complete degree/parameter argument for the full (H^k)-open neighborhood. These verifications were not completed here. In particular, no local, commuting, finite-dimensional, subsequence, or large-parameter substitute is being nominated.

At the same time, the source already supplies the difficult global-versus-local transfer **once** that analytic package is available. The calculations above do not isolate a remaining unpaid compatibility operation, and the unfinished norm verifications are not asserted to be one. This is why there is no freeze or full claim, rather than a claim of a new theorem from the forcing estimate.

## Primary comparison and timing

Buck, Carballeira, Gómez-Serrano and Shi, [arXiv:2609.23685v1](https://arxiv.org/pdf/2609.23685v1), §§4.2–4.3, Lemma 4.4, Proposition 4.7 and Proposition 4.8: the actual compact-dissipativity, finite-dimensional spectral splitting, and Lyapunov–Perron/localization proofs were read in extracted lines 1946–2230. These are radial Euclidean results for the paper's stated dimension/power pairs, not an arbitrary-manifold or physical-open-set theorem. Their compact remainder and graph operations are genuine antecedents. The primary was checked after the initial geometric feasibility calculation; this chronology is not backdated. No full proof of the paper or the source's profile/spectrum construction was reread. Extraction emitted a font-type warning; the argument's prose and displayed estimates were usable, but no visual audit of all glyphs was done.
