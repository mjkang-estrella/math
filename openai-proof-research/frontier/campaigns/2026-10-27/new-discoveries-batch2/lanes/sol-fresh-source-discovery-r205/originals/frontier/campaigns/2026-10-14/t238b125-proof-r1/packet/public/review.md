# T238B125 — independent original-scope correctness review

**Verdict: PASS, relative to the stipulated pinned OpenAI statements and operative proofs. No mathematical repair is required.** This verdict covers the entire frozen theorem, including its credited sharpness statement. It does not assign contribution, acceptance, priority, or a campaign count. Publication remains stopped.

The reviewed author proof has SHA256 `fc725dd2d70ca3a5a52bcfdca7da954e674a3157353b831dd2caf6badd097881`; the unchanged frozen scope has SHA256 `ec09396badbea0351a0eb2f8bdb7b780e1d74ffdace92bb04114cccdc5be4a22`. This is a new independent mathematical review, not adoption of the parent assessment or a reinterpretation of the earlier unlaunched brief. No author files were edited and no weaker theorem was substituted.

## Exact claim and dependency boundary

For each fixed real \(0<\delta<1/2\), one finite \(C_\delta\), depending only on \(\delta\) and fixed source constants, works simultaneously for every integer \(d\ge1\), \(N=2^d\), deterministic initial deck, deterministic infinite array \(p_{t,x}\in[\delta,1-\delta]\), and \(0<\epsilon\le1/4\). All switch coins are independent across positions and times. A physical step swaps each pair \((0,x),(1,x)\) using its specified probability, then applies the left cyclic coordinate rotation. At **every integer**

\[
t\ge d\left\lceil C_\delta\bigl(d+\log(1/\epsilon)\bigr)\right\rceil,
\]

the law of the **entire permutation** is within \(\epsilon\) of uniform on \(S_N\). There is no homogeneity, periodicity, common eigenbasis, or adaptive selection of the array. For each fixed homogeneous \(p\ne1/2\), the credited r113 lower bound gives distance tending to one at sweep counts \(s_d\le(1-\alpha)\log N/(-2\log|1-2p|)\), for every fixed \(\alpha\in(0,1)\). Together these yield the stated fixed-error \(\Theta_p(d^2)\) order.

All OpenAI inputs are taken at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, with their operative proofs stipulated. The central actual source is *Conditional coordinate sweeps and analytic transfer*, `build/sections/03-paths.tex`, Theorem `thm:conditional` / `ac:main`, equation `ac:eq:15`, **at z=0 only**. I read that complete body, its complete `02-preliminaries.tex`, `07-analytic.tex`, and `01-introduction.tex` physical model. The source explicitly covers every fixed feasible layer-disjoint path family and every residual irreducible, including empty and trivial cases; it uses fixed identifications of the remaining input and output slots. Its near-uniform positive-z hypotheses are never imposed on the biased target: the new perturbation argument starts at the uniform z=0 law.

The following checks validate the new deductions. They do not audit the truth of the stipulated source. External comparison papers cited in the author's comparison are not premises of this proof. The finite-dimensional linear algebra, likelihood calculation, Green-kernel estimates, Fourier normalization, and lower-bound recursion are checked below directly. No unsupported external comparison theorem is needed to reach this verdict.

## Conditional operator and every restriction constituent

Write \(a=c_0/(2q)>0\), \(b=e_0/(2q)>0\), with \(c_0=e_0=10^{-4}\). Taking a \(2q\)-th root of the source moment inequality and bounding operator norm by unnormalized Schatten norm gives

\[
\|K_\mu^H\|_{op}\le D_\mu^{-a}N^{bh}.
\]

Here \(c(N)\ge c_0\), \(e(N)\le e_0\), \(\log D_\mu\ge0\), and the discarded trajectory cost is nonnegative. The author's use of these inequality directions is correct.

Fixing the h labelled input-output pairs makes the full permutation a left/right translate of the stabilizer subgroup \(S_{N-h}\). The averaging operator is therefore, up to two fixed unitaries, the average of exactly the source residual law in the restriction of \([\lambda]\). Orthogonal decomposition into subgroup irreducibles makes its operator norm the maximum over *all* occurring constituents, regardless of multiplicity.

For every occurring \(\mu\), not merely a selected large constituent,

\[
D_\lambda\le (N)_h D_\mu\le N^hD_\mu.
\]

The author's explicit intertwiner argument verifies the needed induction fact: a nonzero subgroup map T gives \(v\mapsto[g\mapsto T\rho(g)v]\); its values on subgroup cosets determine it, and its kernel is invariant under the full group and hence zero. The target space has dimension \((N)_hD_\mu\). This also covers \(h=N\), when the residual group is trivial. Consequently

\[
\|A_\lambda^H\|_{op}\le D_\lambda^{-a}N^{(a+b)h}.
\]

There is no suppressed multiplicity and no identification of a random restriction with a fixed invariant subspace of the target biased operator.

## Selected record, both cylinder implications, and zero masses

For a fixed set F of k altered stage-lines, form the record from every label whose path meets F and its endpoints. In an ordered product grid, the slot after stage j is exactly \((v_1,\ldots,v_j,u_{j+1},\ldots,u_b)\); thus endpoints determine every stage-line assignment. Since every line has size at most \(M=R^2\), at most Mk labels are recorded.

If the selected record equals a particular realized H, its fixed paths occur. Conversely, in a realization producing H those paths fill **all input slots of every line in F**. These same paths in any other realization still fill those slots. Bijectivity excludes any additional label entering an altered line; each recorded label still visits its original altered line because its path is fixed. Thus the selected label set and all its paths are precisely H. The record event is exactly the fixed-path cylinder, with no extra exclusion condition. The fact that a label might visit several altered lines only reduces the union's size.

On that cylinder each altered line's entire input-output assignment, hence its complete permutation \(g_L\), is determined. Relative to independent uniform line laws, the modified network has density

\[
w(\omega)=\prod_{L\in F}|L|!Q_L(g_L(\omega)).
\]

This is constant on the cylinder. The uniform network gives every feasible assignment positive mass. If that constant is positive it cancels in conditional probabilities, leaving exactly the all-uniform conditional network and its residual bijection; if it is zero the entire cylinder has zero modified mass and is omitted from the mixture. This handles arbitrary zero masses in Q without division by zero or a lower density assumption. Convexity of operator norm therefore yields

\[
\|A_\lambda(F)\|_{op}\le D_\lambda^{-a}N^{Bk},\qquad B=(a+b)M.
\]

This is the essential bridge; it is valid at its stated generality. Its right side is allowed to exceed one. The argument does not assert residual uniformity for an arbitrary transcript or after revealing all switches.

## Real interval and uniform bounded-bias disk

For independent line mixtures \((1-z)U+zQ_L\), real \(z\in[0,1]\), summing over all Bernoulli subsets gives exactly the binomial generating factor

\[
\|K_\lambda(z)\|_{op}\le D_\lambda^{-a}(1-z+zN^B)^L
 \le D_\lambda^{-a}e^{LzN^B}.
\]

The number of stage-lines is \(L=\sum_jN/m_j\le N^2\). Hence with \(\eta=1/(8N^{B+2})\), the exponential is at most \(e^{1/4}\) on \([0,2\eta]\). The source preliminaries, `ac:eq:1` and the subsequent large-diagram bound, give \(D_\lambda\ge N/e\) for all sufficiently large N outside trivial and sign. Thus \(\log D_\lambda\ge1/(2a)\) makes the bound at most \(D_\lambda^{-a/2}\) throughout \([\eta,2\eta]\). All thresholds are schedule independent.

For a transposition, \(A_p=(1-p)I+p\rho(\tau)\) has eigenvalues 1 and \(1-2p\). On the negative eigenspace its absolute eigenvalue is at most \(1-2\delta<1\). Equality of norm through a product of these contractions forces equality at every factor, so the intermediate vector is fixed by that transposition and stays unchanged. A complete binary line sweep uses every cube-edge transposition; connectedness makes these generate \(S_m\). A nontrivial irreducible therefore cannot have a norm-one vector for that product. Compactness of the finite probability cube and the finite list of line sizes and irreducibles gives a single \(\kappa_\delta<1\). This is a singular/operator norm argument and remains valid when some p exceed 1/2.

In any restriction to a line subgroup, uniform averaging is the invariant projection P and \(PQ=QP=P\). Thus the interpolated operator is \(I\oplus zQ\), with the second block bounded by \(|z|\kappa_\delta\), including arbitrary multiplicities. A fixed \(r>1\) with \(r\kappa_\delta<1\) gives \(\|K_\lambda(z)\|\le1\) on \(|z|\le r\), uniformly over grids, representations, schedules, and polynomial degrees. At z=1 it is the actual specified biased sweep.

## Green kernel and transfer exponent

For real \(t\in[\eta,2\eta]\), with \(2\eta<1/2<r\), set

\[
g_r(z,t)=\log\left|\frac{r^2-tz}{r(z-t)}\right|,
\quad V(z)=\eta^{-1}\int_\eta^{2\eta}g_r(z,t)\,dt,
\quad H_N=\log(r/\eta)+2,\quad W=V/H_N.
\]

The numerator's zero is outside the disk. Also
\(|r^2-tz|^2-r^2|z-t|^2=(r^2-t^2)(r^2-|z|^2)\).
This proves positivity inside the disk and zero boundary values on its circle. V is harmonic away from the slit. The logarithmic singularity integrates continuously even at slit endpoints: its local absolute integral is bounded by a constant times \(h(1+|\log h|)\), tending to zero with h.

For a slit point x, the positive numerator divided by r is at most r. Scaling by \(\eta\) gives
\(V(x)\le\log(r/\eta)+1+\log2<H_N\); the maximum of the remaining integral occurs at the midpoint. Thus \(0\le W\le1\) on the slit. At 1, \((r^2-t)/(r(1-t))\ge r\) because \(t(r^2-1)\ge0\), so \(V(1)\ge\log r>0\).

For any scalar matrix coefficient f, \(\log|f|\) is subharmonic, with the usual minus-infinity value at zeros. On the bounded disk minus the closed slit,
\(J=\log|f|+(a/2)\log D_\lambda\,W\) has boundary limsup at most zero on both slit banks, both endpoints, and the outer circle. It is bounded above. The boundary maximum principle applies; equivalently, locally a harmonic conjugate of W reduces its submean property to the analytic maximum principle. No global conjugate on the slit domain is needed. The identically zero f case is immediate.

Taking the supremum over unit coefficient vectors gives

\[
\|K_\lambda(1)\|\le
 \exp\left[-\frac{a\log r}{2H_N}\log D_\lambda\right]
 \le D_\lambda^{-\gamma_\delta/\log N}
\]

for one positive schedule-independent \(\gamma_\delta\), since \(H_N=(B+2)\log N+\log(8r)+2\). The stated normalization and inequality directions are correct; there is no extra \(\eta\) loss.

## Products, sign, regular multiplicities, and every error

Grouping consecutive bits into sizes \(\ell+t,\ell,\ldots,\ell\), \(\ell=\log_2R\), gives line sizes in \([R,R^2]\) for \(d\ge\ell\). Operations on different coarse lines commute and use disjoint coins, so their chronological bit layers may be interleaved without changing the law or probabilities. This is exactly one d-step sweep in the nonrotating frame. Independence across sweeps yields the ordered Fourier product of potentially different matrices. Submultiplicativity gives exponent \(-\gamma_\delta s/\log N\); neither stationarity nor normality is required.

The sign of a sweep is the product of the signs of its \(Nd/2\) independent switches. Its absolute coefficient is at most \(r_0^{Nd/2}\), \(r_0=1-2\delta\). It is not assumed zero. Matrix Plancherel and Cauchy–Schwarz give

\[
4\operatorname{TV}_s^2\le r_0^{sNd}
 +\sum_{\lambda\notin\{(N),(1^N)\}}
 D_\lambda^{2-2\gamma_\delta s/\log N}.
\]

One dimension factor is the regular multiplicity; the other comes from \(\|A\|_{HS}^2\le D_\lambda\|A\|_{op}^2\). Both are present. A fixed initial permutation only inserts unitaries.

For \(k=\min(N-\lambda_1,N-\lambda'_1)\le N/3\), transposition of diagrams and the partition of the remaining k boxes give at most \(2\cdot2^k\) shapes. The source dimension bound gives \(D\ge e^{-1}(N/k)^k\). For larger k, \(\log D\ge c_{dim}N\), and at most \(2^N\) shapes suffice. Choosing \(\beta_0\) with \(2\,3^{-\beta_0}<1\) and \(\beta_0c_{dim}>\log2+1\) bounds the total reciprocal-dimension sum by an absolute finite \(C_0\). No unbounded partition factor is discarded.

At \(s_0=\lceil(\beta_0+2)\log N/(2\gamma_\delta)\rceil\) that sum is at most \(C_0\). Each subsequent sweep multiplies its bound by at most \(e^{-\gamma_\delta}\), because \(\log(N/e)\ge\tfrac12\log N\) for large N. Thus it is at most \(C_0e^{-\gamma_\delta(s-s_0)}\). Taking
\(s-s_0\ge[2\log(1/\epsilon)+\max(0,\log(C_0/2))]/\gamma_\delta\)
makes this at most \(2\epsilon^2\). The sign term is at most \(e^{-2[-\log r_0]s}\) since \(Nd\ge2\), and is also at most \(2\epsilon^2\) after a constant multiple of \(\log(1/\epsilon)\) sweeps. With \(\log N=d\log2\), one \(C_\delta\) covers these conditions for all \(0<\epsilon\le1/4\), including arbitrarily small errors.

## Finite dimensions and later physical times

For each excluded finite d, every fixed sweep mask has probability at least \(\delta^{K_d}\), \(K_d=Nd/2\), independently of the schedule. Identity and each single cube-edge transposition are realizable masks. A path of length at most d gives any endpoint transposition in at most \(2d-1\) edge transpositions; decomposing cycles uses at most \(N-1\) arbitrary transpositions. Padding with identities to \(H_d=(N-1)(2d-1)\) sweeps gives every permutation probability at least \(a_d=\delta^{K_dH_d}\) in each such block.

The mask events for distinct output permutations are disjoint, hence \(\beta_d=N!a_d\le1\). Every block kernel dominates \(\beta_d U\) and preserves U even for the nonidentical arrays. Subtracting this common uniform component and iterating gives \(\operatorname{TV}\le(1-\beta_d)^{\lfloor s/H_d\rfloor}\). For \(\beta_d<1\), it suffices that \(s\ge H_d[1+\beta_d^{-1}\log(1/\epsilon)]\). For \(\beta_d=1\) one block suffices. The maximum over finitely many d enlarges only \(C_\delta\); d=1 is included.

With rotation R and the physical first-coordinate switch layer \(S_t\), write \(\Pi_t=RS_t\Pi_{t-1}\). Then \(\widetilde\Pi_t=R^{-t}\Pi_t=(R^{-(t-1)}S_tR^{t-1})\widetilde\Pi_{t-1}\): the nonrotating frame visits successive original coordinates. After d steps the accumulated rotation is identity, with the probability array only deterministically reindexed. Each later physical step is independent of the current deck and preserves uniform measure, so TV contracts at every individual step. The exact integer threshold in the frozen statement therefore controls all later times, not just a sweep subsequence.

## Credited lower bound and prior objections

I read the actual r113 `packet/public/screen-238.md`, not just its summary. Assign each card its initial first-coordinate sign and put \(F=\sum_x(-1)^{x_1}c_x\). Other coordinate updates leave F unchanged. Each first-coordinate pair contribution has magnitude at most two; independent swaps give conditional mean \(\rho F\) and conditional variance at most \(8Np(1-p)\), with \(\rho=1-2p\). Therefore \(EF_s=N\rho^s\) and \(\operatorname{Var}F_s\le2N\). Under uniform permutation the balanced signs have covariance \(-1/(N-1)\), yielding \(\operatorname{Var}_UF=N^2/(N-1)\).

Chebyshev on \(\operatorname{sign}(\rho^s)F\ge N|\rho|^s/2\) gives exactly the author's two error terms \(8/(N|\rho|^{2s})+4/((N-1)|\rho|^{2s})\). They vanish uniformly under the frozen bound on \(s_d\), since \(N|\rho|^{2s_d}\ge N^\alpha\). Negative \(\rho\) and s=0 are covered. The lower scale for physical mixing also follows by TV monotonicity between successive sweep endpoints. For each p, choose \(0<\delta<\min(p,1-p)\) for the upper bound. Credit is correctly retained with r113; this review assigns it no new contribution.

The I132 Candidate T and I135 section 2.4 objections remain valid at their original scopes. A full transcript can determine the permutation; this proof never claims otherwise and permits its conditional bound to be vacuous. Marginally uniform dependent X and \(X^{-1}\) multiply to identity; this proof uses actual independent increments, not marginal completion. Observing parity obstructs conditional uniformity; this proof estimates the unconditional sign coefficient separately. Averaged conditional TV does not control rare environments; this proof instead uses the stipulated every-fixed-path moment bound after proving an exact cylinder identity. None of these objections refutes the deductions just checked.

## Disposition and limits

No issue requiring repair was found in the complete original theorem. The PASS is conditional on the user's upstream stipulation; it is neither an unconditional certification of those sources nor a formal proof check. The comparison file was read completely, but its broad novelty, reading-history, and alternative-route claims are not independently certified here. The weighted companion is acknowledged at its actual strength: `tra:duality:weighted` allows arbitrary nonnegative line weights, and the full regular multiplicities are already explicit in its spectral-conversion section. No claim of contribution, acceptance, exhaustive literature clearance, or count is made.

Detached author FINAL/REPORT/MANIFEST/control-receipt hashes reconcile with the actual files and the supplied parent-saved completed task status. The inspected author verifier passed with the detached FINAL/REPORT anchors. The review's own verifier and copied controls authenticate bytes and provenance only. No finite diagnostic was used as mathematical evidence. See `reading-limits.md` and `REPRODUCE.md` for exact extents and the independent seal boundary.
