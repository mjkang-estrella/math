# Iteration 07 — analysis, transport, and constrained approximation

Date: 2026-10-08. Corpus premise: every theorem at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` is accepted. No upstream truth audit.

**Outcome: no prospective substantial finding from this pass; increment the accepted count by ZERO.** Three distinct routes were screened against actual statements and stronger companions. The most promising was a constrained version of three-dimensional Ball–Evans approximation. This report proves a restricted inverse-convergence theorem and gives a smooth counterexample to the attempted higher-exponent transfer. The positive theorem is a standard cofactor/change-of-variables transfer, not the new mechanism the task requires. The compression counterexample is a diagnostic, not a substantial advance. Neither should receive an R-number or be counted toward ten. R006 and R008 remain the two accepted substantial findings; eight remain.

The unresolved research target isolated here is simultaneous forward/inverse **energy-controlled** approximation. The precise missing estimate is stated in §6. This report does not claim that an arbitrary accepted forward approximating sequence supplies that estimate, or that the failure of one such sequence disproves existence of a better one.

## 1. Scope and provenance

Read `AGENTS.md`, `sources/upstream.json`, `frontier/README.md`, the iteration index, the earlier analysis scout, the polygon novelty review, and the Gaussian iteration/review. Those previous demotions are relevant: a valid extension using an established mechanism does not pass the contribution gate. No hot-spots, Gaussian, or bounded-multiplier operator variation was pursued.

The catalog extraction covered families 335–377; the actual-source screen concentrated on 360, 365, 368 and 374. A full-catalog keyword check for diffeomorphic/inverse/incompressible approximation found the two family-368 manuscripts. This is a scoped source search, not a claim to have read every theorem in the corpus. The complete `sources/preprints-tree.json`, not the truncated root tree, supplied the paths. Sixty TeX files covering the relevant manuscripts and their stronger companions were retrieved from immutable raw GitHub URLs; every Git blob hash agrees with the complete inventory. SHA-256 hashes, URLs, paths and sizes are in [retrieval-manifest.json](../sources/i07_analysis/retrieval-manifest.json). The input hashes are in [input-snapshot.json](../sources/i07_analysis/input-snapshot.json).

Only this report and `frontier/{sources,experiments}/i07_analysis/` were written. No agents, messages to external parties, publication, commits, staging or shared-index changes.

## 2. Exact accepted interfaces

The names below abbreviate directories under `preprints/`. All paths and full file hashes are retained in the retrieval manifest. These statements are premises, not objects of criticism.

**BE-high** — `Strong-diffeomorphic-approximation-in-three-dimensions-for-p-gt-2-September-24-2026/build/sections/01-introduction.tex`, labels `main:theorem` and `ha:approximation`. For every pair of bounded domains Ω,Λ in R³, every finite `p>2`, and every homeomorphism `f:Ω→Λ` in W¹,p, there are C∞ diffeomorphisms `f_j:Ω→Λ`, each in W¹,p, with

\[
\int_\Omega (|f_j-f|^p+|Df_j-Df|^p)\,dx\longrightarrow0.
\]

The target is exactly Λ. No boundary regularity, boundary extension, inverse Sobolev hypothesis or nonzero Jacobian is assumed. The paragraph immediately following the theorem explicitly withholds inverse Sobolev convergence and energy convergence for singular determinant penalties. **BE-low**, the corresponding `1-le-p-le-2` introduction, `main:theorem`, covers `1≤p≤2`; it does not supply the missing inverse-energy control. The smoothing appendices preserve target and provide fine value control; no inverse-energy estimate for the general pre-smoothing approximation is silently imported.

**MTW-foundation** — `Global-Support-and-Convex-Injectivity-Domains-under-Weak-MTW-September-25-2026/build/sections/introduction.tex`, `thm:main` and `thm:foundation`. The manifold is fixed, smooth, connected, compact, boundaryless, of dimension `n≥2`. The cost is `c=d²/2`. For every `x`, every minimizing velocity strictly before cut `v∈I(x)`, and every perpendicular pair ξ,η, the cross-curvature convention is

\[
-\frac32\,\partial_s^2\partial_t^2
 c(\exp_x(t\xi),\exp_x(v+s\eta))\big|_{s=t=0}\ge0.
\]

Then every `I(x)` is convex. The stronger foundation theorem gives global support for **every ordinary subgradient** of each cost potential; for each `0<t<1`, the map `(x,p)↦exp_x(tp)` from its full subgradient graph to M is a homeomorphism. Its intermediate regularity is an interior-time conclusion, not a time-one exclusion of conjugate endpoints.

**MTW-Hölder** — `Uniform-Bi-Holder-Transport-from-Weak-MTW-September-25-2026/build/sections/introduction.tex`, `thm:main`. Under the same geometry, for each `0<λ≤Λ<∞` with nonempty admissible probability-density class, there are `α∈(0,1]` and `C<∞` depending only on `(M,g),λ,Λ`. Every pair of measurable probability densities with `λ≤ρ_i≤Λ` has a homeomorphic optimal-map representative, and this map and its inverse are α-Hölder with constant C. No derivatives of the densities enter C. Conjugate cut points are allowed; no positive cut separation or explicit α is asserted.

**CD-rough** — `Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/build/paper.tex`, `thm:main`. On `B(0,3)⊂R³`, there exist two real scalar L∞ coefficients γ₀,γ₁ and fixed unspecified constants `0<c<C<∞`, with `c≤γ_i≤C`, equal to one near the boundary, distinct on a positive-measure set, and with identical full zero-frequency DN operators `H^{1/2}→H^{-1/2}`. The contrast is not prescribed. **Its `cor:localized` already gives 2^m distinct equal-DN conductivities in every finite collection of disjoint interior balls of any bounded connected Lipschitz three-dimensional domain.** The common map is not claimed to equal the DN map of conductivity one.

**CD-smooth-plus** — `Determination-of-a-metric-and-a-unitary-connection-from-one-boundary-patch-October-5-2026/build/sections/01-introduction.tex`, `thm:main`. On a compact connected smooth manifold of dimension `n≥3` with smooth nonempty boundary, an arbitrary nonempty relatively open proper patch Γ carries both input and observation. For smooth metrics gⱼ and smooth u(2)-valued one-forms Aⱼ on the **trivial Hermitian rank-two bundle**, equality of the zero-frequency sesquilinear DN energy forms for all compactly supported smooth Γ-data implies

\[
g_2=\Phi^*g_1,\qquad
A_2=U^{-1}(\Phi^*A_1)U+U^{-1}dU,
\qquad \Phi|_\Gamma=\mathrm{Id},\quad U|_\Gamma=I.
\]

Here Φ is a smooth diffeomorphism and U is a smooth U(2)-valued gauge. The scalar companion's `sections/08-scalar-consequence.tex` treats smooth positive scalar conductivities. Neither interface is a theorem for rough coefficients or unspecified transmission interfaces.

**Brenier-stability** — `Sharp-One-Third-Stability-of-Brenier-Maps-September-25-2026/build/source/sections/introduction.tex`, `main:stability`. For every compact convex body K with interior in `R^d`, `d≥2`, uniform probability source ρ on K, and nonempty compact target-support set Y, there is `C(K,Y)<∞` such that all Borel probability targets μ,ν on Y satisfy

\[
\|T_\mu-T_\nu\|_{L^2(\rho)}\le C(K,Y)W_2(\mu,\nu)^{1/3}.
\]

The exponent cannot be increased uniformly, already for three atoms on a fixed cube. This controls map values, not derivatives of an incompressibility correction. It does not supply §6's estimate.

## 3. Three candidates, and the pivots

### A. Weak MTW → smooth transport without a cut-locus assumption

**Target.** For smooth positive densities on an arbitrary fixed compact weak-MTW manifold, prove that the transport graph avoids the cut locus, then seek smooth optimal transport. This would extend the accepted bi-Hölder conclusion rather than repeat it.

**Attempt and obstruction.** The accepted homeomorphism and the density bounds control endpoint volume distortion. They do not bound the inverse of the differential of the exponential map at a conjugate pair. In particular, a Hölder inverse is not a lower bound for the smallest singular value of a Jacobi matrix. The foundation theorem shortens a minimizing geodesic to `t<1`; its constants cannot simply be passed to `t=1` in a region approaching conjugacy. No estimate bounding that degeneration in terms of the two density bounds was obtained.

**Primary comparison.** Figalli–Kim–McCann, *Regularity of optimal transport maps on multiple products of spheres*, [arXiv:1006.1957v1](https://arxiv.org/html/1006.1957v1), Theorem 5.1 and Corollary 5.2, prove exclusion and uniform separation on products of round spheres; their geometric argument uses that particular cut-locus structure. Corollary 5.3 supplies higher regularity after separation. Substituting the corpus's general bi-Hölder theorem for that specific geometric step does not reproduce it. This is a real missing estimate, not a disproof of the desired extension. **Disposition: not proved.**

### B. Forward Ball–Evans → inverse-energy or incompressible approximation

**Target.** Obtain approximants with simultaneous control of the forward derivative and inverse derivative, ideally with unit Jacobian when the input is volume preserving. This addresses an outstanding part of the nonlinear-elasticity motivation, after accepting both forward BE theorems.

**First attempt.** Apply BE-high, use strong convergence of minors, and change variables. This actually closes at inverse exponent one under the additional hypotheses in §4. It does not close above one: the transformed energy has a negative power of the Jacobian. Section 5 gives a smooth example defeating the claimed automatic extension for *every* `q>1`.

**Pivot within the lane.** Try composing the BE approximants with prescribed-Jacobian corrections, or with Brenier transports of their image densities. Exact correction for each smooth positive density is not the difficulty. The needed estimate is the weighted derivative error of the **composition**. Neither small L¹ Jacobian error nor the one-third L² Brenier-map estimate controls that error. The Dacorogna–Moser theorem gives a regularity-based prescribed-Jacobian construction, not such a consequence of forward Sobolev error alone. Section 6 isolates the precise useful estimate; it remains unproved.

**Primary comparison.** Hencl, *Ball–Evans approximation problem: recent progress and open problems*, [arXiv:2502.01336v1](https://arxiv.org/html/2502.01336v1), explicitly separates ordinary approximation from energy approximation (Open problem 4) and incompressible approximation (Open problem 5). Pratelli, [arXiv:1509.01045v1](https://arxiv.org/html/1509.01045v1), Theorem A, already proves simultaneous W¹,¹ approximation in dimension two. These statements motivate the higher-dimensional extension; they are not evidence of novelty for our elementary transfer. **Disposition: developed in depth below, but no substantial theorem.**

### C. Rough Calderón nonuniqueness → stable, regular, or localized counterexamples

**Target.** Strengthen rough nonuniqueness to a regularity-controlled family or extract a genuinely new instability theorem for smooth conductivities.

**Companion check and rejection.** Finite independent localized choices are already `cor:localized`. Thus the gluing construction cannot be counted as a bridge. Convolving the two rough coefficients inside their common constant boundary collar produces smooth, uniformly elliptic pairs with a persistent L¹ gap and DN discrepancy tending to zero. The latter step is standard boundary-operator continuity, not a new inverse-problem mechanism. Faraco–Kurylev–Ruiz, [arXiv:1311.5466v1](https://arxiv.org/html/1311.5466v1), Theorem 2.1, gives operator-norm DN convergence from G-convergence when the coefficients agree near the boundary; Rondi, [arXiv:1411.1978v1](https://arxiv.org/html/1411.1978v1), develops the related continuity/relaxation theory.

**Pivot and exact missing input.** To get a meaningful regularity-threshold statement one would need a uniform derivative/fractional-regularity budget for the actual scalarization block. CD-rough supplies only `c≤b≤C`; the self-similar repetition scale alone does not supply any fractional Sobolev seminorm of b. There is no valid deduction of a W^{s,p} bound from boundedness. Smooth recovery with no derivative budget versus rough nonuniqueness does not close that gap. **Disposition: localization is already upstream; smoothing is routine; the regularity improvement is unproved.**

## 4. Complete limited theorem: automatic inverse W¹,¹ convergence

This is recorded to separate what is valid from the proposed stronger claim. It is **not** offered as a substantial finding.

**Proposition P.** Let Ω,Λ be bounded domains in R³ and let `p>3`. Suppose `f:Ω→Λ` is an orientation-preserving homeomorphism in W¹,p, `J_f>0` almost everywhere, and `g=f^{-1}∈W^{1,1}(Λ)`. Let `f_j:Ω→Λ` be orientation-preserving smooth diffeomorphisms converging strongly to f in W¹,p. Then

\[
f_j^{-1}\longrightarrow g\quad\text{strongly in }W^{1,1}(\Lambda).
\tag{P}
\]

There is no uniform lower bound on `J_f` or `J_{f_j}` in this statement. No claim is made at `p≤3`, at zero-Jacobian sets, or for inverse exponents above one. If one obtains BE approximants without specifying orientation, they are eventually orientation preserving by local uniform convergence and degree on a fixed small interior ball; discard finitely many terms.

**Proof.** Use Frobenius norms and write `A_j=Df_j`, `a_j=det A_j>0`, `A=Df`, `a=J_f>0`, and `g_j=f_j^{-1}`.

1. **Minors and nonconcentration.** Polynomial inequalities for minors and Hölder give

\[
\operatorname{cof}A_j\to\operatorname{cof}A\text{ in }L^{p/2},
\qquad a_j\to a\text{ in }L^{p/3}.
\tag{4.1}
\]

In particular both sequences are uniformly integrable in L¹. Also

\[
\lim_{\delta\downarrow0}\sup_j
 |\{x:a_j(x)<\delta\}|=0.
\tag{4.2}
\]

Indeed, convergence in measure to a positive a controls all sufficiently large j, and positivity controls the finitely many remaining terms. By the smooth area formula, for every measurable `E⊂Λ`,

\[
|f_j^{-1}(E)|\le|\{a_j<\delta\}|+\delta^{-1}|E|.
\tag{4.3}
\]

Thus `sup_j |f_j^{-1}(E)|→0` as `|E|→0`. This is the essential nonconcentration statement; no inverse-Jacobian L∞ estimate is used. A W¹,p map with `p>3` has the Lusin N property. The area formula and `a>0` give the same estimate for f, and in particular f has N⁻¹ as well.

2. **Convergence of values.** Local Morrey embedding gives `f_j→f` locally uniformly. The inverses converge locally uniformly on Λ: for any `y=f(x)` choose a small ball U compactly contained in Ω with x in U. Its boundary image stays a positive distance from y; for large j the degree of `f_j` on U at nearby y′ equals the degree of f, namely one. Hence `g_j(y′)∈U`. Shrinking U and then taking finite covers of compact target sets proves the assertion. Since Ω is bounded, dominated convergence gives `g_j→g` in L¹(Λ).

3. **Gradient convergence in measure.** The inverse derivative identity is

\[
Dg(f(x))=A(x)^{-1}\quad\text{for a.e. }x.
\tag{4.4}
\]

For precision, this follows by restricting f and g to their countable differentiability/Lipschitz pieces and applying the inverse chain rule there; N and N⁻¹ discard the exceptional sets. Both maps are Sobolev by hypothesis, and `a>0` makes the inverse matrix legitimate.

Let `G=Dg`. For any finite measurable matrix field G on Λ,

\[
G\circ f_j\to G\circ f\quad\text{in measure on }\Omega.
\tag{4.5}
\]

To verify (4.5), approximate G in measure by a bounded continuous field on the bounded target (truncate first, then Lusin and continuous extension). The inverse images of its exceptional set are uniformly small by (4.3) and its counterpart for f. Continuous compositions converge in measure since `f_j→f` in measure. Letting the exceptional measure tend to zero proves (4.5).

Matrix inversion is continuous on invertible matrices, so `A_j^{-1}→A^{-1}` in measure. Equations (4.4)–(4.5) show `A_j^{-1}-G(f_j)→0` in measure on Ω. For any ε>0 the target exceptional set for `|Dg_j-G|>ε` has measure

\[
\int_{\{|A_j^{-1}-G(f_j)|>\varepsilon\}}a_j\,dx\longrightarrow0,
\]

by uniform integrability of `a_j`. Hence `Dg_j→Dg` in measure on Λ.

4. **Uniform integrability of inverse derivatives.** For every measurable E⊂Λ, the smooth area formula gives the exact cancellation

\[
\int_E|Dg_j(y)|\,dy
 =\int_{f_j^{-1}(E)}|\operatorname{cof}A_j(x)|\,dx.
\tag{4.6}
\]

The transpose in the inverse matrix formula disappears in the Frobenius norm. Uniform integrability of the cofactors and (4.3) show that the left-hand sides tend to zero uniformly in j as `|E|→0`. Vitali's theorem with step 3 now gives `Dg_j→Dg` in L¹. Together with step 2 this proves (P). ∎

**Accepted-corpus corollary, expressly routine.** BE-high supplies fⱼ, so every f under P's hypotheses has simultaneous forward W¹,p and inverse W¹,¹ smooth approximation onto the same target. The only corpus-dependent step is existence of a forward sequence. The inverse argument is a standard minors/change-of-variables mechanism and does not meet the requested contribution standard.

## 5. Complete obstruction to the attempted higher-exponent transfer

**Proposition Q.** There exist smooth orientation-preserving diffeomorphisms `F_j:(0,1)³→(0,1)³` such that `F_j→Id` strongly in W¹,p for **every finite p**, but, for **every q>1**,

\[
\|DF_j^{-1}\|_{L^q}\longrightarrow\infty.
\tag{5.1}
\]

For every `b>0` they also satisfy `∫(J_{F_j})^{-b}→∞`. Thus even convergence to a volume-preserving smooth limit does not make an arbitrary forward approximating sequence energy controlled.

**Construction and proof.** Fix a C∞ cutoff θ on R with `0≤θ≤1`, θ=1 on `[-1/2,1/2]`, and θ=0 outside `(-1,1)`. Put

\[
r_j=2^{-j-5},\quad \varepsilon_j=2^{-j^2},\quad c=\tfrac14,\quad d=\tfrac34,
\]

\[
v_j(t)=1-(1-\varepsilon_j)\theta((t-c)/r_j)
          +(1-\varepsilon_j)\theta((t-d)/r_j),
\qquad h_j(t)=\int_0^t v_j(s)\,ds,
\]

and `F_j(x)=(h_j(x₁),x₂,x₃)`. The two cutoff supports are disjoint; `ε_j≤v_j≤2`. Their integrals cancel, so `h_j(0)=0`, `h_j(1)=1`, and `h_j` is a smooth increasing diffeomorphism of (0,1). It equals the identity near the two endpoints. Consequently Fⱼ is a smooth diffeomorphism onto the cube. No claim of fixing the entire cube boundary is needed or made.

The derivative differs from I on a set of volume at most `4r_j`, and its difference has norm at most one. Also `sup|h_j(t)-t|≤2r_j`. Hence, for each finite p,

\[
\int |DF_j-I|^p\le4r_j\to0,
\qquad \|F_j-Id\|_\infty\le2r_j\to0.
\tag{5.2}
\]

On the plateau `|x₁-c|≤r_j/2`, of source volume rⱼ, the derivative is `diag(ε_j,1,1)`. Its image volume is `r_j ε_j`; the first derivative of the inverse there is `ε_j^{-1}`. Therefore

\[
\int|DF_j^{-1}|^q\ge r_j\varepsilon_j^{1-q}
=2^{(q-1)j^2-j-5}\longrightarrow\infty
\quad(q>1),
\tag{5.3}
\]

\[
\int(J_{F_j})^{-b}\ge r_j\varepsilon_j^{-b}
=2^{bj^2-j-5}\longrightarrow\infty
\quad(b>0).
\tag{5.4}
\]

These limits are exact consequences of the quadratic exponents, not finite numerical evidence. At inverse exponent one, the scalar change of variables instead gives

\[
\int_0^1|(h_j^{-1})'(s)-1|\,ds
=\int_0^1|1-v_j(t)|\,dt\le4r_j\to0,
\]

consistent with P. ∎

The smooth compression construction is elementary and does not depend on the accepted corpus. It refutes only the assertion that *every* strongly forward-convergent sequence has higher inverse-energy convergence. It does **not** refute simultaneous approximation: the limit here is the identity, which of course has a perfect constant approximating sequence.

## 6. The substantive step still needed

For `q>1`, the correct exact identity is

\[
\int_\Lambda |Df_j^{-1}|^q\,dy
=\int_\Omega
 |\operatorname{cof}Df_j|^q (J_{f_j})^{1-q}\,dx.
\tag{6.1}
\]

Set `E_j=|cof Df_j|^q J_{f_j}^{1-q}`. Under the remaining hypotheses of P, with `g∈W^{1,q}`, uniform integrability of **Eⱼ on the source** would imply strong inverse W¹,q convergence: (4.3) transfers that uniform integrability to `|Dg_j|^q` on the target; the measure-convergence proof is unchanged; then apply Vitali. This conditional implication is a proof, but it is not the missing construction.

A genuinely useful strengthening of BE would produce the approximants while proving uniform integrability of Eⱼ for inputs with finite corresponding energy. Strong forward convergence controls cofactor moments but gives no control of the negative Jacobian factor. Q shows that this is not a technical omission that can be filled by a general continuity theorem.

For the incompressible pivot, write a proposed corrected map as `H_j=Ψ_j∘f_j`. In the cube with a volume-preserving input, the target density transported by fⱼ is

\[
\rho_j(y)=\frac1{J_{f_j}(f_j^{-1}(y))}.
\]

A correction satisfying `det DΨ_j=ρ_j` makes `det DH_j=1`. Its derivative error is exactly

\[
DH_j-Df_j=(DΨ_j\circ f_j-I)Df_j.
\tag{6.2}
\]

A sufficient new estimate would make the Lᵖ norm of (6.2) tend to zero while retaining the correct target and injectivity. BE does give

\[
\int_\Lambda|\rho_j-1|\,dy
=\int_\Omega|1-J_{f_j}|\,dx\to0
\]

when `p>3` and `J_f=1`, but not a bound on (6.2). Dacorogna–Moser's [prescribed-Jacobian paper](https://numdam.org/item/AIHPC_1990__7_1_1_0/) is not a derivative-free estimate of this form. The Brenier `W₂^{1/3}` theorem estimates Ψⱼ's displacement in an appropriate map representation, not `DΨ_j` multiplied by the possibly large `Df_j` in (6.2).

No estimate establishing (6.2), no construction avoiding its need, and no energy-uniform replacement for the general BE wall/mesh stage was found in this pass. The smoothing stage alone cannot repair an energy defect already introduced before smoothing. I do not assert that the desired incompressible theorem is false.

## 7. Literature, importance, and limits

Six external primary retrievals, exact URLs and SHA-256 hashes are in [literature-manifest.json](../sources/i07_analysis/literature-manifest.json); searchable text is cached beside the HTML. The HTML responses for the specified arXiv versions are recorded as retrieved, rather than assuming the server's displayed dates certify immutable historical content.

The named target is the **Ball–Evans approximation problem for nonlinear elastic energies**, specifically Hencl's Open problems 4 and 5. The proposed substantial improvement would be simultaneous energy control or incompressibility, not another proof of the already accepted ordinary three-dimensional approximation theorem. Pratelli's Theorem A and the original prescribed-Jacobian work are positive prior-art constraints, not merely absence of search matches. No claim of worldwide priority is made for P or Q.

A bounded MathDB search did not identify a verified Ball–Evans problem URL or importance designation. The [inverse-problems listing](https://mathdb.com/database?tag=inverse-problems) does expose anisotropic Calderón questions, but this does not confer a score on the present approximation work. **No MathDB ranking, featured designation, or numerical impact score is assigned.** The absence of a retrieved Ball–Evans page is a retrieval limitation, not evidence that no page exists. No MathDB open/solved status overrides the task's accepted-corpus premise.

The primary external statements were read for target and prior-art checks. They were not used to reject any stipulated corpus theorem. A general correction from L¹ density discrepancy is not attributed to Dacorogna–Moser; general weak-MTW cut separation is not attributed to the sphere-product theorem; exact scalar DN realization is not inferred from homogenization.

## 8. Reproducibility and disposition for the parent

- `experiments/i07_analysis/retrieve.py` reconstructs the pinned TeX retrieval and input snapshot. It hashes every file and compares its Git blob SHA-1 to the complete inventory.
- `experiments/i07_analysis/literature.py` reconstructs the six primary HTML downloads and text extractions, recording errors rather than silently replacing sources.
- `experiments/i07_analysis/verify.py` checks the retained hashes and the exact source labels used above. Its output is `sources/i07_analysis/verification.json`.
- `sources/i07_analysis/artifact-hashes.json` hashes this report, both assigned directory trees and their scripts, excluding itself. The report and provenance are reproducible; no finite PDE solve or numerical asymptotic check is offered. The final check detects that the shared `frontier/iterations/README.md` changed since the initial snapshot; all other snapshotted inputs match. This pass did not edit that index.

**Recommended parent disposition:** preserve this as a screened negative/reduction report. Do not spend two independent review rounds trying to promote P: its proof mechanism already fails the contribution gate, even if the proof passes. If this lane is resumed, the task should be the explicit construction/estimate in (6.1) or (6.2), with a new idea for controlling compressed regions. Neither the endpoint inverse theorem, the smooth compression example, localized rough Calderón pairs, nor the already known sphere-product cut separation adds to the substantial-finding count.
