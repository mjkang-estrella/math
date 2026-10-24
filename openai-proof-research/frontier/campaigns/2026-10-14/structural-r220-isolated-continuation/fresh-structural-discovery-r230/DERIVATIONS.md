# r230 prefreeze derivations — Source354

No theorem is frozen. No nominee or self-assigned grades/count.

Authorized runtime: Codex / GPT-6 Astra / xhigh / default service tier, as specified by the task. Campaign 19/20, latest R041; those are supplied coordination facts, not peer-body premises. All writes confined to this exact root. The complete original standing brief was read in the prompt; obsolete model/count lines are overridden. The source and all operative upstream proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true.

## Operative source interface (read before extended deductions)

Unit torus, total volume 1, v=min(V,1-V), P=min((36π)^(1/3)v^(2/3),2 sqrt(πv),2). Closed phase intervals include adjacent ties at v1=4π/81, v2=1/π. Equality up to flat ambient isometry and null changes; complements for V>1/2. Shortest axes and translations all included. Internal doubled torus has normalized V=physical volume/8, A=physical area/8=P_unit/2 and h=sum curvature. Unit branch endpoint radii 1/3 and 1/π, safely below injectivity radius 1/2.

Actual driver order: preliminaries → geometry → sections → early-exclusions → nesting → completion in paper.tex → elementary-estimates → numerics → references. Nested figure inputs: vertex-patterns from geometry, nesting-sections from nesting. All operative TeX bodies and figure sources semantically read; no truncation in the tool outputs. Article PDF authenticated but duplicate visual not read. Production macros separately read; title/author metadata are not mathematics.

Paid operations: existence/regularity, connectedness-or-planar structure, genus/curvature bound; upper supports and two-volume ODE reduction; original-region reflection via analytic continuation; strict normal signs via constrained nodal domains; two vertex patterns; regular slicing/AC area coordinates and flux/coarea; four-vertex exclusion and first-transition three-vertex exclusion; bottom calibration controlling both strip orientations; integrated Jensen/flux gain; rigorous capped-infimum formula, outward rational arithmetic, semiconcavity and 23-interval certificate with minimum 9/100000. No internal operation is a candidate contribution.

## Directions awaiting primary comparison

Local quadratic coercivity at canonical branches, a volume-dependent crossover estimate, and perturbation of flat lattices are plausible consequences but must first be compared with the actual AFM second-variation/selection proof. A finite-perimeter global conclusion requires more than a normal graph calculation. No source symmetry is assumed on a perturbed torus.

## Evidence limitations already observed

All 13 blobs authenticated by Git blob SHA1 and SHA256. Initial strict-descendant metadata selection had 16 entries; adding the exact folder entry gives the specified 17, without another paper/version search. Lean navigation read [0,1052); its linked CubicTorus.lean [0,4136) ends in sorry. It is a comparator statement, not proved support, and no Lean build or downstream formalization is performed.

The external search tool automatically exposed an AFM dedication/frontmatter and a copyright/footer excerpt in a nonprimary HPRR search result, despite these not being requested as proof. These are accidental navigation exposures, not proof coverage. Source-driver production/title metadata were explicitly read as interface metadata, not operative mathematics. The bibliography word publisher matched a URL and was resolved as a bibliography entry, not an acknowledgement.

## Developed extension: a weak periodic Coulomb interaction (prefreeze)

The one source family remains Source354. The following is an exploratory extension of that family, not a second catalogue family. Nothing below is submitted as a substantial nominee, and no full target has been frozen. This section records actual derivations rather than a promise to invoke a selection principle later.

Let T=R^3/Z^3 with its Euclidean metric and volume one. For every measurable E, set f_E=1_E-|E|, let w_E be the mean-zero weak solution of -Δw_E=f_E, and set
\[
 {\cal N}(E)=\int_T|\nabla w_E|^2,\qquad
 {\cal F}_\epsilon(E)=P(E)+\epsilon{\cal N}(E),\quad\epsilon\ge0.
\]
All comparisons are at prescribed Lebesgue volume and modulo null sets. Define m_epsilon(v) to be the infimum over all finite-perimeter sets of volume v. No connectedness or topology restriction is imposed on competitors. AFM and Cristoferi use u_E=2 1_E-1, so their nonlocal energy is 4 N(E) and their coupling is gamma=epsilon/4. There is no unmentioned factor four in the numerical values below.

### 1. Basic compatibility and compactness

Fourier coefficients use exp(-2π i k·x). The mean-zero inverse of -Δ has eigenvalues (4π²|k|²)^(-1), hence
\[
 {\cal N}(E)=\sum_{k\in Z^3\setminus\{0\}}
 \frac{|\widehat{1_E}(k)|^2}{4\pi^2|k|^2},
 \quad 0\le {\cal N}(E)\le |E|(1-|E|)/(4\pi^2).
\]
The series is finite by Parseval. L1 convergence of characteristic functions implies L2 convergence (the squared L2 difference is the L1 difference), and therefore N is continuous under L1 convergence. More precisely, the bounded L2 operator (-Δ)^(-1) gives
\[
 |{\cal N}(E)-{\cal N}(F)|
 \le (4\pi^2)^{-1}(\|f_E\|_2+\|f_F\|_2)\|f_E-f_F\|_2 .
\]
This is enough for existence of constrained global minimizers by BV compactness and perimeter lower semicontinuity. Translation, signed coordinate permutation, and complementation preserve N and F_epsilon. Thus the geometric parameter regimes used below exist; they are not incompatible formal assumptions.

For epsilon_n→0 and v_n→tau∈(0,1), a global minimizer E_n has P(E_n) bounded by the corresponding canonical competitor. If tau is a transition, every subsequential L1 limit is an isoperimetric minimizer at tau, since N is uniformly bounded and P(E_n)≤I(v_n)+O(epsilon_n). Source354 supplies exactly the two adjacent compact orbits. At a prescribed transition, their translation/axis orbits have positive L1 separation: the distance is attained by compactness, and distance zero would identify their smooth boundaries a.e., hence everywhere, contrary to the spherical/cylindrical or connected/disconnected topology. This is only a separation fact, not a numerical estimate of that distance.

### 2. A volume-correction calculation for arbitrary finite-perimeter sequences

Fix one smooth canonical minimizer E_0 at volume tau. Write h_0 for its sum of outward principal curvatures. Choose a smooth periodic vector field X with
\[
 \int_{\partial E_0}X\cdot\nu=1.
\]
For example extend the normal smoothly from a tubular neighborhood, multiply by a cutoff, and divide by P(E_0). Let Phi_t be its flow. The volume and perimeter identities for a finite-perimeter set F are
\[
 |\Phi_t(F)|=\int_F\det D\Phi_t,\qquad
 P(\Phi_t(F))=\int_{\partial^*F}
          |\operatorname{cof}D\Phi_t\,\nu_F|\,d{\cal H}^2.
\]
They preserve the admissible finite-perimeter class and explicitly account for all interface cost.

Suppose E_n→E_0 in L1 and P(E_n)→P(E_0). Then D1_{E_n} converges weakly as vector measures, and its total variations converge weakly as positive measures. The latter follows from local lower semicontinuity plus convergence of total masses on compact T. A smooth extension N_0 of nu_{E_0}, with |N_0|≤1, gives
\[
 \int |\nu_{E_n}-N_0|^2\,d|D1_{E_n}|\longrightarrow0.
\]
Indeed expand the square, use weak convergence of vector measures for the cross term and weak convergence of total variation for |N_0|²; all three limiting terms equal P(E_0), with coefficients 1,-2,1. Orientation signs are fixed consistently with the outward normal. It follows by boundedness and Cauchy–Schwarz that
\[
 \int_{\partial^*E_n}
 [\operatorname{div}X-\nu_{E_n}\cdot DX\,\nu_{E_n}]
 \longrightarrow
 \int_{\partial E_0}\operatorname{div}_{\partial E_0}X=h_0.
\]
The last equality is the smooth first variation and the unit-flux normalization.

Uniform Taylor expansion of the cofactor expression, with error ≤C t² P(E_n), now gives
\[
 P(\Phi_t(E_n))=P(E_n)+t(h_0+o(1))+O(t^2).
\]
Similarly the volume derivative at zero tends to 1 and remains bounded away from zero uniformly for small t. If |E_n|=tau+epsilon_n s_n, s_n bounded, the intermediate value theorem supplies an exact volume-correcting t_n with
\[
 |\Phi_{t_n}(E_n)|=tau,\qquad
 t_n=-epsilon_n s_n+o(epsilon_n).
\]
No smoothing, lost boundary, or assumed graph parametrization of E_n is used. Applying Source354 at volume tau to Phi_{t_n}(E_n) yields
\[
 P(E_n)\ge I(tau)+epsilon_n h_0s_n+o(epsilon_n). \tag{VC}
\]
This computation is valid for disconnected and nonsmooth competitors as soon as their perimeter converges. It is a standard strict-BV/volume-flow operation, written out here so that it is not mistaken for a new regularity theorem.

### 3. First-order transition functional, including all competitors

At tau_1=4π/81 the adjacent types B,T have
\[
 r_B=1/3,\quad r_T=2/9,\quad I(tau_1)=4π/9,\quad h_B=6,\ h_T=9/2.
\]
At tau_2=1/π the adjacent types T,S have
\[
 r_T=1/π,\quad \text{slab width}=1/π,\quad I(tau_2)=2,\quad h_T=π,\ h_S=0.
\]
All these shapes embed; radii are <1/2. Small bounded volume changes preserve embeddedness. Cubic axis choices and translates do not change these numbers.

Let epsilon_n↓0, s_n→s, and require |E_n|=tau+epsilon_n s_n. For the renormalized energy
\[
 ({\cal F}_{epsilon_n}(E_n)-I(tau))/epsilon_n,
\]
the L1 Gamma limit is +infinity off the two canonical minimizer orbits at tau, and on orbit j it is
\[
 h_j s+{\cal N}(E_j(tau)). \tag{G}
\]
Here are the details. If the liminf is finite, pass to a subsequence realizing it. Source354's locally Lipschitz explicit profile bounds the renormalized energy below. Its finite upper bound and N≥0 imply P(E_n)≤I(tau)+O(epsilon_n). Perimeter lower semicontinuity forces any L1 limit to be an exact minimizer at tau, and forces convergence of perimeters. Equation (VC), followed by L1 continuity of N, proves the lower bound in (G). If the limit has larger perimeter, lower semicontinuity makes the renormalized liminf infinite. For recovery at any translate/axis of either orbit, take the same canonical type with volume tau+epsilon_n s_n. Its smooth perimeter branch has derivative h_j, and its N converges to N(E_j(tau)), giving equality. Null changes are immaterial.

In particular, for every finite M,
\[
 \sup_{|s|\le M}\left|
 \frac{m_\epsilon(tau+\epsilon s)-I(tau)}{\epsilon}
 -\min_j\{h_js+{\cal N}(E_j(tau))\}\right|\longrightarrow0. \tag{U}
\]
To prove uniformity, a failed assertion supplies epsilon_n→0 and bounded s_n with a fixed error; pass to s_n→s, use BV compactness for minimizers and the preceding lower bound, and use the two canonical recovery sequences for the upper bound. This is a sequential compactness proof of a uniform little-o, not an effective remainder.

If one affine value is strictly smaller, all global minimizers approach that entire type orbit in L1. A contrary sequence would have a limit in the losing compact orbit and contradict (G). At the crossing value both types survive in the limiting functional; (G) does not assert two exact minimizers at a fixed positive epsilon.

### 4. Exact Fourier formulas and signs

For a centered embedded ball of radius R and volume v,
\[
 \widehat{1_B}(k)=3v\frac{\sin t-t\cos t}{t^3},
 \qquad t=2πR|k|.
\]
This follows by integrating exp(-2πik·x) on spherical shells; the formula at k=0 is its limit v. For a tube of radius r along a coordinate circle, coefficients vanish unless the axial component of k is zero. On the remaining Z²,
\[
 \widehat{1_T}(k)=2v\,J_1(t)/t,\qquad t=2πr|k|.
\]
Integrating over the polar angle and then radius gives this expression. It can alternatively be defined directly by the absolutely convergent entire series below, so the certificate has no unverified Bessel library call.

For a coordinate slab of width v only modes on its normal axis survive. Its one-dimensional Poisson solution gives
\[
 {\cal N}(S_v)=v^2(1-v)^2/12.
\]
For completeness, put the occupied interval at [-v/2,v/2]. Its derivative w' equals -(1-v)x inside, and v(x-1/2) for x∈[v/2,1/2], with odd reflection. Thus
2[(1-v)²(v/2)³/3+v²((1-v)/2)³/3]=v²(1-v)²/12.

For a cutoff K, let a_k be the exact coefficient and
Q_K=sum_{0<|k|≤K} a_k²/(4π²|k|²),
M_K=sum_{0<|k|≤K} a_k².
Parseval gives the rigorous positive-tail enclosure
\[
 Q_K\le {\cal N}(E)\le Q_K+
 \frac{v(1-v)-M_K}{4π²(K²+1)}. \tag{PT}
\]
The integer K²+1 is valid because |k|² is an integer; for a tube the zero axial modes account for the entire three-dimensional sum. The residual is nonnegative by Parseval. This residual-tail bound is much sharper here than replacing the numerator by v(1-v).

The executable CERTIFY.py uses K=32, counts lattice modes exactly, evaluates every term by outward integer intervals on scale 10^180, and uses 241 Taylor terms:
\[
 \frac{\sin t-t\cos t}{t^3}
 =\sum_{j=0}^{\infty}(-1)^j
       \frac{2(j+1)t^{2j}}{(2j+3)!},\qquad
 \frac{2J_1(t)}t
 =\sum_{j=0}^{\infty}(-1)^j
       \frac{(t^2/4)^j}{j!(j+1)!}.
\]
No square roots are needed at the relevant volumes:
for B(tau_1), t²=4π²q/9;
for T(tau_1), t²/4=4π²q/81;
for T(tau_2), t²/4=q.
In each recurrence the ratio of successive positive terms decreases beyond the truncation and is <1. The absolute alternating remainder is bounded by the first omitted term, and the code checks that bound <10^-60. Early terms need not decrease; only the tail criterion is used. Interval cancellation is enclosed, not discarded. A separate Machin identity with odd partial sums of arctan(1/5), arctan(1/239) gives a rational enclosure of π; no floating-point sin, cos, pi, or J_1 is used in the certificate. Each elementary interval rule follows by monotonicity and floor/ceiling of integer division. The code is a reproducible finite rational calculation accompanying the analytic proof (PT), not a replacement for an inequality theorem.

The outward enclosures obtained, all endpoints exact decimal rationals, are
\[
\begin{array}{c|cc}
 &\text{lower}&\text{upper}\\
{\cal N}(B_{\tau_1})&.001995652773&.001995707068\\
{\cal N}(T_{\tau_1})&.001996177582&.001996232102\\
{\cal N}(T_{\tau_2})&.003924209676&.003924288287\\
{\cal N}(S_{\tau_2})&.003923674752&.003923674753
\end{array}
\]
The interval subtraction before coarse outward printing gives the following enclosures (inclusive endpoint versions suffice):
\[
 470514/10^{12}<{\cal N}(T_{\tau_1})-{\cal N}(B_{\tau_1})
                   <579328/10^{12},
\]
\[
 534923/10^{12}<{\cal N}(T_{\tau_2})-{\cal N}(S_{\tau_2})
                   <613534/10^{12}.
\]
Using non-strict inequalities at the printed endpoints is also sufficient; the stored high-precision endpoints lie strictly inside them.

Hence the crossings of the limiting affine energies are
\[
 s_1=\frac23({\cal N}(T_{\tau_1})-{\cal N}(B_{\tau_1}))
       \in[313676,386219]/10^{12},
\]
\[
 s_2=\frac{{\cal N}(S_{\tau_2})-{\cal N}(T_{\tau_2})}{π}
       \in[-195294,-170271]/10^{12}.
\]
In the first transition scaling, balls are selected for s<s_1 and tubes for s>s_1. In the second, tubes are selected for s<s_2 and slabs for s>s_2. Thus the limiting tube window narrows from both ends. This is an asymptotic selection statement, not an exact finite-coupling phase diagram. The very small gaps explain why a crude tail or unvalidated numerical sum would not establish the signs.

### 5. Local spectra and what primary continuation already pays

The constrained perimeter quadratic form is Q(u)=int(|∇u|²-|II|²u²). At a sphere, eigenvalues are (l(l+1)-2)/R²: the mean constraint removes l=0 and translations remove l=1, leaving a positive gap. At a length-one tube they are (m²-1)/r²+4π²k², for angular/axial integers m,k. Removing the constant and transverse translations leaves the minimum of 3/r² and 4π²-1/r², positive at r=2/9 and r=1/π. Axial translation has identically zero normal component, so it is not an extra kernel. A slab has two flat components; volume and its one normal translation remove the two constant modes, and all remaining Fourier modes have eigenvalue ≥4π². There are three axis choices, not a continuous rotation family on the fixed cubic lattice.

AFM Corollary 1.2 and the proof in §§2–4 therefore give local L1 quadratic coercivity at all four transition representatives. Cristoferi Proposition 4.3, its entire uniform proof in §4.2, and Proposition 4.16 already pay uniform local minimality and weak-coupling continuation. They address arbitrary finite-perimeter competitors via uniform penalization and improved convergence, rather than assuming competitors are graphs. Translation uniqueness must be read as equality of translation orbits: the proof yields alpha=0, and literal uniqueness of sets would contradict translation invariance. This is how the result is used here.

The new energy-gap computation can be combined with that machinery at a fixed endpoint. At tau_1, all global minimizers converge to the ball orbit, so uniform penalization (Cristoferi Lemma 2.15) and improved convergence put them in the neighborhood of the local ball continuation; uniqueness there identifies its orbit. At tau_2, all global minimizers converge to the slab orbit. A slab remains an exact critical point of F_epsilon (its potential has the same value on both boundary components), so continuation uniqueness identifies that exact slab orbit for sufficiently small epsilon. Constants remain existential. This fixed-endpoint continuation is a composition of the cited results and the signed energy comparison, not an unproved novel selection principle.

A useful localization estimate follows at a fixed endpoint after the winning orbit has been selected. The periodic Green kernel is integrable, hence N is L1-Lipschitz with some finite L (also proved as AFM Lemma 2.6 in its normalization). If d is distance to the winning unperturbed orbit and P(E)≥I+c d² there, minimality against that canonical set implies c d²≤epsilon L d, so d≤(L/c)epsilon. The c and localization radius are not numerically known from the read primary proof. No explicit global stability constant is claimed.

### 6. Shape correction and compatibility of a putative second-order claim

For research purposes the formal normal-graph reduction has also been carried out. On the volume/translation orthogonal subspace X_j, let
A_j=-Δ_{Σ_j}-|II_j|² and g_j=2 Pi_{X_j}(w_{E_j}|_{Σ_j}).
If a sufficiently differentiable local branch has
u_epsilon=epsilon u_1+O(epsilon²), differentiating H+2epsilon w=λ gives
\[
 u_1=-A_j^{-1}g_j.
\]
The constrained energy expansion would then be
\[
 {\cal F}_\epsilon(E_{j,\epsilon})
 =P(E_j)+\epsilon{\cal N}(E_j)
 -\frac{\epsilon^2}{2}\langle g_j,A_j^{-1}g_j\rangle
 +O(\epsilon^3).
\]
This comes from minimizing
(1/2)Q(u_1)+2 int w_{E_j}u_1.
It does not identify global minimizers by itself. Cristoferi's quoted continuation theorem states continuity, not this differentiability or a numerical remainder. A full proof of this displayed second-order formula would require the boundary-potential shape mapping estimates, the gauge-fixed inverse, and a justified remainder; it is retained as a prospective reduction, not asserted as proved.

The slab has g_S=0 and remains undeformed. For balls and tubes it is incorrect to keep an exactly round shape at positive coupling merely because it was minimizing at zero. A direct compatibility argument is available: if the potential were constant on the boundary of an embedded ball, its interior Poisson solution would be radial quadratic. C1 matching and harmonic unique continuation make its exterior potential radial, of the form v|x|²/6+a/|x|+b, on the connected cube-minus-ball. Periodic matching of normal derivatives on x_1=±1/2 would force that radial derivative to vanish on an interval of radii, impossible since v>0. For a tube, uniqueness makes the potential independent of its axis, and the same argument in the transverse square uses v rho²/4+a log rho+b. Thus round balls/tubes are not critical for epsilon>0. Late comparison: the actual Choksi–Sternberg first-variation proof and Remark 2.4 were subsequently read; that remark already states the noncriticality of spheres on the torus. The present elementary compatibility derivation is retained, with no novelty claim. The two-dimensional transverse version applies the same reasoning to a tube.

### 7. Strongest reduction and current boundary

The developed first-order nonlocal construction is stronger than simply substituting the profile in an inequality: it covers arbitrary finite-perimeter sequences with moving volume, writes the exact interface cost of the correcting flow, includes all adjacent symmetries at ties, and certifies a delicate lattice-Fourier ordering with rational arithmetic. Nevertheless its analytic operations are standard compactness, first variation, Fourier/Parseval, and primary local-continuation machinery. The arithmetic sign comparison is explicit but does not itself establish the requested nonroutine substantial contribution. It is not nominated by this author.

An effective finite-coupling phase diagram with explicit epsilon range and a certified transition error cannot be extracted from (U): (U) has no effective remainder, the global gap outside local neighborhoods is only a compactness gap, and the available local radii/coercivity constants are existential. The source's 9/100000 margin applies to its exact symmetric CMC endpoint configurations; a nonlocal critical surface has nonconstant mean curvature, so reusing that margin without a quantitative replacement for reflection/section identities would be invalid. The second-order branch reduction above clarifies one local ingredient but does not close this global effective obligation.

This is a prospective direction, not a frozen theorem to be narrowed later. No exhaustion of the family, no priority claim, and no mathematical grade are asserted.
