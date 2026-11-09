from pathlib import Path
import json,hashlib,subprocess,shutil
R=Path(__file__).resolve().parents[1]; P=R/'packet'; repo=R.parents[3]
def put(name,s): (P/'public'/name).write_text(s.strip()+'\n')
put('report.md',r'''
# Analytic/geometric discovery r120 — prefreeze archive

No target was frozen and no nominee is submitted. No count, gate, correctness PASS, or substantiality rating is assigned. The campaign remains the parent's responsibility. This is a record of six operative screens, with unequal depth, after a broader catalogue/history navigation pass. It neither proves that these families are exhausted nor claims worldwide priority clearance.

The fixed upstream revision is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. All its statements and operative proof operations are stipulated. The complete preprints tree was parsed and every entry traversed: 13,223 entries, `truncated=false`, 10,373 blobs and 2,850 trees. The truncated root tree was not used. AGENTS.md, upstream identity, catalogue entries, campaign requirements/history, and accepted R023–R040 findings were consulted at the reading extents in `reading-limits.md`. The separate historical sixteen and the current eighteen are not conflated.

The most developed comparison is source078's smooth homogeneous phase interface. A scale-dependent Taylor reduction absorbs a smooth remainder into an amplitude while keeping a uniformly admissible Gevrey polynomial phase. Its cap-count cost is an arbitrarily small power, which fits the source's strict-order estimate. The source's actual pseudoconformal operation and the primary Taylor/amplitude precedent remove the apparent regularity incompatibility. This is a preselection calculation, not a frozen anisotropic multiplier theorem.

For source366, finite-tip structure, local blow-up convergence and the classical crack-tip normalization give the expected exact tail coefficient by a fixed-ball superlevel limit. This uses the source's stronger local models and the primary pointwise bound, not only its weak-L4 headline. No uniform tip-count estimate or new free-boundary mechanism was constructed.

For source219, the tree stability operations accept bounded iid randomness, but finite-graph microscopic averaging and conditional centering use the continuous potential distribution. Clean-graph continuous switching was tested as the stronger alternative. Its common covariance/regular-part conjugacy does not directly survive distinct random environments. Matching environments was considered but no full microscopic conditional estimate or centering replacement was obtained. This route remains unfinished, without a claim that the full atomic-disorder question is false.

Source341's elliptic compatible-family construction already supplies local smooth closed lifts and convex patching. The endpoint proof still chooses geometric preparation data; an arbitrary external parameter family would need compatible choices throughout that construction. The earlier I80 family screen already identified that interface. Source083's pointwise maximal truncation direction is likewise an actual old unresolved target, not fresh work. Source090's strict first-shell deficit and original-cell geometry are stronger than a Gaussian minimum headline; a stationary-law variance calculation is recorded, but no new stationary or unscreened crystallization theorem is asserted.

Files: `smooth-phase.md`, `spectral-screen.md`, `geometric-screens.md`, `reading-limits.md`, and the source/primary/history/search registers. Public files contain original prose/code and metadata. Retained upstream, primary and historical bodies are private and retain their original rights. No formalization, manuscript, release, shared-index edit, git operation, nested delegation or publication occurred.

The manifest and detached FINAL/report hashes authenticate bytes and provenance only. Copied controls are not mathematical gates. There is no full candidate awaiting a correctness or contribution review from this round.
''')
put('smooth-phase.md',r'''
# Source078: smooth phase versus the actual Gevrey interface

This is prefreeze feasibility, not a candidate declaration. The constants below may depend on the fixed smooth phase, its compact slope domain, ellipticity, fixed support and the requested positive loss. There is no uniform bound over all smooth functions with only a C2 bound, no critical endpoint, and no maximal-operator assertion.

The exact pinned input is `thm:oscillatory-estimate` in `12-multiplier.tex`: for a two-dimensional input and three-dimensional output, the L3 estimate has decay lambda^(-1+nu), for every nu>0. Its derivative identity is partial_v Phi= zeta(v,x-cv), with symmetric uniformly definite partial_p zeta and fixed Gevrey Hessian bounds. The rest of that file actually performs the radial slicing, pseudoconformal substitution, globally definite Hessian extension, spatial binning, shell expansion and strict-order interpolation. These are stipulated operations, not new constructions to claim here.

Consider a fixed smooth function g on a neighborhood of a compact slope patch, with positive definite Hessian bounded above and below. Work with a smooth compactly supported convolution phase

    h(y',t)=t g(y'/t),       0<c<=t<=C.

Negative definite Hessians are handled by the permitted sign convention, but no sign variant is a separate candidate. The exploratory question was whether a merely smooth g leaves a genuine obstruction to the source's Gevrey phase contract.

Fix small epsilon>0 and let rho=lambda^(-epsilon). Partition the compact slope set into O(rho^(-2)) caps. For a cap center q0 and a fixed input third coordinate y3, divide y' into squares of side rho. Write

    y'=y0+rho v,   z'=y0+t q0+rho X,   t=z3-y3,
    Lambda=lambda rho^2.

The support for a cap forces X,v into fixed bounded sets (enlarging bins a bounded number of times). At each fixed t, output bins have bounded overlap. Taylor's affine terms separate into input and output factors of modulus one. The remaining phase is

    Lambda t G_rho((X-v)/t),
    G_rho(q)=[g(q0+rho q)-g(q0)-rho grad g(q0).q]/rho^2.

Let P_rho be its Taylor polynomial of degree N at zero. On every fixed relevant q ball,

    ||G_rho-P_rho||_(C^j) <= C_(j,N,g) rho^(N-1)

for each fixed j. For j<=N+1 this is Taylor's remainder with derivatives; for j>N+1 the polynomial derivative vanishes and rho^(j-2)<=rho^(N-1). Choose N with epsilon(N+1)>=1. Then Lambda(G_rho-P_rho), including all derivatives required of the fixed smooth amplitude, is bounded independently of lambda and q0. Thus exp(i Lambda t(G_rho-P_rho)) belongs in that amplitude. This is a derivative estimate for the whole residual factor; merely bounding its value would not suffice.

The quadratic part Q of P_rho has the original uniformly positive Hessian. On a fixed larger ball the remaining polynomial has C2 size O(rho). Extend by

    Q + chi(P_rho-Q),

where chi is a fixed compactly supported Gevrey cutoff equal to one on that ball. For sufficiently small rho its Hessian remains uniformly positive everywhere. Because N is fixed after epsilon, its higher derivatives have one uniform Gevrey envelope, depending on N and g but not lambda or q0. The finitely bounded remaining lambda range is controlled directly. This avoids assuming a global smooth convex extension of the original g with uniform Gevrey derivatives.

Set s=1/t and Z=X/t. The phase becomes s^(-1)P_rho(Z-sv). Differentiating in v yields -grad P_rho(Z-sv). An affine normalization of the compact s interval gives the source x-cv form (a fixed v-dependent translation inside zeta is allowed). Jacobians are bounded on c<=t<=C. The source estimate at scale Lambda therefore applies to every bin, with uniform constants for this family of phases and amplitudes.

The input Jacobian contributes rho^2. The physical transverse L3 factor rho^(2/3) cancels the input rescaling rho^(-2/3). Thus a bin has norm bound

    C rho^2 Lambda^(-1+nu)
      = C lambda^(-1+nu) rho^(2nu).

Bounded overlap sums bins for each cap without an additional power of rho. Triangle inequality over O(rho^(-2)) caps gives

    C lambda^(-1+nu+2epsilon-2epsilon nu).

For any requested eta>0 choose positive epsilon,nu with 2epsilon+nu<eta, then choose N as above. Minkowski in the bounded y3 interval is the same source slicing step. The full smooth homogeneous phase calculation therefore fits a lambda^(-1+eta) strict-loss bound. None of the constants is independent of eta or the selected high derivatives of g.

The closest primary proof read was Guo–Oh–Wang–Wu–Zhang, *The Bochner–Riesz problem: an old approach revisited*, [2104.11188v1](https://arxiv.org/pdf/2104.11188v1): §2 performs slicing and pseudoconformal reduction; Lemma3.8 rescales the phase; Lemma3.10 uses a Taylor remainder as a uniformly smooth amplitude and Fourier expands that amplitude. Their exact theorem is not asserted to be this entire smooth phase statement. Their actual operations supply the relevant compatible compiler precedent, while the stronger pinned estimate supplies the exponent.

Chronology matters: the initial Taylor feasibility calculation preceded the full Lemma3.10 read. That primary comparison was completed before selection; no freeze occurred at any point. The all-strict-order multiplier shell summation is already a source operation, but this round does not present a complete new general-convex multiplier theorem or claim every stationary-phase interface was independently developed. A smooth-phase headline alone does not identify an unpaid integrated operation after the displayed reduction. General variable phases without this homogeneous difference structure, rough curvature, maximal and critical-order estimates are not consequences claimed here.
''')
put('spectral-screen.md',r'''
# Source219: an atomic-disorder route that remains unfinished

No full target was frozen. The exploratory scope was fixed bulk energy, fixed degree and genuinely atomic bounded weak iid potentials on random regular graphs, with the full microscopic GOE point process as the intended question. A smoothened, averaged-energy, subsequential or delocalization surrogate is not substituted for that question.

The October5 pinned companion `01-introduction.tex` states its full result for uniform potentials on [-w,w]. Its complete `02-tree.tex`, especially `prop:tree-stability`, proves stability using a disk coordinate X=(g-q)/(g-qbar), one-leaf contraction, a mean multiplier bq^2 bounded away from 1 in the bulk, an iterated fluctuation contraction, and independent bad-leaf estimates for inverse imaginary-part moments. The inspected estimates use bounded iid input and weak disorder, rather than a density at this stage. This makes the tree input a credible compatible reduction for a two-point law. It is not itself a microscopic finite-graph theorem.

The density is used later in two distinct operations.

* `03-local-law.tex` begins with finite-matrix spectral averaging for independent uniform diagonal entries. It supplies a Wegner bound E Tr 1_I<=C_w n|I|, compression tails and the averaged Ward estimate at microscopic scale. Tree inverse moments do not automatically provide this finite-matrix statement. Smoothing atomic variables by noise of width epsilon incurs density constants of order epsilon^(-1), so taking epsilon to zero after a fixed-noise n limit does not establish the intended atomic result.
* `04-marked-entropy.tex`, `lem:conditional-mean`, eliminates a coherent environment-dependent eigenvector mean. It changes every V_v by t b0(V_v). One-site chi-square error O(t^2) gives product total variation O(sqrt(n)t), while a shift interval of length n^(-2/3) and the averaging identity kill the microscopic coherent component. For a two-point law, such shifted product measures are generally mutually singular. An independent global eigenvector sign only symmetrizes a mixture; it does not make the conditional spatial empirical law centered in every limiting environment. That shortcut therefore does not reproduce the actual contract.

The strongest alternative was explicitly checked: the clean regular-graph manuscript's `prop:continuous-switching` in `05-switching.tex`. Its discrete edge-switch identities and Gaussian invariance turn conjugated permutation matrices into small-angle continuous rotations. This is not dismissed merely because the graph moves discretely. In the clean setting the covariance C_k and regular part K_k commute with Q_U=diag(U,U). That exact common-block invariance pays the conjugacy. For different random environments the conditional Gaussian blocks have different covariance and regular part; a generic orthogonal mixing does not preserve their law. Whitening the vectors changes the physical switching matrices as well and is not the same insertion identity.

The October5 `07-insertion.tex` instead uses a root-excluded event on which c(v),a(v) are bounded, pairs intervals of length ell, and obtains D=+/-ell under a measure-preserving switch. With beta=cD/(1+aD), opposite intervals cancel the first-order drift, leaving E beta=O(ell^2), variance O(ell^2), s1=O(T), s2 comparable to T and max|beta|=O(theta), for T=r theta^2. A two-point flip has fixed size and does not directly supply that small-angle triangular array. A smooth positive density can plausibly be handled by the usual conditional-CDF pairing, but no complete all-proposition extension was established here and it would not address atoms.

Matching finite-depth environments before applying the clean rotation is a possible structural idea. It still requires uniform control of microscopic conditional covariance/regular parts as depth grows and a replacement for conditional centering. Neither was derived. This is the exact stopping point, not a proof that every atomic-disorder method fails.

Primary comparison was deliberately limited. Anantharaman–Sabri [1704.02765v1](https://arxiv.org/pdf/1704.02765v1), introduction and Theorems1.1–1.2 setup, has a Hölder-continuity assumption on the potential distribution and averaged quantum ergodicity for suitable tests. It excludes the atomic case in that contract and is not a fixed-energy microscopic point-process theorem. Its full proof was not read. He–Huang–Wang [2610.08127v1](https://arxiv.org/pdf/2610.08127v1), introductory result/setup, concerns clean random regular graphs. Its later proof chain was not read; no priority clearance or asserted disorder transfer is based on it. The full clean switching proof operation used above comes from the pinned companion, not this unread primary proof.

This is an exact-gap archive. No conditional bridge is promoted as a result, no numerical experiment is used, and no changed law or weaker conclusion is nominated.
''')
put('geometric-screens.md',r'''
# Further geometric and analytic screens

These are preselection records. The calculations below are not frozen candidates or independent correctness/contribution decisions.

## 366: crack-tip superlevels

The pinned `completion.tex` proves `cor:classification`, completes `thm:main`, and observes that endpoints/triple junctions are relatively closed and discrete, hence finite on compact subsets. Its `cor:weak-l4` uses the full local-model equivalence of De Lellis–Focardi, not merely an unspecified integrability theorem. `reductions.tex` supplies the exact SBV/reduced-minimizer interface for the bounded fidelity problem.

The stronger primary input is De Lellis–Focardi [2308.14660v2](https://arxiv.org/pdf/2308.14660v2), Proposition2.5.6 and its first-variation proof: the half-line profile is b sqrt(r) sin(theta/2), up to rotations, signs and additive constants, with b^2=2/pi. Thus |grad U|^2=1/(2pi r). Theorem6.1.6's proof gives |grad u(x)|<=C dist(x,{tips})^(-1/2) near the finitely many tips and bounded gradient away from them, including triple-junction neighborhoods. Theorem2.2.3 and its setup provide local convergence off the limiting crack; AppendixD Step3 explains the ordinary elliptic convergence there. Only the beginning of AppendixD was read, not its complete compactness proof.

The feasibility calculation uses this stronger interface. Fix a tip p and scale r=t^(-2). On fixed rescaled balls, t^(-1) grad u(p+t^(-2)y) converges, along every convergent blow-up subsequence, off the limiting half-line to grad U. The limiting half-line and the level circle |grad U|=1 both have planar measure zero. The pointwise estimate confines the original t-superlevel set to a ball of radius C^2 t^(-2) around p. Dominated convergence of indicator functions on this fixed rescaled ball gives

    t^4 area({|grad u|>t} near p) -> pi(1/(2pi))^2 = 1/(4pi).

No common limiting orientation is necessary: all possible rotations/signs have the same radial gradient magnitude. The subsequence criterion therefore gives the unrestricted t limit. Continuous compactly supported tests localize to finitely many tips, so the compatible measure calculation is

    t^4 1_{|grad u|>t} dx  ->  (1/(4pi)) sum_(interior tips p) delta_p

vaguely in the interior. A slightly larger compact neighborhood handles tips near the support boundary. A test vanishing at a boundary tip contributes zero by continuity. The corresponding log-truncated fourth moment has coefficient 1/pi per tip by layer cake, with the truncation convention fixed before using that observation. It is not a uniform estimate over minimizers.

This calculation preceded any selection and no target was frozen. It is the classical distribution-function transfer from the source's finite-tip regularity and the primary normalized asymptotic. It leaves no identified new compatibility operation. The old I122 quantitative tip-count question remains a different question: finiteness depending on a minimizer gives no polynomial or uniform bound in the data. Nothing here changes that question, creates a uniform rate, or handles variable coefficients.

## 341: actual compatible families versus the endpoint choices

The October7 `05-families.tex`, `lem:compatible-family`, already constructs smooth closed lifts by the elliptic inverse G_v=(L_v+H_v)^(-1)(I-H_v), the correction D_v=dd*G_v+H_v, and a convex partition of unity in the external parameter. This pays a genuine parameter-dependent exactness operation. Simply asking for a smooth family of compatible forms would repackage that construction.

The complete `11-endpoint.tex` uses a primitive null class F, rotates the cohomological basis, prepares a fibration and auxiliary data, chooses one sufficiently small epsilon, solves the appropriate Kähler/Yau steps, and joins compatible tamers along the path. The source introduction also already obtains individual Kähler forms in the relevant positive classes and the smooth K3/T4 classification. The earlier I80 geometric-flows report discusses the genuine family/equivariant issue. A free finite group action descends to the quotient within the relevant hypotheses; a general nonfree action or arbitrary compact parameter family requires compatible geometric preparation throughout. The local elliptic lemma does not select that preparation. This round constructed no such global family mechanism. The September main file was only an input map, not a fresh reading of every earlier proof section. No parametric theorem is asserted or frozen.

## 083: the actual old maximal question

The pinned introduction puts sup_epsilon OUTSIDE the L2 norm. It includes deterministic packet subcollections and Hilbert-valued bin estimates, not arbitrary output-dependent selectors. Actual r65 `flow-route.md` and r67 `selected-diagonal-status.md` were read. The old straight-segment maximal question has an unresolved diagonal-selected short-scale piece; it is not a fresh target for r120.

Lacey–Li [0704.0808v1](https://arxiv.org/pdf/0704.0808v1), Theorem1.18 statement and the proof of Lemma4.25, was checked. The fixed-kernel/packet estimates and its footnote concerning the missing suitable maximal function do not license an unnoticed supremum interchange. The flow route has a classical one-dimensional maximal transform after straightening a flow with controlled Jacobian, but comparing actual straight segments with flow curves costs O(t^2) displacement and can be order one at high transverse frequency. That method obstruction does not refute the original maximal question. No restart of its frozen target occurred; acquired reduction/assembly bodies not semantically needed were removed.

## 090: a stationary variance calculation, with explicit limits

The full Gaussian-transfer section supplies `prop:density-lp` and `lem:gaussian-duality`: a common radial Schwartz minorant f, Fourier positivity, and triangular direct/dual contact. The atomic companion's `prop:global-signs` has a strictly positive deleted-jet margin on the first left half-cell (greater than .032 before the positive normalization). With s=(sqrt(3)/2)|x|^2, this is the actual source operation behind I134/I137's first-shell quadratic gap q=G-f>=c_alpha(1-s)^2 for s<1. It is stronger than knowing only the optimum energy. I137's original-cell deficit and finite-window signed-measure-square arguments were read, including their square-density/subsequence limitations. Its old stationary/Palm warning is not adopted as a theorem of impossibility.

Here is the compatible probabilistic calculation tested. For a stationary simple intensity-one point process N with finite Gaussian pair energy per unit area, E N(Q)^2 is finite for a fixed unit square Q because G is bounded below on Q-Q. Translation invariance and Cauchy–Schwarz then bound mixed second moments of any two unit cells uniformly. Hence every Schwartz kernel is absolutely integrable against the expected pair measure, by summing cell displacements.

For a large square D, the signed finite measure (N-dx)|D has nonnegative f-energy by Fourier positivity. Taking expectations, dividing by |D|, and passing to the limit using the preceding cell bounds yields

    E sum_(x in N intersect Q) sum_(y in N,y!=x) f(x-y)
       >= fhat(0)-f(0),                 |Q|=1.

The cross/background terms converge to their integrals by stationarity; the pair boundary weights tend to one and are dominated by the summable Schwartz envelope. If the expected Gaussian pair energy equals the triangular value fhat(0)-f(0), subtraction and q>=0 show that the expected q-pair sum is zero. Countable windows therefore give no pair at distance below a=(sqrt(3)/2)^(-1/2), almost surely, using the strict first-shell gap. This calculation handles the expectation interface at this explicitly finite-energy Gaussian contract. It is not an unscreened Riesz/Coulomb equality theorem.

The remaining passage from stationary maximal-density hard-core packing to an almost sure single triangular lattice has the familiar saturation/Voronoi equality route: stationary saturation must preserve the relevant intensity comparison, mean side count is controlled by planar boundary errors, and equality in the polygon area bound forces hexagons. This round did not complete a fresh, fully specified stochastic saturation/mass-transport proof or read the closest primary for that entire passage. It therefore does not assert a new stationary crystallization theorem. The source's stationary minimizing-field construction and long-range screening appendix were not freshly read. They must be checked before any later claim involving renormalized energy. A mere stationarity restriction of an old rigidity question would not establish contribution.

The circle-packing companion main was inspected only for its actual input map and periodic-equality abstract; its proof sections were not acquired. That abstract is navigation, not a cleared comparison or a proof premise. No lattice candidate was frozen, no finite test was treated as proof, and no claim of exhaustion follows from this screen.
''')
put('RIGHTS.md','''# Rights and scope

`public/` contains original r120 prose and code, plus bibliographic/provenance metadata. `private/` contains pinned upstream, external primary, and historical research bodies retained for internal semantic comparison. Those bodies retain their respective original rights; inclusion here does not relicense them or authorize publication. This packet has not been uploaded or published. No external contacts were made.
''')
print('wrote notes')
