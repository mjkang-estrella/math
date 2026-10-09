# I20 — Kinetic selection, finite seeds, and collision-scale corrections

Research date: 2026-10-09. Premise: all proofs in `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are true. **Outcome: scoped gap report; no substantial positive finding is proposed.**

Three distinct bridges were screened: microscopic selection between the cold-jet Boltzmann solutions; nonequilibrium fluctuations for stable radial potentials; and a first-order dynamical correction to the hard-sphere mean. The first is developed furthest. Its finite-seed obstruction and initial Poisson window are proved below, but the dynamical selection theorem remains unproved. The third yields an exact initial contact calculation, which explains a missing trace estimate. These elementary probabilistic and exclusion calculations are technical results, not candidates for the substantial count. No finding number is assigned.

## 1. Scope, frozen inputs, and novelty checks

The [original brief](../sources/i20_pde_kinetic_discovery/full-brief.txt) is preserved verbatim. Read `AGENTS.md`, the ledger, upstream revision, complete inventory, and I07-analysis/I12/I13/I14. The earlier failures exclude automatic inverse-energy transfer, dimension-free linear stability, qualitative-mixing CLTs, and routine coefficient changes. The current brief supersedes the frozen ledger's stale I17 status: I17 is TECHNICAL ONLY with proof PASS. Nothing here reopens I15/I17/I19, arithmetic, or the spent structural routes.

[Input snapshots](../sources/i20_pde_kinetic_discovery/input-manifest.json) freeze the actual bytes before this work. [Inventory screen](../sources/i20_pde_kinetic_discovery/inventory-screen.json) traverses the complete, nontruncated 749-manuscript inventory. The old catalogue heading reports 719; it is not used as an inventory bound. The read-only I14 cache supplied 166 selected files, independently rechecked by SHA-256 and Git blob identity against the complete inventory, then copied into this assignment's directory. [Pinned manifest](../sources/i20_pde_kinetic_discovery/pinned-manifest.json) retains every exact raw URL, blob hash, size and SHA-256. [Reading locators](../sources/i20_pde_kinetic_discovery/reading-locators.json) identify 37 decisive labels and line locations; [statement contracts](../sources/i20_pde_kinetic_discovery/statement-contracts.json) preserve 509 labelled statements. Extraction/copying is not a claim to have read or audited every statement.

The early literature check found affirmative constraints on novelty. BGSS already prove short-time nonequilibrium process fluctuations with exact microscopic centering; Pulvirenti–Simonella already separate Enskog displacement errors from correlation errors; Chen–Guo–Shen–Zhang already prove a strong-to-weak hard-sphere instability below spatial Sobolev index one. Thus merely producing instability, changing centering, or mentioning the Enskog equation is insufficient. The final selection calculation is recognizable partition-function/Poisson reasoning and is expressly not promoted because its application to the cold-jet parameters was previously unstated.

Search queries and raw results are retained in `web-search-1.json` through `web-search-4.json` and `search-log.json`. [Literature manifest](../sources/i20_pde_kinetic_discovery/literature/manifest.json) retains downloaded bytes, hashes, version-bearing text headers and retrieval dates. Two nonexistent version URLs returned 404; those response bytes remain recorded, and the actual v2 papers were subsequently retrieved. The older DHM v2 is retained, but the comparison below uses v3. Search snippets, secondary expositions, and absence of hits are not used to establish priority.

## 2. Exact accepted interfaces

Abbreviate the following complete directory names under `preprints/`; all subsequent short filenames refer to these directories.

**H:** `Hard-sphere-fluctuations-on-the-regular-Boltzmann-lifespan-September-23-2026`. In `build/sections/01-introduction.tex`, `ass:kinetic` requires a smooth nonnegative probability density on **R³×R³**, finite `Bol,2β` norms of the datum and its spatial gradient, and a nonnegative classical Boltzmann solution on a fixed finite `[0,T]` with `sup e^(2β|v|²) f < infinity`. The Bol norm sums local spatial suprema over the integer lattice. The particles start from the exactly normalized grand-canonical product activity conditioned on pairwise spatial exclusion, with `μ=ε^-2`. The kernel is `[(v-v*)·ω]_+`, integrated with ordinary sphere area. `thm:main` gives joint Gaussian convergence of exact-centered empirical observations for **each fixed finite list of times and compact smooth tests**, with Poisson initial covariance and the stated collision noise. It does not give path tightness, shrinking-test estimates, singular-data selection, or a first-order dynamical mean expansion.

H's `02-initial-target.tex`, `prop:initial` and `eq:initial-insertion`, give factorial domination by `f0^⊗h`, the exact insertion partition ratio, and the already-upstream initial mean shift

`ε^-1(F1,0^ε − f0) → −(4π/3) ρ0 f0`.

In `06-sharp-asymptotics.tex`, `thm:sharp-cumulants` gives `||c_h^ε||TV ≤ C_h μ^(1-h)` for fixed factorial order and bounded fixed observation records of the pasted process. The normalized one- and two-root measures converge to signed tree measures; cycles and nontrivial initial links are little-o at this scale. Weighted assertions concern retained diagrams, not an arbitrary microscopic remainder. `08-transfer.tex`, `lem:center-transfer`, transfers exact centering using the separately proved true/pasted discrepancy bound. None of these is a boundary trace estimate for finite-ε collision surfaces.

**P:** `The-Boltzmann-Grad-limit-for-stable-radial-potentials-on-regular-kinetic-intervals-September-23-2026`. `build/sections/01-preliminaries.tex`, `pre:potential`, permits fixed radial finite-range C² potentials, either regular at zero or diverging repulsively there, satisfying thermodynamic stability `Σi<j Φ(qi−qj) ≥ −B n`. Attractive parts and long delays are permitted. The initial law is product activity with hard exclusion, **not a Gibbs equilibrium law for Φ**. Newtonian dynamics thereafter retain simultaneous interactions. The kinetic kernel is the actual two-body scattering map in impact-disk variables. `00-introduction.tex`, `thm:main`, assumes C¹ probability input with the same spatially summable Gaussian bounds and a fixed classical regular kinetic interval. It proves all fixed factorial marginals converge in full phase-space L¹, uniformly in deterministic time. `cor:empirical` is already its deterministic-time law of large numbers.

P's `pre:duration` proves a bounded-velocity incoming-flux **first moment** of the isolated two-body residence time. `pre:scattering` supplies compact nondegenerate scattering sets and rotational marginals, not independence of outgoing velocities. `06-closure.tex`, `close:summability`, supplies exponentially summable completed histories and qualitative decay of each fixed-size centered term; `close:tails` gives strong actual-witness/remainder bounds. The missing fluctuation step must concern normalized connected retained histories, not pretend that this source lacks cutoff control.

**N:** `Nonuniqueness-with-local-conservation-for-the-hard-sphere-Boltzmann-equation-October-5-2026`. `build/paper/01-introduction.tex`, `thm:main` and `def:admissible`, give a datum on **T³×R³**, bounded in velocity support and finite in mass, energy and absolute entropy, with two distinct global entropy solutions. Both are strongly continuous in L¹; gains and losses separately have every polynomial velocity moment integrated on finite time intervals; all five local collision-invariant balances, entropy inequality, and initial traces are retained. The datum has unbounded amplitudes. The singular weight in `02-framework.tex` is `H=e^(-|v|²)<v>^-100(1+|vbar|^-q)`, `1<q<2`; an H-bound is not an ordinary Gaussian supremum bound.

The older `Nonuniqueness-for-the-periodic-hard-sphere-Boltzmann-equation-September-23-2026`, `build/sections/01-introduction.tex`, `thm:main`, lacks the new exact local momentum/energy conclusion. N is therefore the stronger relevant companion. Neither says that particle dynamics select either branch.

N uses the kernel `|(v-v*)·ω|`, twice H's collision normalization. Multiplying a solution of N by two converts its equation to H's collision convention, but does not repair space, mass normalization, regularity, or approximation hypotheses. The finite N-construction uses a **cutoff kernel** `min(1,b/|v-v*|)` and measurable spatial masks. It cannot silently be treated as a smooth uncut hard-sphere kinetic solution.

## 3. Three candidate hypotheses and early adversarial screens

### A. Microscopic nonuniversality and a critical seed window

**Proposed substantial target.** Choose one fixed small horizon from N's construction and paired dormant/cap subsequences with common limiting datum F0. Write `a_n` for the truncated cold datum plus bath, and `b_n≥0` for the selected hot seed. Find a common particle diameter sequence `ε_n→0` for which hard-sphere empirical **spacetime** observations, started respectively from the exclusion ensembles of `a_n` and `a_n+b_n`, converge in probability to the two different N-solutions (after matching the collision normalization). More ambitiously, identify a nontrivial law of branch selection when the expected seed count stays finite. For the first assertion, it suffices to find one fixed smooth compact velocity/spacetime test Φ on `[0,T]×T³×R³` whose two limiting integrals differ. We do not demand uniform convergence for every rough observable.

**Proof hypothesis under test.** Smooth/cutoff removal of each finite jet approximation, followed by the regular kinetic limit, might allow a diagonal passage to the two branches. H's fluctuations might then quantify the seed window. Neither step is automatic. Sections 4–6 prove the microscopic constraints first and state the remaining construction precisely.

**Adversarial outcome.** A finite expected seed count is incompatible with deterministic selection of a different branch: a nonvanishing no-seed component survives every common microscopic evolution. H's fixed-test Gaussian theorem cannot identify this localized finite-count population, nor does it apply to the unbounded limiting datum. A meaningful positive result would need a new many-seed kinetic approximation or a conditioned finite-seed dynamical law. That is still missing.

### B. Nonequilibrium Gaussian fluctuations for stable radial potentials

**Target, with quantifiers.** For every fixed Φ in P's class and every datum/regular interval satisfying P, establish for each fixed finite list `(tj,φj)` the exact-centered Gaussian limit of `sqrt(μ)[π^ε_t(φ)−Eπ^ε_t(φ)]`. The proposed drift is the adjoint of the linearization of `QΦ`; the proposed covariance rate is

`CΦ,t(φ,ψ) = (1/2) ∫ dx dv dv* d²b |v−v*| f_t(x,v) f_t(x,v*) ΔΦφ ΔΦψ`,

where the impact disk has radius one and `ΔΦ` uses the actual outgoing two-body velocities. Initial covariance would be `∫ f0 φψ`. No unproved collision-angle density is introduced.

**Proof hypothesis under test.** Replace H's instantaneous collision merger by P's finite-duration whole-component encounter; use the latter's stability budget and actual-witness estimates; retain factorial cancellations and recover a sharp connected-tree expansion. The required new estimate is, for every fixed h and fixed record list,

`sup_(ε small) ε^(-2(h−1)) ||c_h^ε||TV < infinity`,

with normalized cycle contributions tending to zero and the normalized two-root trees converging to the covariance just written. One needs this with a summable majorant **after** extracting the `ε^(2(h−1))` gain, plus exact-centering transfer.

**What the attempted repair actually supplies.** On a fixed bounded-velocity isolated encounter, let ν be incoming flux and τ* its microscopic duration. P gives `∫τ* dν<∞`. For a bounded Lipschitz function of a recorded event time,

`∫|h(t+ετ*)−h(t)| dν ≤ Lip(h) ε ∫τ* dν`.

It also gives `ν(ετ*>δ)≤C ε/δ`. This completely handles the delay of one isolated encounter. It does **not** control overlapping multibody episodes, repeated contacts inside an intact component, or the growth of the constant with all retained labels. H's merger proof uses independent relative translations of already built straight-segment groups; P's whole interacting components need a new compatible connected representation. Even the strong unnormalized exponential tail in `close:summability` cannot be multiplied by `ε^(-2(h−1))` and then discarded uniformly without a corresponding normalized bound.

**Adversarial validation and disposition.** Both residence-time integrability and the existing strong cutoff bounds were checked; the gap is not merely long two-body delays. Le Bihan's [v2, Theorem 1](https://arxiv.org/pdf/2408.03597v2) already treats covariance over long times for a specified smooth-potential family **at Gibbs equilibrium**, with parameter restrictions. It is neither a nonequilibrium full Gaussian theorem for arbitrary stable Φ nor permission to replace the initial law. PSS's [v2, Section 8, Hypothesis 1′ and Theorem 1′](https://arxiv.org/pdf/1301.2514v2) already handles stable potentials at short time. We found no closure of the marked normalized multi-component estimate. Candidate B is unproved, not disproved; the displayed covariance is a target, not an established extension.

### C. Determine the dynamical mean at the fluctuation scale

**Target, with quantifiers.** For every sufficiently regular f0 in H's class on a fixed regular interval, construct deterministic `h_t` and prove, for each compact smooth φ,

`sup_(0≤t≤T) | ε^-1(Eπ_t^ε(φ)−∫f_t φ) − ∫h_t φ | → 0`.

Then kinetic-centered fluctuations would be the H-Gaussian plus h. The trivial initial value `h0=−(4π/3)ρ0f0` is already upstream and earns no credit. The first trial equation was homogeneous linearized Boltzmann transport of h0; the repaired trial includes spatial Enskog terms and a contact-correlation source.

**Substantial residual bridge.** One must identify and control the order-ε collision-surface trace of `F2^ε−F1^ε⊗F1^ε`, and justify exchanging its limit with the BBGKY collision integral over the whole interval. H's bulk total-variation cumulants and qualitative negligible-cycle statements do not determine this trace or an order-ε one-root remainder. Section 7 calculates the real initial contact discrepancy and tests the homogeneous-linearization shortcut. The general repaired evolution remains unproved.

**Prior-art/adversarial outcome.** Pulvirenti–Simonella's [v2, Theorem 2.4 and Section 1.5](https://arxiv.org/pdf/1405.4676v2) already compare microscopic, Enskog and Boltzmann factorizations, with bounds of the form `ε^(γk)`. They do not give this first-order trace expansion. BGSS's [v2, equation (1.3.1) and Theorem 2](https://arxiv.org/pdf/2008.10403v2) already center by the actual first marginal. The proposed deterministic correction is not obtained by citing either result or differentiating a weak convergence theorem. No complete h-equation has been proved here.

## 4. Complete technical result: the no-seed mixture

This result is elementary and independent of any claimed new PDE theorem. It is stated for arbitrary integrable activities, so it applies directly to N's finite measurable data without falsely invoking H.

Let phase space be `X×R³`, where X is R³ or a flat torus. Fix `ε>0`, `μ>0`, and finite nonnegative integrable activities a,b. Let `P_a` be the probability law on finite unordered configurations with density proportional to

`μ^k/k! · 1_(pair distances>ε) · ∏_(i=1)^k a(zi)`;

denote its partition function by Z(a). There is no requirement that `∫a=1`. Set `δ=∫b` and `Λ=μδ`. Total variation distance means `sup_E |P(E)−Q(E)|`.

**Proposition A1.** There is a probability law R and `p0=Z(a)/Z(a+b)` such that

`P_(a+b) = p0 P_a + (1−p0) R`,

`p0 ≥ exp(−Λ)`, and `dTV(P_(a+b),P_a) ≤ 1−exp(−Λ)`.

Every common measurable evolution/observation map, including the entire trajectory map up to an arbitrary ε-dependent time, preserves the mixture and cannot increase this distance. The assertion remains valid for a common Markov transition kernel.

**Proof.** Introduce an auxiliary color on each initial particle, expanding each activity as a+b. The joint colored partition function is exactly Z(a+b), by the binomial coefficient cancelling the factorial. Let K be the number of b-colored particles. The K=0 contribution is Z(a), and its conditional uncolored law is exactly P_a. Forgetting colors proves the mixture identity.

For each fixed configuration of a-particles, discard all exclusion constraints involving b-particles. The sum of b-particle weights is then at most `Σk Λ^k/k!=e^Λ`, so `Z(a+b)≤Z(a)e^Λ`. Positivity also gives `Z(a+b)≥Z(a)>0`. These inequalities prove the bounds. A pushforward or common transition acts linearly on the mixture; its total-variation contraction follows directly by testing events (or functions in [0,1]). No stability estimate for particle trajectories is needed. ∎

The common-evolution requirement matters. Comparing an exact gas to a resampled/cutoff gas does not give this statement without an additional coupling. In the present application, both seeded and dormant laws can use the same genuine hard-sphere evolution, which is defined almost everywhere under these absolutely continuous exclusion ensembles.

**Proposition A2 (necessary infinite-seed condition).** Let `(a_n,b_n,μ_n,ε_n)` be any sequence as above. Let X_n be a common real-valued measurable observation of the corresponding microscopic path. If its dormant law converges in probability to D and its seeded law converges in probability to a different constant C, then

`μ_n ∫b_n → infinity`.

In particular, when `μ_n∫b_n→0`, the entire laws become indistinguishable, however large an unstable deterministic amplification may be.

**Proof.** An interval around D of radius less than `|C−D|/3` has dormant probability tending to one and seeded probability tending to zero. A1 bounds the seeded probability below by `e^(−μ_n∫b_n)` times the dormant probability. Hence `e^(−μ_n∫b_n)→0`. ∎

This argument concerns probabilities, not convergence of unbounded empirical expectations. Total-variation convergence alone need not compare such expectations without uniform integrability. No expectation claim is smuggled into A2.

## 5. Complete technical result: the initial finite-seed window

Set `ρ_w(x)=∫w(x,v)dv` and define

`q = μ sup_x ∫_(B_X(x,ε)) ρ_(a+b)(y)dy`.

**Proposition A3.** If q≤1, then for the initial colored law and every `0≤t≤1`,

`exp(−Λ(1−t)) ≤ E t^K ≤ exp(−(1−q)Λ(1−t))`.

Consequently, if `q_n→0` and `Λ_n→λ<infinity`, then `K_n ⇒ Poisson(λ)` and `p0,n→e^(−λ)`. If a and b have disjoint phase-space supports, then

`dTV(P_(a+b),P_a)=1−p0`.

In that disjoint case, the microscopic initial total variation tends exactly to `1−e^(−λ)`. No macroscopic dynamical selection probability is asserted.

**Proof.** Insertion of a marked particle at z gives its intensity under activity w as `μ w(z)` times the probability that the existing configuration has no center within ε of x. The intensity is at most `μw(z)`. The union bound therefore makes that vacancy probability at least

`1−μ∫_(B_X(x,ε))ρ_w ≥1−q`

for `w=a+tb`, `0≤t≤1`. Differentiating the absolutely convergent partition sum (dominated by the exponential of total activity) gives

`Λ(1−q) ≤ d/dt log Z(a+tb) ≤ Λ`.

The exact generating function is `E t^K=Z(a+tb)/Z(a+b)`. Integration proves the bounds, including t=0. These imply the Poisson generating function limit; bounded means `EK≤Λ` give tightness on the nonnegative integers, and the generating function identifies every subsequential limit. If a and b are disjoint, a physical configuration containing a point in `{b>0}` has zero P_a probability. The K≥1 residual law is thus singular to P_a, and the upper bound `dTV≤1−p0` is attained. ∎

For finite λ, suppose additionally the dormant scalar observation tends to D and the seeded laws have a weak subsequential limit ν. The mixture implies

`ν ≥ e^(−λ) δ_D` as measures.

To verify this without a boundary-set issue, test against every bounded nonnegative continuous function and pass to the limit in the mixture lower bound. Thus any alternative macroscopic branch has total probability at most `1−e^(−λ)`. Equality, existence of an alternative branch, or a two-point limiting mixture requires new dynamics.

**Why this is technical.** The proof uses the same insertion principle as H's initial ensemble and ordinary generating functions. Georgii–Küneth's [primary manuscript, Theorem 1.1 and Example 2.1](https://www.mathematik.uni-muenchen.de/~georgii/papers/FKGrev.pdf) places conditional-intensity comparisons with Poisson processes in a classical framework. We do not claim their theorem literally states A3, nor that a hard-core process becomes monotone in arbitrary activities; the explicit partition proof avoids that stronger assertion. The argument does not meet the requested nonroutine significance gate.

## 6. Application to the actual cold-jet parameters, and the missing theorem

N's `04-construction.tex`, `con:scales`, `con:jet-datum`, `con:seed`, specify

`s_N=s0 e^(−Nη)`, `d_s=d0 s^10`,

`b_N(x,v)=λ_N T_N^p s_N Σ_(n∈Λ) χ((x−n)/s_N,v)`, with `0<λ_N<L0`.

The seed exponent p is fixed by `early:exponents`; `early:cap-selection` selects λ_N. There is **no source lower bound for λ_N uniform in N or horizon**. Write `Cχ=∫_(R⁶)χ>0`. Integration over a fundamental domain gives the exact identity

`δ_N = λ_N Cχ T_N^p s_N^4`,

and hence the actual expected-activity seed scale is

`Λ_N = λ_N Cχ T_N^p s_N^4 / ε_N²`.                         (6.1)

The source's `O(s_N^4)` bound alone loses the selected λ_N and T_N factors; they cannot be discarded in a critical-window claim.

The dormant spatial density has the bound `ρ_aN≤C/s_N`. Indeed the cold supports are disjoint, each velocity profile integrates to one, `sech²≤1`, and the bath density is bounded. The seed has `ρ_bN≤C λ_N T_N^p s_N`. For sufficiently small ε_N on the covolume-one flat torus,

`q_N ≤ C ε_N/s_N`.                                            (6.2)

Thus the Poisson conclusion holds whenever `ε_N/s_N→0` and (6.1) tends to a finite λ. In particular, choosing the *initial-law* critical diameter

`ε_N = s_N² (λ_N Cχ T_N^p/λ)^(1/2)`

for a fixed λ>0 automatically gives `ε_N/s_N→0`. This is a permitted diagnostic choice of microscopic ensemble. It is not a proof that its later law follows the cap solution.

For an explicit allowed source choice, take χ supported in `|x|<1/2`. Then b_N lies inside `|x|<s_N/2`, whereas the retained jets have transverse radius exceeding s_N and the bath is absent in the fixed hole. The activities are disjoint for small s0. N only requires a smooth compact nonzero nonnegative χ and a suitable L0, so this choice is within its stated construction. A3 then yields the exact initial total-variation crossover `1−e^(−λ)` for this choice. The hard-sphere flow is reversible almost everywhere, so the full microscopic state preserves total variation; coarse empirical observations may lose information. Neither fact provides macroscopic branch separation.

**Attempted repairs and precise gaps.**

1. **Directly use H at F0.** F0 fails the ordinary Gaussian supremum hypothesis already at t=0, lies on a torus, and is not the required smooth whole-space probability datum. Small entropy, compact velocity support, and all polynomial collision moments do not remove these distinctions. No uniqueness contradiction follows.
2. **Apply the kinetic limit to each finite source approximation and diagonalize.** N's approximations solve a velocity-cutoff equation with measurable masks and a singular H-bound. To justify this repair one must construct smooth **uncut** hard-sphere kinetic approximations through the chosen common interval, prove their ordinary Gaussian bounds, and show their limits retain the selected dormant/cap branches. Smoothness of finitely many initial jets alone gives only a possibly shrinking regular interval. H/P/DHM do not provide that construction. A torus version or a controlled localization is another obligation. If all these fixed-approximation interfaces were supplied, an unspecified very small-diameter diagonal would be a routine final step, not the new discovery.
3. **Use Gaussian fluctuations as the hot seed.** H treats fixed tests with exact centering. N's seed occupies a shrinking region and its separating dilation tests depend on the scale and blow up in normalization. Moreover a fixed expected number of seed particles has Poisson, not Gaussian, statistics. No uniform shrinking-test central limit estimate or conditioned amplification law is present.
4. **Choose enough seed particles.** A2 requires `ε_N²=o(λ_N T_N^p s_N^4)` for deterministic selection of distinct branches. It is a necessary condition, not a sufficient scale relation. The collision-history constants can depend on the increasingly fine masks, velocity widths, Gaussian bounds, and regular lifespan. Neither the source cap argument nor the kinetic theorem supplies an estimate comparing their thresholds to (6.1).
5. **Claim a Poisson mixture of the two PDE branches.** A3 supplies only the K=0 component and the initial law of K. For each k≥1, one would have to analyze particle dynamics conditional on exactly k seed particles and show how they interact with a diverging cold population. The relevant limiting object might not even be one of the deterministic cap limits. The probability of any non-dormant macroscopic branch could be zero. This repair remains open.

For a precise future theorem, retain (6.1), prove a common regular approximation of the two selected branches, and establish a microscopic error estimate on at least one separating spacetime observable that tends to zero in an explicitly specified **many-seed** regime. Alternatively, derive the k-seed conditioned limit at finite λ and recombine it with the Poisson weights. No such error estimate or conditioned limit is proved here. These are gaps in this proposal, not assertions that selection or nonuniversality is impossible.

## 7. Exact contact calculation for candidate C

Here the space is R³ and all input is within H's initial-law class. Choose smooth `f0(x,v)=ρ(x)g(v)`, with g a positive anisotropic Gaussian probability density, ρ smooth compactly supported with integral one, and ρ equal to a positive constant r on an open ball. All calculations take place strictly inside that plateau, including the ε-neighborhoods used below. Let `v_ex=4π/3`.

For a measurable spatial set U consisting of one or two exclusion balls, let N_U count centers in U under the unmarked initial gas. H's insertion formula gives factorial densities bounded by products of f0, and `F1,0=f0+O(ε)f0`. The first two Bonferroni bounds give

`P(N_U=0)=1−μ∫_Uρ +O(ε²)`,

uniformly for these sets: replacing F1 by f0 in the first moment costs `O(ε)μ|U|=O(ε²)`, and the second factorial moment is at most `μ²(∫_Uρ)²=O(ε²)`. This is an analytic bound, not an independence assertion.

For one root, the ratio is `1−v_ex r ε+O(ε²)`. For two **allowed** roots at separation ε, read the exterior/incoming trace of the exact insertion formula. The excluded region for all other particles is the union of two radius-ε balls with center distance ε. Their intersection volume is

`v_lens ε³`, where `v_lens=2π∫_(1/2)^1(1−z²)dz=5π/12`,

and their union volume is `v_union ε³`, where `v_union=2v_ex−v_lens=9π/4`. Consequently

`F2,0^ε(x,v,x+εω,v*) = f0(x,v)f0(x,v*) [1−v_union r ε+O(ε²)]`,

whereas

`F1,0^ε(x,v)F1,0^ε(x+εω,v*) = f0(x,v)f0(x,v*) [1−2v_ex r ε+O(ε²)]`.

Thus the actual initial exterior contact trace satisfies

`ε^-1 [F2,0^ε−F1,0^ε F1,0^ε] → (5π/12) r f0(x,v)f0(x,v*)`.  (7.1)

The boundary value in (7.1) is an exterior trace; plugging the strict-exclusion indicator's arbitrary pointwise value at equality into the collision flux would be wrong. Formula (7.1) is the classical first excluded-volume contact correction. The lens integration and this initial-ensemble consequence are not a new substantial mechanism.

There is a direct consistency test for the homogeneous-linearization proposal. Take `φ(x,v)=ψ(x)χ(v)` with ψ supported strictly inside the plateau, and χ compact smooth. The standard incoming one-collision flux formula for the right derivative of the empirical mean uses F2's incoming contact trace. With H's normalization it is one half the integral of that trace times `[(v−v*)·ω]_+` times the two-particle change of φ. Integrating in x removes the shifted ψ factors by translation. The transport term's leading and first-order pieces integrate to zero because the density is constant on the support. Therefore its order-ε collision coefficient is

`−v_union r (∫ψ) ∫χ Q(f0,f0) dv`.

Homogeneous linearized transport of `h0=−v_ex r f0` would instead give

`−2v_ex r (∫ψ) ∫χ Q(f0,f0) dv`.

Their difference is `(5π/12)r` times the same collision observable, nonzero for some χ. Indeed an anisotropic Gaussian is not collision invariant: its positive entropy dissipation makes Q nonzero, and Gaussian decay allows detection by a compact smooth test. Thus an expansion **differentiable at the initial time with convergence of right derivatives** cannot satisfy the homogeneous trial equation. This initial-generator test does **not** by itself disprove a merely C⁰-in-time mean limit: exchanging the ε-limit and time derivative requires an estimate, and an initial boundary layer could invalidate that exchange.

The bulk-to-trace obstacle is also visible without any gas approximation. With compact smooth nonnegative velocity factors and a compact x cutoff, put on the allowed side

`r_ε(x,v,y,w)=ε A(x,v,w) η((|y−x|−ε)/ε⁴)`,

where η is smooth on `[0,infinity)`, supported in `[0,1]`, and η(0)=1. Its phase-space L¹ norm is `O(ε⁷)` (amplitude ε, sphere area ε², layer thickness ε⁴), so even `μ||r_ε||1→0`. Yet its incoming trace divided by ε is exactly A. This is a counterexample to a proposed **norm-to-trace estimate**, not a construction of consistent gas marginals. The real initial gas in (7.1) independently demonstrates that a nontrivial contact correction actually occurs.

Adding the lens coefficient to an Enskog equation is not a proof of the dynamical expansion: incoming correlations at later times depend on shared histories and can include recurrent-contact contributions. BGSS's [one-sided convergence paper, v1, Theorem 2.1 and Section 4](https://arxiv.org/pdf/1612.03722v1) already emphasizes that microscopic exceptional sets and the direction of incoming convergence matter. The unsolved part here is a uniform first-order incoming trace expansion and its propagation, not the observation that bulk convergence has no general trace theorem.

## 8. Additional PDE checks and significance limits

The optional nonkinetic source checks did not justify another candidate. The stable torus NLS manuscript's `build/main.tex`, `thm:blowup`, already gives a nonempty **H^k-open** blowup set for one sufficiently large odd power in dimension twelve, and `cor:gaussian` already gives positive Gaussian blowup probability for every `α>k+6`. Full-support transfers to other comparable Gaussian laws would repeat its mechanism. The higher-dimensional Schrödinger endpoint theorem concerns the **free Euclidean** propagator at `s_n=n/[2(n+1)]`; it cannot make nonlinear supercritical torus blowup or stability estimates available. No nonlinear endpoint bridge was established.

The eventually stationary forcing companion already provides a fixed-particle halting detector from zero initial velocity on the flat torus; the rapidly vanishing forcing companion already has a shrinking detector and explicitly no uniform precision tolerance. Simply adding such descriptions or slowing a clock is spent within those companions. No robust noisy-computation result is inferred. These were secondary rejection checks, not extra findings.

The named potential contributions were microscopic selection/nonuniversality for entropy Boltzmann solutions, a nonequilibrium full fluctuation law beyond hard spheres, and first-order kinetic centering. The report establishes none of those full claims. The no-seed mixture, Poisson window, and initial lens coefficient do not pass the substantial gate on their own. No worldwide novelty, MathDB rank, human peer review, or formal proof certification is claimed. A fresh independent proof/significance review would be appropriate only after one of the missing dynamical bridges is completed.

## 9. Reproduction and handoff

Run, from this repository:

```sh
python frontier/experiments/i20_pde_kinetic_discovery/diagnostics.py
python frontier/experiments/i20_pde_kinetic_discovery/verify.py
```

The diagnostics exactly check partition/mixture and conditional-intensity inequalities on 1,099 finite exclusion graphs, and rational lens/union coefficients. Twelve finite independent-cell examples illustrate the Poisson limit; they do not prove it. All continuum arguments are written above. The provenance script reconstructs inventory checks, exact contract extraction and source reading locators. The literature script preserves failed responses and skips already-retained URLs.

The artifact seal covers only this report and the two assigned I20 trees, excluding the seal and its derived verification output. Verification checks frozen dependency bytes separately from live shared-index drift; drift is reported, never repaired by writing a shared file. No agents were spawned; no other project, shared index, staging area, commit or remote was changed by this task.

**Parent disposition:** preserve this as a negative/technical discovery record. The best continuation is the explicitly quantified many-seed or conditioned finite-seed dynamical limit in Section 6. Do not route the elementary mixture or lens calculation alone as a substantial candidate, and do not change the accepted count.
