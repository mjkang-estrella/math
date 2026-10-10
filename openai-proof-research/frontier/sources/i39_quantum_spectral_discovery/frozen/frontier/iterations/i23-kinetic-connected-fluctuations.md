# I23 — Connected fluctuations for finite-duration interactions

Research date: 2026-10-09. Accepted premise: every proof in `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` is true. **Disposition: scoped gap after two constructive attempts; no full Gaussian theorem is established.** This is not a proof-acceptance or significance-acceptance record.

The first attempt constructs an exact whole-trajectory polymer identity and proves a normalized bound for a single positive physical component, keeping its multibody dynamics intact. It also supplies a non-overcounted finite tree extraction. The unresolved step is their compatibility with the signed, layered resummation needed on a general regular kinetic interval. The second attempt truncates scattering parameters and replaces completed scattering arcs by their actual outgoing rays. It works for a fixed finite isolated history but does not justify fluctuation-normalized cutoff removal. A stronger repulsive class gives a useful multibody virial estimate, proved below, but still does not close that removal.

These results neither disprove the proposed limit nor merely repeat that two-body delays are long. In particular, **P already proves multibody first-contact translation charts**, strong actual-witness bounds, and exponential completed-history summability. The gap identified here is a compatible *normalized connected representation with summable constants*, not the absence of those inputs. I20's no-seed mixture, Poisson window, and contact-lens coefficient are not resubmitted. Cold-jet selection and I21/I22 are outside this assignment.

## 1. Sources and precise target

The [original I23 brief](../sources/i23_kinetic_connected_fluctuations/full-brief.txt), complete I20 report and its original brief, current ledger, instructions, upstream pin, catalogue and complete inventory are frozen in the [input manifest](../sources/i23_kinetic_connected_fluctuations/input-manifest.json). The inventory has 749 manuscripts, rather than the older catalogue's count. Its kinetic-name companion screen is retained. The 23 retained H/P source files are independently checked against Git blob identities and SHA-256 in the [pinned manifest](../sources/i23_kinetic_connected_fluctuations/pinned-manifest.json). Only this selected material was copied; the 9,340-file cache was not copied or edited.

Write **H** for `preprints/Hard-sphere-fluctuations-on-the-regular-Boltzmann-lifespan-September-23-2026`, and **P** for `preprints/The-Boltzmann-Grad-limit-for-stable-radial-potentials-on-regular-kinetic-intervals-September-23-2026`. References below to sections mean their actual `build/sections/*.tex` files, not catalogue summaries. [Contracts and read passages](../sources/i23_kinetic_connected_fluctuations/reading-contracts.json) identify the exact retained passages used.

Fix a radial potential `Φ(q)=φ(|q|)`, zero for `|q|≥1`, in P's `pre:potential`: either `C²(R³)` or `C²(R³\{0})` with repulsive divergence at zero, and stable with constant B:

`Σ_{i<j} Φ(q_i−q_j) ≥ −Bp` for every p-particle configuration.

The potential is fixed as ε tends to zero. Space is **R³**, not a torus. The dynamics are

`ẋ_i=v_i`, `v̇_i=−ε⁻¹ Σ_{j≠i} ∇Φ((x_i−x_j)/ε)`.

Fix a smooth nonnegative probability density f₀ satisfying P's spatially summable Gaussian bounds for f₀ and ∇ₓf₀ (smoothness here is a harmless strengthening of P's C¹ assumption). Fix `[0,T]`, independently of ε, with a nonnegative classical probability solution f of `∂ₜf+v·∇ₓf=Q_Φ(f,f)` and `sup_[0,T],x,v e^{2β|v|²} f<∞`. No equilibrium or smallness condition is imposed. P's `pre:envelopes` supplies uniform spatially summable Gaussian bounds for f and its spatial gradient on this interval.

Set μ=ε⁻². The **initial** law is exactly

`Pε(N=n,dZₙ)=Zε⁻¹ μⁿ/n! · ∏ᵢf₀(zᵢ) · 1_{|xᵢ−xⱼ|>ε, i≠j} dZₙ`.

It is the excluded product-activity ensemble, not the Gibbs measure for Φ. Subsequent evolution allows overlaps, finite-duration encounters, attractive clusters and recollisions. The expected particle number is asymptotic to μ; it is not identically μ.

For every fixed finite list of real `φ_j∈C_c^∞(R⁶)` and deterministic `t_j∈[0,T]`, the target is joint Gaussian convergence of

`ζε(t_j,φ_j)=μ⁻¹/²[Σ_i φ_j(z_i(t_j))−EεΣ_i φ_j(z_i(t_j))]`.

Centering is the exact microscopic expectation, not `∫f_t φ`. No path tightness, shrinking tests, varying potential, or ε-dependent observation times are included.

Use P's actual scattering map. For `g=v−v_*`, the impact parameter b lies in `g⊥`, `|b|<1`, with ordinary disk area `d²b`. Set

`Δ_Φφ=φ(x,v′)+φ(x,v_*′)−φ(x,v)−φ(x,v_*)`,

where the outgoing pair is the genuine two-body scattering output, including all branches. The proposed drift and noise are

`A_tφ=v·∇ₓφ+∫ f_t(x,v_*) |g| Δ_Φφ d²b dv_*`,

`C_t(φ,ψ)=½∫ f_t(x,v)f_t(x,v_*) |g| Δ_Φφ Δ_Φψ dx dv dv_* d²b`.          (1)

The initial covariance is `∫f₀φψ`, with no fixed-particle-number subtraction. The factor ½ counts unordered interacting pairs once. P's `pre:operator` proves reversibility and the normalization `|n·g|dσ(n)=|g|d²b`; the disk has area π. Differentiating P's weak quadratic operator yields precisely the displayed drift, because its two differentiated factors cancel the ½. Collision invariants have zero Δ; the form C is positive semidefinite. These are checks on the *candidate target*, not a derivation from the gas.

If U(s,t) is the backward propagator of A, the target covariance is

`∫f₀ U(0,t)φ U(0,s)ψ + ∫₀^{min(t,s)} C_r(U(r,t)φ,U(r,s)ψ)dr`.          (2)

H's Gaussian-target construction is based on Gaussian energy bounds and integrable collision flux, and suggests the same construction here. The missing microscopic argument below is required even if (2) is independently constructed. A formal covariance formula alone is not a fluctuation theorem.

## 2. What the accepted proofs do and do not supply

H, `06-sharp-asymptotics.tex`, `thm:sharp-cumulants`, proves for its **hard-sphere pasted process**, with finite records, `||c_h^ε||TV≤C_h μ^{1−h}`. Its `04-cluster-expansion.tex`, `lem:marked-regrouping`, `lem:diagram-labels` and `thm:marked-expansion` supply the exact connected representation and remove large complexity before using this sharp bound. In particular, the independent one-root factors are resummed without changing the global components, and record projection commutes with the expansion. In bounded complexity, the difference between slab label count and fresh-label count is bounded. The factorial denominator therefore changes by only a fixed polynomial. H's normalized majorant is

`C_K(1+n)^{d_K}(CT/√L)^n`.                                             (3)

The exponential base is independent of the complexity threshold and fixed moment order. This distinction is part of the theorem, not optional bookkeeping.

P has stronger interfaces than a qualitative Lanford limit:

* `cell:expansion` gives exact finite Boolean/generation kernels for **whole** interacting components. `cell:factorization` includes every detached and reference path in its avoidance condition. Its factorial coefficient is `μ^m/m!`; there is no extra partition of all root labels.
* `cent:definition` centers only isolated singleton slots and retains nonsingleton polymers intact. `cent:cancellation` is an exact simple-family cancellation. `cent:charges` and `cent:pin-forest` distinguish algebraic ownership from geometric pins.
* `hist:gaussian` preserves augmented volume and pays for stability **once**: source energy S gives `Σ|v_active|²≤S+2Bp`. Departed components retain their potential energy. The source does not identify S with terminal kinetic energy.
* `hist:pinning` already integrates intact finite-duration groups by endpoint pins or `ε²|(v_i−v_j)·ω|dt dω`. The changes are triangular and use no derivative bound for a many-body flow. Repeated internal contacts do not have to be enumerated. Its fine original-parent charts preserve exponential counting; its coarse global charts cost `p^{Cp}` and are used with extensive geometric gains.
* `hist:basic` retains original-parent sums, a common Gaussian, the time simplices `b^{n_j}/n_j!`, and mesh gains for multiple insertions. `close:summability` gives, for any requested a, `Σ_{|Γ|=p}∫|wΓ|≤e^{−ap}` once p is large relative to the top-root number. Its choice of rarity constants is independent of the polynomial label-cap exponent.
* `close:tails` gives **actual-process** bounds `P(B_j(D_j))≤e^{−8D_j}` and physical/centered remainder norms `R_j≤e^{−8K_j}`, with polynomial-logarithmic thresholds. `exp:finite` gives fixed-size vanishing of unprescribed contacts and interference, and explicitly includes multiple top roots.

Those actual-witness and remainder estimates are already smaller than any prescribed fixed ε-power after their schedule. They are not the obstacle identified here. On the other hand, neither P's centered array `E_π` nor its simple-family charge count is the factorial cumulant `c_h`. Singleton subtraction eliminates independently evolving singleton families; cumulant inversion must cancel **all proper partitions of the observed roots**, including two nontrivial subfamilies. Naming both operations “centering” does not identify them.

A direct use of P's `exp:finite` is also insufficient: a contact between two top roots is negligible in its unnormalized conclusion but is precisely a leading-order event after division by ε². Its proof integrates the available relative translation to get a small tube volume; the fluctuation proof must extract that volume and retain the resulting contact law.

For a bounded scalar mark `y_i=Σ_j a_j φ_j(z_i(t_j))`, let F_h be the factorial record measure normalized by μ⁻ʰ and

`c_h=Σ_{π∈P([h])} (−1)^{|π|−1}(|π|−1)! ⊗_{B∈π}F_|B|`.

The exact factorial-to-ordinary identity is

`κ_k(Σ_i y_i)=Σ_{π∈P([k])} μ^{|π|}∫c_|π| ∏_{B∈π} y_B^{|B|}`.          (4)

Thus the required TV bounds make each term O(μ), and yield normalized higher cumulants `O(μ^{1−k/2})`. Covariance also needs both the same-particle diagonal F₁(y²) and the connected term μc₂(y⊗y). This explains why every fixed h, projection of records, and exact centering matter.

An explicit logical test: let an artificial Cox cloud have random intensity `μ(1+εR)`, R an independent fair sign, and independent particle locations with density f. Its normalized factorial laws converge to `f^⊗h`; `c₂=ε²f^⊗2` is at the requested scale. But `c₄=−2ε⁴f^⊗4`, instead of O(ε⁶). Its centered particle-count fluctuation tends to an independent standard Gaussian plus R. This is **not the prescribed initial ensemble or a counterexample to the proposed gas theorem**. It disproves the inference from chaos and correctly scaled pair covariance to Gaussianity.

## 3. Construction A: entire components, exact cancellation, and root gains

### 3.1 Exact whole-trajectory polymer identity

At first avoid every layer cut. For a finite label set A, evolve precisely those labels by the true potential flow on `[0,T]`. A is a dynamical polymer if its **ever-contact graph** is connected: an edge means the distance becomes at most ε at some time. Its internal trajectory retains every simultaneous interaction and repeat encounter. Initial coordinates also satisfy internal exclusion. For two polymers on disjoint labels define

`a(A,B)=1{their separately evolved trajectories come within ε during [0,T]}`.

An overlap in this definition does not exert a force between the separate polymer flows. Let `Y(A)` be the sum of the fixed single-particle record marks on that polymer. Give it the unnormalized activity measure

`dν_{ε,λ}(A)= μ^{|A|}/|A|! · 1_initial-exclusion · 1_connected · exp(λY(A)) ∏_{i∈A}f₀(z_i)dZ_A`,

interpreting the measure on unlabelled finite phase arrays, or equivalently with the displayed factorial divisors. The exact unnormalized generating partition function is

`Zε E exp(λΣ_i y_i)=Σ_{k≥0}1/k! ∫ ∏_{j=1}^k dν_{ε,λ}(A_j) ∏_{j<ℓ}(1−a(A_j,A_ℓ))`.   (5)

**Proof.** For each finite initial cloud, its actual ever-contact components form a unique partition. Different components exert no cross force, so their restricted paths are their isolated flows. Conversely, mutually avoiding isolated polymers give exactly those components in their union. Initial cross exclusion is included in avoidance at time zero. The record observable is additive under this decomposition. Label allocation produces the factorial factors in (5). At each fixed total particle number the identity is finite. For complex λ its absolute sum is bounded by the positive initial sum with weight `exp(|λ|M_obs N)`, at most `exp(μe^{|λ|M_obs})`. Thus the positive polymer decomposition and its complex marked version are actual identities, not formal approximations. ∎

For a fixed list of polymers, connected Mayer inversion uses

`u_k=Σ_{G connected on [k]} ∏_{e∈G}(−a_e)`.

Choose a total edge order. Every connected graph has a unique minimum spanning tree T. If Q(T) contains the non-tree edges later than every edge on their T-path, the graphs with that minimum tree are exactly `[T,T∪Q(T)]`. Hence

`u_k=(−1)^{k−1}Σ_T ∏_{e∈T}a_e ∏_{e∈Q(T)}(1−a_e)`,

and `|u_k|≤Σ_T∏_{e∈T}a_e`. Each tree has coefficient at most one. This is an exact finite, non-overcounted extraction, the same combinatorial identity used in H. Taking the logarithm of (5) yields its connected expansion **formally coefficientwise in μ** near zero; asserting absolute convergence at μ=ε⁻² still needs an estimate. It is not supplied by formal logarithms or by the finiteness of Zε.

### 3.2 A complete positive-component estimate with multibody dynamics

Here is a limited estimate that can be proved without imposing a two-body-only rule. It isolates a part of the missing mechanism which *does* work.

Let `p≥h≥1`. Define the positive measure on h observed records by pushing forward

`μ^{p−h}/(p−h)! · 1_initial-exclusion · 1_{p-particle ever-contact graph connected} · f₀^⊗p dZ_p`

under the p-particle isolated flow. Denote it M_{p,h}^ε. It is **one unnormalized physical-component activity**, not the full gas's h-particle cumulant. There is C, depending on the Gaussian/spatial input bounds and B but not p,h,T,ε, such that

`||M_{p,h}^ε||TV ≤ ε^{2(h−1)} C^p p^{h−1} T^{p−1}`.                 (6)

The p=h=1 interpretation is a bounded mass. Increasing C accommodates all small p cases. In particular, for fixed h the sum of these positive component bounds converges when CT<1. We make no such assertion for a general prescribed large T.

**Proof.** Begin at time zero with p separate translation groups, since the initial exclusion holds. Compute each group's own physical flow. At the first contact between different groups, record its time and touching pair, choose the pair lexicographically if necessary, and merge the groups. Continue with the true isolated dynamics on their union. Do not split an ever-connected group again and do not enumerate its internal encounters. A connected p-particle trajectory has exactly p−1 mergers.

Before a merger, its groups have independently translatable histories `X_A+q_i^A(t)` and `X_B+q_j^B(t)`. With all preceding internal coordinates fixed, the contact determines their relative translation by

`X_B−X_A=εω+q_i^A(t)−q_j^B(t)`.

Its determinant is `ε²|(v_i(t)−v_j(t))·ω|`. Earlier pin variables enter only off-diagonal blocks. The component dynamics are translation equivariant; curvature and arbitrarily many internal encounters therefore do not change this determinant. Retain the indicator that this is the first cross-group contact, so multiple crossings are not counted as different realizations. The area formula on regular flow domains and then exhaustion handles singular potentials and zero-flux contacts, just as in P's `hist:pinning`. One overall translation remains. All p source velocities remain independent coordinates. This yields ε^{2(p−1)} and the ordered time simplex of volume T^{p−1}/(p−1)!.

For the speed sum, put `E₀=Σ_i|v_i(0)|²`. On every admissible partial branch, all initial potentials are zero, and every genuine merger is made where cross potentials are zero. Conservation and stability give `Σ_i|v_i(t)|²≤E₀+2Bp`. This includes already interacting groups. At a node of the discrete merger-choice tree,

`Σ_{i<j}|v_i−v_j| ≤ p^{3/2}(E₀+2Bp)^{1/2}`.

Sum child weights at that node, then recurse. Future realizability restrictions can be discarded after retaining this energy gate; no energy inequality is claimed for an invalid off-domain reconstruction. Consequently the sum of products of the p−1 incoming fluxes is at most `[p^{3/2}(E₀+2Bp)^{1/2}]^{p−1}`. Angular integration costs C^{p−1}. The deterministic merger construction supplies the selected pair lists directly; it introduces no extra partition count or ordering permutation.

Write `f₀(x,v)≤g(x)e^{−β₀|v|²}`, with g bounded and integrable as provided by the Bol norm. Integrate one g in the common translation and take the spatial supremum of the others, costing C^p. Retaining half the Gaussian and using `sup_{u≥0}u^k e^{−cu}≤(k/(ce))^k` gives

`∫ e^{−β₀E₀}(E₀+2Bp)^{(p−1)/2}dV_p ≤ C^p p^{(p−1)/2}`.

Before normalization the connected integral is therefore bounded by

`ε^{2(p−1)} C^p T^{p−1} p^{2(p−1)}/(p−1)!`.

Multiplication by `μ^{p−h}/(p−h)!` extracts exactly ε^{2(h−1)}. Finally `(p−h)!≥p!/p^h`, `(p−1)!=p!/p`, and `p!≥(p/e)^p` bound the residual factorial ratio by `e^{2p}p^{h−1}`. Absorb e² in C. Projection to any bounded record observable cannot increase the mass. ∎

This is a source-relative technical component estimate, not an independently reviewed new fluctuation theorem. It demonstrates explicitly that finite-duration multibody motion need not destroy the root-gain Jacobian. The loss in the full proposal occurs at a later representation/summation step.

With s physical initial spanning links in a compatible connected history on p particle lives and h roots, the dimensional bookkeeping would similarly be

`μ^{p−h} ε^{2(p−1−s)} ε^{3s}=ε^{2(h−1)+s}`.                         (7)

But (7) requires that the links and dynamic mergers belong to one compatible representation. It is not permission to impose p−1 independent pins on an arbitrary product of P's signed terms.

### 3.3 Why this does not close the regular-interval problem

First, (5) uses whole `[0,T]` dynamical polymers. Its natural tree estimate has base CT, and its components can contain long sequences of well-separated binary collisions. Finite-duration control does not shorten the macroscopic history. BGSS's physical-trajectory cluster paper explicitly restricts its corresponding expansion to small time. Replacing T by T/L in (6) and multiplying layers would require independent input factors at every cut. The actual input is correlated. P resolves that problem for chaos by its singleton/reference cancellation, but that cancellation has not here been lifted to the connected Mayer expansion of (5).

Second, P deliberately anchors all top roots together in `hist:pinning`: they are fixed output coordinates, not asserted dynamically connected. Its fine estimate pays for p−h extra-label pins. To obtain (7) one must pin the additional h−1 relative root translations while retaining:

1. the exact root-partition cumulant cancellation on **all displayed** trajectories;
2. P's whole-component energy budget and restored cut-pattern indicators;
3. the original-parent summation, independent-source factors and fresh-label factorials;
4. the factorization under record projection and under global-component splitting.

P's factorization holds on cross avoidance of every displayed path; avoidance only between paths in the full physical cloud is insufficient. A detached path belongs to a different force prescription and can contact a family that the full physical path avoids. Consequently the actual physical contact graph cannot alone be used as the dependence graph of all the signed terms.

I tried taking the original rooted forests and adding just h−1 root bridges. The graph-rank count is correct, but it does not prove preservation of the chronological charts. Even with two fixed roots and p−2 new labels, every new label can have its original-factor contact with root 1 later in backward time than an earlier virtual contact with root 2. The original-parent forest then differs from the global-earliest-contact forest on p−2 edges. There is no combinatorial bound on this difference depending only on h. This is a finite contact-record diagnostic, not an asserted realizable gas counterexample. P recognizes the issue: `cent:pin-forest` and `hist:coarse-chart` reserve such global rerouting, with its full p^{Cp} cost, for an extensive-defect estimate. An arbitrary rerouting does not receive a gain automatically.

The repair tested was to divide terms into extensive defects, where P's exposure mechanism pays the coarse count, and few defects, where a bounded modification might preserve the fine chart. “Few” in P means a small fraction of p, whereas H's polynomial loss in (3) uses **bounded complexity independent of p**. P's completed histories can contain many carried slots or qualitatively small residual inputs. Its proof uses factors `γ_ε^{θp}` with `γ_ε→0` and no required rate. I did not construct a complexity filtration and marked factorization that both extracts ε^{2(h−1)} and leaves a majorant of type (3). Invoking H's hard-sphere `thm:marked-expansion` for those new potential histories would assert the missing result.

The exact unresolved claim for construction A is:

> Represent the marked factorial cumulants of P's gas, modulo remainders negligible after μ^{h−1}, by compatible connected completed histories Γ, with independent sources and intact force groups, and prove `Σ_{|Γ|=p} μ^{h−1}∫|wΓ|≤A_{h,p}` for an ε-independent summable sequence A_{h,p}. Within those coordinates, prove the normalized extra-contact and nontrivial-initial-link sums vanish, and identify the one-/two-root limits.

No such representation with this bound is proved here. In particular, I do not extrapolate the positive-component estimate (6) to the signed layered cumulants.

## 4. Construction B: scattering truncation and uniform removal

Choose a velocity bound M, a compact regular scattering set K, a microscopic duration bound D and a positive separation δ between finitely many scheduled encounter times and record/cut times. For fixed history size p, choose K as in P's `pre:scattering` so the nonzero velocity increments are bounded away from zero. Force-free passages are crossings, rather than discarded zero-increment scatterings. On K, isolated two-body entrance and exit maps are regular and have duration at most D. An isolated arc has physical duration at most εD and displacement at most `C_M εD`. Collapsing it to its **actual** outgoing velocity is justified at fixed p,K by continuity of the scattering flow and a finite induction over the tree. Derivatives enter a finite constant `C_{p,K}`; they are not asserted uniformly bounded as p or K changes.

Before the first interfering event, all relevant displayed histories are such isolated arcs and rays. For fixed p,K, P's `exp:finite` gives the unnormalized smallness of interference, but the connected normalization requires the event measure **in the root-merger coordinates**, not its original unnormalized estimate. In a proposed normalized tree representation, a time separation strip has an O_{p,K}(δ) measure and the event/record displacement tends to zero as εD→0. Those conditional statements explain how a finite-tree limit could work; they do not supply the absent normalized representation.

P's first residence-time moment supplies the valid, cutoff-free isolated-event estimate

`∫|H(t+ετ_*)−H(t)|dν ≤ Lip(H) ε ∫τ_*dν`, `ν={|g|≤M} incoming flux`.  (8)

This is more useful than a mere tail probability, but it concerns one isolated event with its own incoming flux measure. It does not bound the law of a component already selected by a root-connection constraint or an overlapping encounter.

### 4.1 Two limit-order stress tests

**History-size tails.** P's `e^{−ap}` bound alone is not a normalized dominating sequence. Let ε_n=2⁻ⁿ and, for fixed h≥2, let a nonnegative artificial history weight have its only nonzero term at `p_n=2(h−1)n`, of size `2^{−p_n}=ε_n^{2(h−1)}`. It obeys the exponential tail with a=log 2. Every fixed-p normalized term is eventually zero, yet the total normalized mass is exactly one. Choosing instead p_n=n gives a divergent normalized total for h≥2. These are exact counterexamples to the proposed domination inference, not examples of gas histories.

Discarding `p>A log(1/ε)` directly using the exponential tail can be made small after a **fixed** fluctuation normalization by choosing A large. But it leaves all growing sizes below that threshold. Fixed-p constants then are insufficient. For example, with a proposed error `ε exp(bp)` and tail `exp(−ap)`, choosing p=q log(1/ε) requires `q>2(h−1)/a` for the normalized tail and `q<1/b` for that illustrative error. Neither existence of these bounds with compatible constants nor their uniformity in the cutoffs follows from P. This example diagnoses a missing estimate; it does not prove that every cutoff schedule fails.

**Centering the delay error.** If bounded per-label observation errors have expected absolute size O(ε), their total error divided by √μ is only O(1). Exact centering does not turn this into o(1). To see the logical issue exactly, take N=μ deterministic along integer μ and errors `d_i=εR`, the same centered fair sign for every label. Each has size ε and mean zero, but `μ⁻¹/²Σ_i d_i=R`. Thus an O(ε) isolated-event estimate cannot by itself transfer the fluctuation law. Independence would give a much smaller variance, but the needed weak dependence is precisely the connected estimate under investigation.

A valid sufficient transfer for a proposed truncation is, for every fixed scalar observation list,

`μ⁻¹ Var(S_true−S_truncated)→0`.                                     (9)

Alternatively, if a number-preserving comparison agrees with the true gas outside a **global** event of probability `O(ε^{1+η})`, the initial factorial bound and Hölder give

`μ⁻¹/² E|S_true−S_truncated| ≤ C_q ε⁻¹ P(event)^{1−1/q}→0`

for `q>(1+η)/η`, just as H's exact-centering lemma. P's superpolynomial actual-witness bounds can pay for their own stopping errors. They do not bound the global event that *some* ordinary finite-duration encounter is modified by the scattering-collapse approximation. A per-encounter flux cutoff is a different event, involving a gas with order μ encounters over kinetic time. I did not prove (9) or a sufficient global coupling for the collapse.

The unsuccessful repair was to send the fixed scattering cutoff to its full value after the ε-limit, relying on `ν(K^c)→0`. This is valid for a fixed isolated history after obtaining a normalized integrable majorant. It is invalid before that majorant: multiplying an unnormalized discarded mass by μ^{h−1} can remove its smallness. Choosing an ε-dependent cutoff instead requires explicit bounds on scattering-map and history constants. P's qualitative nondegeneracy modulus does not assert such bounds, and the full stable class supplies no suitable general rate here.

## 5. A meaningful repulsive restriction, and what it repairs

The following is a genuine deterministic multibody estimate, stronger than treating each isolated pair separately. It does not require Gibbs equilibrium. It also does not solve the cumulant problem.

Assume in addition that Φ is nonnegative and, for some fixed s≥2,

`−rφ′(r)≥sφ(r)` for `0<r<1`.                                        (10)

This is a stronger assumption, not a consequence of stability or monotonicity. There are nonzero finite-range potentials in P's class satisfying it: for example

`φ(r)=λ r^{−s} exp(−1/(1−r²))` for `0<r<1`, and zero for `r≥1`,

with λ>0 fixed. This is C∞ away from its repulsive singularity at zero, is flat at the range boundary, and has stability constant zero. Its logarithmic derivative gives `−rφ′/φ=s+2r²/(1−r²)²≥s`. The finite-diagnostic rational example `φ=(r⁻²−1)^4` is C³ at the boundary, hence meets P's C² requirement and obeys `−rφ′/φ=8/(1−r²)≥8`.

**Virial proposition.** Evolve an isolated group of p≥2 particles under such a potential. Let

`E_rel=½Σ_i|v_i−v_cm|²+Σ_{i<j}Φ((x_i−x_j)/ε)>0`

be its conserved relative energy. The set of times during this isolated evolution at which its instantaneous distance-ε graph is connected is contained in an interval of length at most

`ε(p−1)^{3/2}/√E_rel`.                                               (11)

**Proof.** Set `I=Σ_i|x_i−x_cm|²=(1/p)Σ_{i<j}|x_i−x_j|²`. Differentiating twice along the exact multibody dynamics, with `r_ij=|x_i−x_j|/ε`, gives

`I″=4K_rel−2Σ_{i<j} r_ij φ′(r_ij) ≥4K_rel+2sU≥4E_rel`.

This uses every pair potential and has no binary-isolation approximation. If the instantaneous graph is connected, its diameter is at most `(p−1)ε`, so `I≤M=(p−1)^3 ε²/2`. Strong convexity and I≥0 imply that the sublevel interval `{I≤M}` has length at most `√(8M/(4E_rel))`: apply the midpoint convexity inequality to any two points in it. Substitution gives (11). The connected-time set lies inside that interval, even if it is itself disconnected. ∎

For a two-particle incoming encounter, `E_rel=|g|²/4`, and (11) gives duration at most `2ε/|g|`, uniformly in impact parameter. This avoids the head-on angular-momentum cutoff for this stronger singular repulsive class. For a group begun from separated independent Gaussian-velocity sources, the singularity `E_rel⁻¹/²` is locally integrable in the `3(p−1)` relative-velocity dimensions. That observation concerns the independent source measure; it does not assert integrability under every selected merger constraint.

There is a reason for the stronger assumption. Smooth **bounded** monotone repulsive potentials need not have uniformly bounded two-body duration at bounded nonzero incoming speed. Take

`φ(r)=λ exp(−r²/(1−r²))`, `r<1`, and zero outside.

It is smooth, radial, positive, and strictly decreasing for 0<r<1, but has a maximum λ at the origin. At zero angular momentum and incoming relative energy λ, the radial speed is `2√(λ−φ(r))∼2√λ r`, so reaching the origin takes infinite microscopic time. By continuity on any fixed finite portion of that orbit, arbitrarily long residence occurs on nearby positive-flux parameter neighborhoods. This does not contradict P's finite **flux first moment**; the exact trapped incoming set has zero flux. Monotonicity alone does not give the uniform bound that a naive scattering truncation would use. PSS already controls repulsive durations with an angular-momentum cutoff, and Le Bihan also uses such scattering control; (10) is an explicitly narrower class.

What (11) repairs is the lifetime of a fixed isolated, instantaneously connected component. It does **not** bound the duration of an ever-contact cluster: a particle can encounter another, travel an order-one distance, and encounter a third. Nor can it simply be summed across changing memberships: external particles exchange energy, and the relative energy of the chosen subset is not conserved while cross forces act. P avoids illegal cuts by keeping whole components intact; a connected cumulant construction must do the same.

I tested applying (11) to the “multiple-addition” and “incomplete-passage” errors of construction B. On a fixed isolated block with a relative-energy cutoff it gives an explicit O(ε) episode length, and can replace a qualitative two-body delay discard. But it does not control the number, weights, or dependence of such blocks after root-merger conditioning; cutting at a fixed observation/layer time may also meet an ongoing group. Removing the energy cutoff uniformly under the normalized connected history measure is an additional obligation. No completed regular-interval Gaussian theorem is therefore claimed even for (10).

The narrowed target still allows a spatially localized, anisotropic Gaussian input and any supplied fixed nonequilibrium regular classical interval; it does not change the input into a Maxwellian Gibbs law or let T shrink with ε. Restricting T to a perturbatively short interval would change the requested regular-lifespan bridge and would not establish the missing long-interval mechanism.

## 6. Covariance identification, cycles, and the remaining acceptance gates

For a fixed compatible binary **tree** with compact scattering parameters, the finite-duration limit uses the scattering map in (1), not the hard-sphere reflection. After the one-root evolution is identified, joining two root branches by their last common contact and adding the diagonal produces the candidate source `½ f f_* |g| Δ_Φφ Δ_Φψ`. The factor can be checked directly by expanding the product of the two pair increments. It vanishes for collision invariants. These checks determine the plausible covariance; they do not show that all normalized two-root histories converge to it.

The Gaussian statement still requires all of the following, jointly on a single microscopic law:

* the marked connected representation and summable bound specified in §3.3 for every fixed factorial order;
* normalized negligibility of extra contacts and nontrivial initial links, including overlapping finite-duration groups and signed auxiliary paths;
* identification of the one- and two-root record limits, with the same-particle diagonal, as (2);
* exact-centering transfer of whatever comparison process is actually used, proved via its own event or variance estimate.

The initial law itself is not an obstacle: it is exactly H's ensemble, so H's initial factorial domination, `||c_{h,0}||₁=O(ε^{3(h−1)})`, initial Gaussian law, and particle-number moment bounds apply unchanged. They do not supply the dynamically generated connected gains. A bound before extracting ε^{2(h−1)}, a limit at each fixed p, or knowledge of c₂ alone does not meet these gates.

## 7. Fresh primary-literature comparison

Current unversioned arXiv landing pages and pinned full PDFs were retrieved on 2026-10-09; identities, response bytes, SHA-256, and extracted text are in the [literature manifest](../sources/i23_kinetic_connected_fluctuations/literature/manifest.json). Read-passage contracts retain the theorem statements, rather than relying on abstracts. Queries and tool retrievals are retained separately. They establish the following scope comparison, not worldwide novelty.

[Le Bihan, 2408.03597v2](https://arxiv.org/pdf/2408.03597v2), current revision 2026-01-08: Assumption 2.1 uses `V=χ(r)/r^s` with a decreasing finite-range cutoff. Equations (2.4)–(2.9) define a stationary **grand-canonical Gibbs** ensemble in a periodic box. Theorem 1, (2.15), is a quantitative **two-time covariance** estimate against the linearized collision equation, with restrictions on α, mean free path, θ, and T; subsequent results address grazing/long-range scalings. It is not an arbitrary nonequilibrium full Gaussian law, and does not authorize replacing the excluded product activity. The earlier [2212.04392v1](https://arxiv.org/pdf/2212.04392v1), still the current listed version, is a hard-sphere equilibrium covariance proof without billiard theory. These papers are relevant mechanisms but do not duplicate the target.

[Pulvirenti–Saffirio–Simonella, 1301.2514v2](https://arxiv.org/pdf/1301.2514v2), current revision 2014-01-04: §8, Hypothesis 1′ and Theorem 1′ (the extracted text renders primes as zeroes), cover stable smooth potentials, including attractive parts, at **short times**, with their initial-hierarchy hypotheses. The repulsive case includes explicit convergence estimates and Lemma 1 controls scattering duration by angular momentum. These are kinetic-chaos results, not the normalized cumulant theorem sought here. The present positive-component calculation and virial restriction are not claimed to supersede their short-time results.

[BGSS, 2008.10403v2](https://arxiv.org/pdf/2008.10403v2), current revision 2022-08-25: equation (1.3.1) already uses **exact first-marginal centering**; Theorem 2 proves nonequilibrium **hard-sphere process** fluctuations on a short interval. Its initial law is grand canonical with exclusion. [BGSS, 2205.04110v1](https://arxiv.org/pdf/2205.04110v1), the only version listed, develops the physical-trajectory polymer representation; Proposition II.6 gives the absolutely convergent dynamical cluster expansion for small time. Remark II.7 explicitly identifies its time restriction. Identity (5) and its tree-graph algebra are extensions of that standard representation to the available intact smooth-potential flows; they are not presented as a new substantial mechanism.

[BGSS, 2201.04514v1](https://arxiv.org/pdf/2201.04514v1), the current listed version, Theorem 1.3 proves the all-time **hard-sphere equilibrium Gaussian process** limit in periodic dimension at least three. Its proof exploits the invariant equilibrium measure; the paper distinguishes higher-moment convergence from covariance convergence. The initial ensemble and invariance argument do not apply to the target here.

The complete pinned manuscript inventory identifies H and P as the relevant regular-lifespan companion pair; it does not contain a separately titled smooth-potential regular-lifespan Gaussian theorem in the kinetic-name screen. Primary searches did not locate an exact theorem with all of our hypotheses and conclusion. That is a bounded search result, not proof of absence. No count, worldwide priority, or acceptance claim is made.

## 8. Diagnostics and handoff

Run from the repository root:

```sh
python frontier/experiments/i23_kinetic_connected_fluctuations/diagnostics.py
python frontier/experiments/i23_kinetic_connected_fluctuations/verify.py
```

The exact diagnostics check the minimum-spanning-tree partition and tree bound for 1,099 finite edge-activity graphs through five vertices, 338,350 normalization exponent identities, 3,240 positive-component factorial bounds, and 3,160 rational virial inequalities. They also check the Cox fourth-cumulant example, normalized-tail escape arrays, and cutoff exponent conditions. The 1,099 count happens to match I20's graph count, but these test different identities. None certifies an analytic estimate, dynamical realization of the rerouting graph, or the full Gaussian law. No simulation is used as proof.

The seal covers only this report and the assigned I23 source/experiment trees, excluding the seal itself and its derived verification output. Verification separately reports any live shared-index drift without changing the frozen copy or a shared file. It checks pinned source hashes against the complete inventory and all extracted contract/passages against retained bytes. Failed or unversioned retrievals are distinguished from pinned sources; the unversioned Le Bihan hard-sphere PDF is retained alongside the explicitly pinned v1 retrieval.

The handoff is the precise normalized marked-resummation gap in §3.3, with the two attempted constructions and the complete limited estimates (5), (6), and (11). These limited estimates are technical research progress and have not had independent proof review. The full candidate is **not ready** for a fresh full-theorem proof/significance acceptance round. No agents were spawned, shared index edited, staging performed, commit created, or remote changed by this assignment.
