# Family375: finite index and the missing density localization

Myeongjin Kang; no affiliation. Original prose CC BY4.0. Research checkpoint, not a manuscript or a claim of a new classification.

## Status and exact prospective operation

No target was frozen and no result is nominated. The screened statement was the energy-free finite-index classification for the quartic Allen–Cahn equation in all dimensions 4 through 7. Its essential missing operation is an automatic bound

    sup_{R≥1} R^(1−n) E(u;B_R) < ∞

for an entire solution u:R^n→(−1,1) of Δu=u³−u with finite Morse index, 4≤n≤7. Here E(u;Ω)=∫Ω (|∇u|²/2+(1−u²)²/4).

The full statement is already formulated as Conjecture E in Florit-Simon, arXiv:2602.03136v1. His Theorem1.2 supplies the finite-index classification under the displayed energy bound and an appropriate stable finite-density classification premise. The pinned family375 stable theorem supplies that premise. This substitution is a technical deduction, not a campaign nominee. The newer Liu–Luo–Wang–Wei–Wei–Wu arXiv:2610.08499v1 independently retains the energy bound in Theorem1.3 and Corollary6.8. Neither source's finite-index argument removes it.

The pinned theorem and all its lower operations are stipulated true. The issue here is extending their hypotheses, not auditing their correctness. No result in dimensions5–7 is asserted as a substitute for the unproved 4–7 operation.

## Valid qualitative deductions

Let 4≤n≤7 and let u:R^n→(−1,1) be a smooth entire solution of finite Morse index. Write

    Q_u(f)=∫ (|∇f|²+(3u²−1)f²).

1. There is R0<∞ such that Q_u(f)≥0 for every compactly supported smooth f in R^n\B_R0. Otherwise select successively negative tests outside balls containing all previous supports. Their supports are disjoint, so Q is negative definite on their span. This contradicts finite index. This standard operation is also explicitly used at (6.2) in the newer primary paper.

2. For every sequence z_j∈{u=0} with |z_j|→∞, a subsequence of u(z_j+·) converges smoothly on compact sets to an entire stable solution v with v(0)=0. Boundedness and elliptic estimates give the subsequence; every fixed compactly supported test eventually lies outside B_R0, and stability passes to the limit. If n<7, the constant extension v(x,y)=v(x) is stable in R7: apply n-dimensional stability to each y-section and add the nonnegative y-gradient term. The pinned R7 theorem classifies that extension as a planar heteroclinic; its independence of y forces the planar direction to lie in R^n. Thus every such limit is g(e·x), where g(t)=tanh(t/√2).

Consequently, uniformly along escaping zeros, |∇u|→1/√2 and the zero-set second fundamental form tends to zero. Every fixed-radius window around an escaping zero approaches a single planar interface after rotation, in every fixed C^k topology. This is uniform qualitative convergence: failure of uniform convergence would give a sequence contradicting the preceding compactness argument. It supplies no rate as a function of |z| and no convergence on windows whose radii grow with z.

3. Put U=g^(-1)(u), q=1−u², and D=1−|∇U|². Modica's inequality gives D≥0. On escaping zeros, D→0. For the pinned penalized reach

    d(z)=inf_{y∈{u=0}, y≠z} |y−z| Γ(|ν(z)·(y−z)|/|y−z|),

where Γ≥1 and Γ(s) is comparable to 1/s, one also has d(z)→∞ along escaping zeros. Indeed, a bounded reach sequence has approximating chords of bounded length. Chords bounded away from zero tend to tangent chords of the limiting plane, making their angular penalty diverge. For chord lengths tending to zero, the single-graph representation and C² convergence give |ν(z)·(y−z)|≤ε_j|y−z|² with ε_j→0. The penalized chord is then at least c/ε_j. Both cases contradict bounded reach. This conclusion again supplies no comparison between d(z), |z|, and the isolation radius used by the source.

These are standard compactness deductions from the stipulated theorem. They do not prove an energy bound, finite ends, quantitative curvature decay, or a finite-index classification.

## Exact compact-core stability remainder

Choose smooth ξ=sin θ and ζ=cos θ, with θ=0 on a neighborhood of B_R0 and θ=π/2 outside a larger fixed ball B_R1. Then ξ²+ζ²=1 and the IMS identity is

    Q_u(F)=Q_u(ξF)+Q_u(ζF)−∫(|∇ξ|²+|∇ζ|²)F².

The first term is nonnegative by exterior stability. Since 3u²−1≥−1, the second is bounded below by −∫ζ²F². Hence for a finite constant C depending on the chosen core,

    Q_u(F) ≥ −C ∫_{B_R1} F².                       (A)

There is also an exact useful scalar identity. Direct differentiation gives

    (−Δ+3u²−1)q = −q²D,
    Q_u(qη)=∫q²|∇η|²−∫q³Dη².                    (B)

For η supported outside B_R0 the left side of (B) is nonnegative; for a general η, (A) gives a compact remainder. Thus the stability defect is controllable in a fixed compact set, but the effect of that remainder on the source's global fourth-moment argument still needs estimation.

Constant extension of a finite-index solution is not a license to invoke global stability or finite index in R7. If u has a negative test f, take f(x)η_R(y−y_j) in R^(n+k). The quadratic form is

    Q_u(f)∫η_R² + (∫f²)∫|∇η_R|².

For R sufficiently large this is negative because the gradient-to-mass ratio is O(R^−2). Arbitrarily many disjoint y-translates give infinite index. What does extend is (A), as the cylindrical inequality

    Q_{u(x)}(F) ≥ −C∫_{B_R1×R^(7−n)} F².         (C)

This distinction is essential for any argument using the source's ambient dimension7 calculations.

## First unpaid interface: stable isolation balls

The pinned reach calculation obtains a bounded-density window at radius

    h(z)=d(z) exp(−C sqrt(log(K(d(z))+1))),
    K(t)=1+sup_x M_t(x),  1≤K(t)≤1+Ct.

The stress-tensor/delayed-monotonicity part of this construction does not itself use global stability. The subsequent isolation and derivative estimates do use stable regularity on that window. Florit-Simon's local Theorem2.12 states the relevant kind of hypothesis explicitly: stability on the containing ball, bounded normalized energy there, and a small ε/r ratio. The source's corollary in 02-finite-density.tex is applied to an entire stable solution.

For finite index, the ball B_h(z) is known stable only if it avoids the core (or the core cylinder after extension). The qualitative statements above show d(z)→∞ but do not show h(z)<dist(z,core), even up to a fixed admissible fraction. Truncating h at the distance to the core changes the derivative estimates used in the reach differential inequality. Replacing d by such a truncated length also introduces an artificial branch and its boundary/contact terms. Those modifications have not been proved here. No error estimate below silently assumes this localization issue is solved.

## Second unpaid interface: fourth-moment error at dimension4

The source in ambient dimension7, interface dimension m=6, proves

    Y_R:=∫_{Σ_g} χ_R²(a⁴+D²+E²)+N_R ≤ C K(R)R². (M1)

Here a=|A|, E=exp(−κd), N_R is its rough-point count, and χ_R is an exponential spatial weight. The full growth proof was read. Its closure uses A⁴, D² and E²; in particular, t³f(t)² smallness turns the large-ad curvature source into a⁴, followed by the interface defect comparison and Young's inequality. It does not state a lower-power moment estimate that can simply be substituted at dimension4.

The radial argument sets

    L=R/sqrt(K(R)),   θ=.02,   A_R=K(R)L^(1−θ),

and bounds curvature sources on a shell ρ≈s by

    C K(s) exp(C sqrt(log(K(s)+1))) s^−2
      (L+log s)^(3−θ).                              (R4)

The read proof identifies the underlying operation exactly: multiply the shell fourth moment by φ=ρ^−4 and bound W_*d³ by C(L+log s)^(3−θ). This is also used for curvature at receiving feet. Under (M1), its sum divided by A_R is controlled by a subpolynomial factor in K divided by K, which tends to zero.

Now consider the naive attempt to absorb (C) solely as a scalar additive loss in (M1). For a core centered at the origin, its weighted cylindrical volume is O(R^(7−n)). Even granting all other localization steps, suppose the resulting estimate were only

    Y_R ≤ C K(R)R² + C R^(7−n).                    (D)

This is a conditional test of the proposed proof interface, not a proved finite-index version of M1. In dimension4 the extra shell allowance is C s³. Feeding that allowance through the very same φW_*d³ step produces the extra bound

    C s^−1 (L+log s)^(3−θ)

apart from the non-improving subpolynomial factor. Already its first-shell bound at s≈R, normalized by A_R, is of order

    R^−1 L² / K(R) = R/K(R)².                     (E)

The source hypotheses allow K(R) to diverge as slowly as log(2+R); for that formal growth profile (E) does not tend to zero. This is a failure of the proposed upper estimate to prove negligibility. It is not a lower bound on an actual error, not a construction of an Allen–Cahn solution with this K, and not a disproof of the conjecture.

For n≥5 the same particular volume power fits inside the R² allowance. That arithmetic alone does not pay the isolation-ball problem, the source/receiving-foot localization, or every use of the global surface stability test. No classification in dimensions5–7 follows here. No reduced-dimensional target was frozen after discovering (E).

A direct n-dimensional redevelopment could avoid literal cylinder lifting, but would need its own weighted radial constants and localized moment estimates. It is not justified merely by relabeling the ambient dimension in a proof whose radial constants use m=6. A logarithmic core cutoff, a growing excluded core, or a lower-power curvature moment could conceivably improve the remainder; none is established in this packet. Qualitative decay at infinity by itself gives no rate strong enough to replace the missing estimate in (E).

## Why the closest primary finite-index proof does not supply the estimate

Liu et al, §6, starts from exterior stability (6.2), but at (6.5) explicitly obtains finite D_∞ using the assumed energy bound (1.6). Bound (6.6) then gives finite mass for blowdowns. Lemmas6.1–6.3 obtain planar/conical limits and complete sheeting. Only after those steps does (6.16) give |x||A|+|x|²|H|≤C. Lemma6.5 upgrades graph heights to logarithmic growth, and Lemma6.6 controls interaction and profile errors by r^−2 and r^−4 polylogarithmic terms. Proposition6.7 applies an exterior scalar/Toda contradiction using these quantitative inputs. It correctly avoids the compact unstable core in its tests, but it does so after bounded-density blowdown and graph construction, not before.

Florit-Simon's Theorem1.2 and its proof likewise start within the bounded-energy class. Thus the newer scalar operation cannot be fed only the qualitative planar limits established here. The missing density/quantitative graph step would otherwise be used to prove itself.

## Disposition

There is a concrete unpaid operation, with two explicit interfaces: isolate the growing stable windows and localize the fourth-moment/radial comparison with a genuinely negligible core remainder in the critical dimension4 case. Neither is completed. The screen does not establish a new classification and makes no contribution verdict about an unproved theorem. The bounded-energy implication and the qualitative compactness lemmas are antecedent/technical material. No acceptance increment, publication, or formalization is requested.
