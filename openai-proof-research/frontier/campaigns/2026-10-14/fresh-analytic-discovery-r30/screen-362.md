# Family 362: full Schwartz-data extension remains unresolved

Author: Myeongjin Kang. No affiliation. Original prose: CC BY 4.0. Code: MIT. Third-party source bodies under `private/` are retained evidence, not release material.

## Status and unchanged target

This is a discovery checkpoint, not a candidate, proof of global existence, contribution verdict, or acceptance. Parent campaign count remains 12/20. No scope was frozen for nomination. The following full target was selected before the failures below and is retained unresolved; neither a compact-spatial-support version nor an exponential-tail version is substituted.

Use the one-species three-dimensional relativistic Vlasov–Maxwell equations in source normalization: q(v)=sqrt(1+|v|²), u=v/q, transport force E+u×B, charge ρ=∫f dv, current j=∫u f dv, div E=ρ and div B=0. For every nonnegative f0∈S(R³_x×R³_v), and every E0,B0∈C_b^∞(R³;R³)∩L² satisfying these constraints, seek a unique global smooth solution with the prescribed initial data, continuous L² fields, bounded field derivatives on every finite time slab, and f∈C([0,T];S(R⁶)) for every finite T. Uniqueness is intended within this regularity class. There is no smallness, symmetry, neutralizing background, assumed evolved-moment bound, momentum cutoff, spatial cutoff, or quantitative exponential tail hypothesis. This solution-class formulation is a research target, not a theorem obtained here.

The pinned source `introduction.tex`, `thm:global` and `eq:data`, instead assumes nonnegative C_c^∞ particle data. Fields have the same C_b^∞∩L² hypotheses. Its classical class has compact phase-space particle support on each compact time interval. The source theorem is stipulated true. We inspect which interfaces would need extension, without auditing its truth.

## Exact source interface

`setup.tex`, `eq:P-range`, `prop:increment`, `eq:bootstrap`, and the complete `closure.tex` give constants M,A,P0 depending on the datum and horizon, but not the intermediate time or admissible dyadic P. The explicit admissibility condition is P≥1024 sup q(V) over all initially supported labels and all times under consideration. For a supported receiver staying in q(V)∈[w/8,8w] on an interval of length I, the signed estimate is

    |V(t2)−V(t1)| ≤ M P sqrt(I) + A I P² log(2+P)/w.                 (1)

At successive maxima 2^n, choosing P=1024·2^n produces a lower time of order 1/n. Its divergent sum prevents finite-time escape of the bounded initial momentum support. An infinite initial support has no finite admissible P and no first finite global maximum. This failure occurs even if M,A,P0 could be proved uniform along initial cutoffs. The statement only says they may depend on the whole datum; it does not specify a uniform bounded-support-radius dependence. We have not established such uniformity by reading the entire source proof.

This is not merely notation: `direct.tex` 195–275 uses sums over source scales p≤P, including Σp p≲P, Σp p/min(p,w)≲log(2+P)+P/w, and Σp p^(3/2)sqrt(P/min(p,w))≲P²/sqrt(w). `occupation.tex` gives a bin density bound with p³, a joint energy budget, and angular ranges whose number is bounded using log P. Replacing these by sums over all p needs new weighted estimates.

`retarded.tex`, `ret:energy`, has the conserved TOTAL density

    U=(|E|²+|B|²)/2+∫q f dv,
    S=E×B+∫q u f dv,       ∂t U+div S=0,

and the positive cone flux controls both the total good field and ∫q(1−n·u)f. This is the energy available in the occupation argument. It is not an energy separately conserved for a label shell with its own field.

## Attempt 1: approximation with the field constraints preserved

Let smooth cutoffs χ_R increase to one in both x and v, and set f0,R=χ_R(x)χ_R(v)f0. Define C(ρ)=−∇(−Δ)^−1ρ. Then

    E0,R=E0+C(ρ0,R−ρ0),       B0,R=B0

has div E0,R=ρ0,R and div B0,R=0. Merely truncating f while retaining E0 would violate Gauss' law. These corrected data satisfy the compact source theorem. Since ρ0,R→ρ0 in Schwartz topology, the Coulomb corrections tend to zero in every H^s and in every bounded-derivative norm. For L² this follows directly in Fourier space: near zero, |ξ|^−2 is integrable in three dimensions and the charge difference has small L¹ norm; away from zero, Schwartz convergence controls all weighted Fourier integrals. The same split with Fourier L¹ bounds proves bounded-derivative convergence. Nonzero total charge does not prevent Coulomb fields being L² in dimension three.

This constructs global approximate solutions but supplies no uniform finite-horizon moment/field bound. Equation (1) controls each current support in terms of its own initial radius. Taking the radius to infinity is not justified by that estimate. Nor does continuous dependence on each fixed compact-data solution supply a radius-uniform neighborhood or lifespan: arbitrary Schwartz tails need not dominate an unspecified deteriorating stability constant.

Spatial localization is a separate technical issue. The source's finite-horizon modification in `continuation.tex` 285–490 writes a divergence-free vector field as curl of an explicit potential, truncates that potential outside a large ball, and retains the Coulomb part. A vacuum difference then vanishes throughout the compact particle region by finite propagation. For noncompact spatial particle data, no single such ball contains that region. A local cone/patch construction could address spatial localization, but has not been carried out here and would not resolve the unbounded momentum estimate. We do not silently replace C_b^∞∩L² initial fields by global H^s fields.

One initial boundary use of compact momentum support is harmless in isolation. In `ret:initial-boundary`, d0=1−n·u≥1/(2q²), while |n−u|≤2. Sphere area therefore gives |Ebd|+|Bbd|≤C t sup_x∫q² f0(x,v)dv, finite and cutoff-uniform for Schwartz f0. This removes only that boundary estimate; the evolving cone-tip and bulk estimates still need weighted control. It is not a nominee.

## Attempt 2: normalize momentum growth and use the primary moment criteria

On an existing regular interval define

    Λ(t)=sup_{0≤s≤t,z in supp f0} q(V(s;z))/q(v0) ≥1.

When the force is bounded on a finite slab this quantity is finite. Volume preservation and transport give, for every m≥0,

    M_m(t)=∫q(v)^m f(t,x,v) dx dv ≤Λ(t)^m M_m(0).                 (2)

Every M_m(0) is finite for Schwartz data; (2) is not a bound on Λ up to a hypothetical blowup time. It cannot be inserted into a continuation criterion as though it were uniform there.

Primary comparison was made against actual versioned TeX bodies, not just abstracts:

* Luk–Strain, arXiv:1406.0169v1, `main.theorem.1`, assumes weighted H^4 particle regularity, local-shift supremum-integrability of weighted particle derivatives, H^4 fields, and a uniform integral of |E|+|B| along ALL characteristics. Its proof first turns that assumed integral into a uniformly bounded absolute displacement in momentum (`prelim.est`, 1165–1235), obtains weighted density bounds from the initial local-shift conditions, then closes field/characteristic derivative bounds and local continuation (1510–1544). A signed force increment such as (1) is not this absolute-field criterion. Schwartz data satisfy the particle initial hypotheses, but the full field class above is not automatically global H^4.
* Its `main.theorem.2` uses an evolved L^∞_t L^q_x L^1_v weighted norm with θ>2/q for q>2 (and high initial moments). It does not replace that evolved assumption by initial Schwartz decay.
* Patel, arXiv:1607.07416v1, `MAIN`, uses initial moment order greater than 5 and the inherited regularity assumptions, plus an evolved globally integrated moment of some order θ>3 bounded throughout [0,T). In `finalest`, 660–795, the standard moment estimate is combined with field estimates to upgrade a bounded evolved moment M>(N+3)/2 to an evolved moment N>3. Young's inequality absorbs the N moment only because the lower evolved moment is already bounded. Iteration M↦M+(M−3)/2 reaches an order greater than 5 and then the absolute-characteristic criterion. Conservation gives order 1, not the required starting order greater than 3.

The papers supply a useful downstream continuation interface. They do not pay the new global tail propagation step. The primary comparison is bounded to these papers and sections; it is not a worldwide novelty determination.

## Attempt 3: transported label shells and their cross-work

Take a smooth dyadic partition in the INITIAL label q0, with shell j at q0≈2^j, j≥0. Transport f0,j by the TOTAL RVM characteristic flow. Then f=Σj f_j, and each f_j solves the same linear transport equation with the total force. Put a_j=||f0,j||∞ and m_j=||f0,j||1. These are preserved. On a Λ-bootstrap interval, each shell has current momentum support q≤CΛ2^j. Thus

    ||ρ_j||∞ ≤ C a_j Λ³2^(3j),  ||ρ_j||1=m_j,
    ||j_j||2 ≤ ||ρ_j||2 ≤ C Λ^(3/2)2^(3j/2) sqrt(a_j m_j).       (3)

This estimate follows by the volume of the momentum ball and L¹–L∞ interpolation. It requires no fictitious conservation of shell energy.

For any Maxwell decomposition F=Fvac+Σj F_j with F_j sourced by j_j and with consistent Gauss initial data, the EXACT local balance is

    ∂t[∫q f_j dv+(|E_j|²+|B_j|²)/2]
      +div[∫q u f_j dv+E_j×B_j] = (E−E_j)·j_j.                 (4)

Indeed, the particle equation contributes E·j_j; the shell Maxwell equation contributes −E_j·j_j. Its cone integral therefore includes cross-work with no sign. The total energy's cross-field terms are what restore cancellation. Using the source's conserved total cone flux for each (f_j,F_j) would be invalid.

There is a legitimate but insufficient substitute. Maxwell L² evolution and (3) give, for a tail sourced by Σ_{j>J}j_j,

    ||F_tail(t)||2 ≤ ||F_tail(0)||2 + C T Λ(T)^(3/2) S_J,
    S_J=Σ_{j>J}2^(3j/2)sqrt(a_j m_j).                           (5)

Likewise total electric energy bounds ∫|E·j_j| by C||j_j||2, giving the same Λ^(3/2) loss for this crude work estimate. Own-field cross-work in (4) is not better by this argument. Formula (5) is an L² estimate, not an estimate of force along characteristics; even if a later cone estimate could use it without further loss, the following logarithmic closure test already fails.

Consider the explicit permitted datum

    f0(x,v)=χ(x) exp(−[log(2+|v|²)]²),

where χ is a nonzero nonnegative C_c^∞ function. This is Schwartz in all six variables: each derivative is a finite sum of polynomial/logarithmic factors times the displayed function, which dominates every inverse polynomial. It decays more slowly than exp(−c|v|^α) for every c,α>0. For any standard dyadic partition nontrivial on fixed-width annuli, shell mass and supremum give

    exp(−C1 J²) ≤ S_J ≤ C2 exp(−c2 J²)

for all large J, after adjusting positive constants. This follows directly from the exponent −4(log|v|)² and the annular volume 2^(3j); the linear-in-j factors do not change the quadratic exponent. Consequently making the positive right-hand error Λ^(3/2)S_J bounded by a fixed small number in THIS ESTIMATE requires J≳sqrt(log Λ), and J=C sqrt(log Λ) is sufficient with large enough C. Fixed J cannot absorb arbitrarily large Λ.

For a low-initial-momentum receiver at normalized scale Λ≈2^n, the finite-shell cap is then P≈Λ2^J. Even granting an extension of (1) to that split system with cutoff-independent constants and assuming the tail could be harmlessly absorbed, an increment of order Λ yields only

    Δt_n ≥ c (Λ/P)²/log(2+P) ≍ c 2^(−2J)/(n+J).                (6)

To check (6), divide (1) by Λ with w≈Λ; if Δt is smaller than a sufficiently small constant times (Λ/P)²/log(2+P), both terms are smaller than the required unit increment. For J≈C sqrt(n), the resulting lower bound is proportional to exp(−c sqrt(n))/n. Its sum CONVERGES: group n between k² and (k+1)², or substitute y=sqrt(n) in the integral test. A convergent lower bound on doubling times does not rule out finite-time growth. This is a failure of the estimated bootstrap, not a constructed RVM blowup or a lower bound forcing actual shell work to be large. There may be cancellations or better two-scale cone estimates that eliminate the Λ power; none has been proved here.

This test also explains why “all moments initially finite” is insufficient for the proposed shortcut. Replacing (3) by a high moment with a fixed polynomial-tail bound still introduces Λ-dependent evolved moments via (2). Choosing a tail cutoff depending on Λ changes the very cap factor that drives the source's logarithmic time divergence. One must track these dependencies, not invoke Schwartz decay qualitatively.

## Remaining unpaid mechanism and contribution boundary

A complete result would need a new global estimate controlling all initial velocity shells with their observer/source scales separately, preserving a nonintegrable growth-time lower bound (or a uniform evolved moment greater than 3), and respecting the total-field cross-work in (4). It must also implement continuation/localization for the full C_b^∞∩L² field class and noncompact spatial support. Neither requirement is discharged by the compact source theorem plus the cited conditional continuation criteria.

The boundary-term replacement, constraint-preserving initial approximation, identity (4), bound (3), and convergence test are elementary diagnostic deductions. They are recorded to make the failed paths reviewable, not nominated as substantial new mathematics. No full candidate, source-to-new-theorem dependency graph, or Lean proof interface has been frozen. A Lean check of finite sums, exponents, or the series test would not certify the missing nonlinear cone estimate; no formal proof of the proposed global theorem is claimed. The unchanged full Schwartz-data target remains unresolved.
