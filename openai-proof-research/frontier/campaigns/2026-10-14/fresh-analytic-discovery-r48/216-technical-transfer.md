# Critical XY magnetic response: a technical scaling transfer

Myeongjin Kang. No affiliation. Original prose CC BY 4.0.

This is an author-side deduction, not an independently reviewed candidate. The scope was recorded after exploration: no discovery target was frozen and then weakened. The generic magnetic scale selection is credited to Camia–Garban–Newman (CGN), *The Ising magnetization exponent is 1/15*, arXiv:1205.6612v2, especially §§2 and 4. The substitutions below use existing XY correlation inequalities and the pinned source estimates. They are classified here as technical, with no contribution or count claim.

## Statement and conventions

Consider the nearest-neighbor cosine XY model on Z² with exponent

    b_c Σ_{edges} cos(θ_x−θ_y) + h Σ_x cos θ_x,

where each edge is counted once and b_c is the mass-defined critical inverse temperature of source216. The number h is the dimensionless field appearing in this exponent; there is no extra b_c in its definition. Let m(h) be the magnetization of the translation-invariant infinite-volume Gibbs state, for h>0, and p(h) its pressure. Then for some c,C,h₀>0,

    c h^(1/15) [log(1/h)]^(1/15) ≤ m(h)
        ≤ C h^(1/15) [log(1/h)]^(1/15),        0<h<h₀.            (1)

The same constants need not occur in the two bounds. In particular

    p(h)−p(0) ≍ h^(16/15) [log(1/h)]^(1/15).                    (2)

No limiting amplitude, near-critical field process, or magnetic correlation-length asymptotic is asserted. The pressure and translation-invariant-state facts used here are classical: Messager–Miracle-Solé–Pfister (MMP1978), Theorem3 and §4, use the rotator Lee–Yang theorem to obtain differentiability at nonzero h and uniqueness of the translation-invariant state. The proof of the inequalities also works directly for the plus-state magnetization, without needing uniqueness of all Gibbs states.

## Exact inputs

Write ℓ(r)=log(e+r). Q_n=[−n,n]²∩Z² has its boundary vertices fixed to angle zero, retains all its internal nearest-neighbor edges, and has no field unless stated. Put a_n=E^+_{Q_n,0} cos θ_0.

* Source216 center-magnetization Theorem main gives a_n~A n^(−1/8)(log n)^(1/16), A>0. Increasing constants handles all n≥1.
* Source216 critical-spin-field Proposition correlations:diagonal, equation(20), and Lemma correlations:green-diagonal give, uniformly for x,y in the central half of Q_n,

      0≤ E^+_{Q_n,0} cos(θ_x−θ_y)
          ≤ C a_n² n/(1+|x−y|).                               (3)

  Indeed equation(20) concerns the normalized fields W_n^±; their additional Green diagonal factors and reciprocals are bounded on this fixed compact subset. This bound deliberately uses the source's integrable exponent1, not an unproved sharp collision exponent1/4.
* Source216 critical-spin-field Lemma fields:lee-yang gives, for any finite pinned XY graph and nonnegative weights, W=Σ λ_x e^{iθ_x}, v=E|W|²,

      ||W||_q ≤ C√q √v, q≥2,

  and its proof gives P(|W|>r)≤4 exp(−r²/(2v)). The auxiliary uniform rotation is used only to establish this absolute-value estimate; it does not rotate the physical external field.
* Source216 logarithmic-correction Theorem main gives the free infinite-volume axis correlation C(re₁)~B r^(−1/4)(log r)^(1/8), B>0.
* Ginibre1970 Proposition3 and Example4/Model3 give nonnegative covariances for cosine characters with nonnegative cosine couplings, including one-site fields. MMP1978 Proposition1 gives domination of any boundary angles by aligned zero boundary angles. Its §3 gives the monotone plus-state limit. These are comparisons of cosine observables, not an asserted coordinatewise order on angle configurations.
* Dario–Garban2025, PropositionA.2 and Remark16, equation(A.2), record the classical Messager–Miracle-Solé comparison: for an absolute C₀, |y|≥C₀|x| implies C(y)≤C(x). Their statement applies to ordinary homogeneous Z² as a special case. Combining both comparisons with axis points gives

      C(z) ≍ (1+|z|)^(−1/4) ℓ(|z|)^(1/8).                     (4)

  For the upper bound choose an axis point of length at most |z|/C₀; for the lower choose one of length at least C₀|z|. Bounded distances are absorbed into constants. This operation is already in that primary source; no new reflection argument is claimed.

## Boundary-to-bulk block moment bound

For a set B contained in the central half of a square Q_n, with diameter and cardinality bounded respectively by Cn and Cn², summing (3) gives

    E^+ |Σ_{x∈B}e^{iθ_x}|² ≤ C n⁴ a_n².                       (5)

For each x, the sum of n/(1+|x−y|) over a square of radius O(n) is O(n²), by counting O(k) lattice sites in each annulus k≤|x−y|<k+1. Thus the total is O(n⁴). Formula(5) includes coincident points.

We extend this bound to the entire pinned square, including its boundary layer. A lattice Whitney decomposition of the interior consists of disjoint boxes B at dyadic scales r≥1, each contained in the central half of a concentric lattice square of radius comparable to r that remains inside Q_N. There are at most C N/r boxes at scale r. To construct it, partition the strips where distance to ∂Q_N lies between successive powers of two into a bounded number of rows of dyadic squares of a fixed smaller size, and subdivide boundary leftovers. Put the O(N) sites within a fixed distance of the boundary into singleton boxes. Constants in the enlargements and counts are absolute; rounding finitely many small sizes changes only these constants.

Condition on the spins outside an enlarged square. MMP Proposition1 bounds every conditional cosine difference of two spins in B by the corresponding aligned-boundary expectation. Consequently (5) bounds its unconditional second moment in Q_N too. For a box of scale r,

    ||Σ_{x∈B}e^{iθ_x}||₂ ≤ C r² a_r
        ≤ C r^(15/8) ℓ(r)^(1/16).

Apply the triangle inequality in L² to the complex sums over all boxes. The boundary singletons contribute O(N). The remaining contribution is at most

    C Σ_{dyadic r≤N} (N/r) r^(15/8) ℓ(r)^(1/16)
      ≤ C N^(15/8) ℓ(N)^(1/16),                               (6)

because Σ_{dyadic r≤N}r^(7/8)≤C N^(7/8). No independence of boxes is used. Including or omitting the pinned boundary sites has the same bound. Thus, for W_N=Σ_{Q_N}e^{iθ_x},

    v_N^+ := E^+|W_N|² ≤ C N^(15/4) ℓ(N)^(1/8).                (7)

This elementary boundary summation is the only localization adjustment to the source local moment estimate.

## Upper magnetic response

Put X_N=Re W_N. Tilting the pinned zero-field measure by exp(hX_N) gives the pinned-field measure; boundary sites contribute a deterministic factor that cancels. Ginibre positivity gives E^+X_N≥0, so Jensen gives E^+exp(hX_N)≥1. For any fixed K<∞ the absolute Lee–Yang tail estimate implies

    E^+[|W_N| exp(h|W_N|)] ≤ C_K √v_N^+
                      whenever h√v_N^+≤K.                    (8)

For example, set Y=|W_N|/√v_N^+ and integrate the tail bound against the derivative of y exp(Ky); its integral against 4exp(−y²/2) is finite. Hence

    E^+_h X_N ≤ C_K √v_N^+.

Conditional boundary domination for the infinite-volume state, followed by translation invariance, yields

    m(h)≤ |Q_N|^(−1) E^+_h X_N
         ≤ C N^(−1/8)ℓ(N)^(1/16)                             (9)

when h N^(15/8)ℓ(N)^(1/16) is bounded. This argument uses no XY GHS inequality.

## Lower magnetic response

Let μ₀ be the rotation-invariant free-box infinite-volume zero-field law. Its finite-dimensional existence follows from the usual cosine-character monotonicity and compactness; sine expectations vanish by reflection, and global rotation removes nonneutral characters. For X_N=Σ_{Q_N}cos θ_x under μ₀, symmetry gives EX_N=0, and rotation invariance gives

    V_N:=EX_N² = (1/2)Σ_{x,y∈Q_N}C(x−y)
          ≍ N^(15/4)ℓ(N)^(1/8).                              (10)

The upper estimate follows by radial summation of (4). For the lower, take x in a fixed central sub-square and y in a sub-square at distance comparable to N; there are order N⁴ such pairs, each bounded below by cN^(−1/4)ℓ(N)^(1/8).

The finite-free-graph Lee–Yang theorem and its symmetric product representation imply

    E exp(tX_N) ≤ exp(t²V_N/2), t∈R.                          (11)

Pass from free finite graphs to μ₀ with the fixed finite observable X_N; boundedness justifies passage of both moments and exponential moments. Add field h only at sites of Q_N. The expectation of X_N in this local-field tilt is

    E[X_N exp(hX_N)]/E exp(hX_N)
      = E[X_N sinh(hX_N)]/E cosh(hX_N)
      ≥ h V_N exp(−h²V_N/2),                                (12)

since x sinh(hx)≥h x². Ginibre monotonicity in the nonnegative one-site fields makes each cos θ_x expectation no smaller when field h is then imposed everywhere in a finite containing volume. Pass to infinite volume. The free uniform-field limit is the translation-invariant state at h>0 (or is dominated by the plus state). Therefore

    m(h) ≥ |Q_N|^(−1) h V_N exp(−h²V_N/2).                    (13)

This is a classical local-field tilt argument, not an FK cluster construction and not a change of the model's physical field.

## Choice of scale and pressure

Let H=log(1/h) and choose

    N= floor(h^(−8/15) H^(−1/30)).                            (14)

For sufficiently small h, N≥2 and log N/H→8/15. Thus

    h N^(15/8)ℓ(N)^(1/16) ≍ 1,
    N^(−1/8)ℓ(N)^(1/16) ≍ h^(1/15)H^(1/15).

The logarithmic cancellation is (−1/30)(15/8)+1/16=0; the final logarithmic exponent is (−1/30)(−1/8)+1/16=1/15. Equations(7)–(13) prove(1). Finitely many lattice sizes or rounding errors are irrelevant after fixing h₀. The pressure is differentiable for h>0, with p'(h)=m(h); its continuity at zero follows from bounded spins. Integrating(1) gives(2). For the lower bound integrate over [h/2,h]; for the upper use the integrability of t^(1/15)(log(1/t))^(1/15) and a dyadic split of (0,h].

## Contribution boundary

CGN already supplies the non-power scale relation hL²√ρ(L)≈1 and the plus-boundary block strategy. Source216 supplies the exact logarithmic normalization and the hard local field estimates. MMP, Ginibre and Lee–Yang supply all order/tilt operations. The Whitney summation, symmetric tilt and elementary inversion above do not presently justify a substantial-contribution claim. The absence of a located identical XY formula does not establish priority. No full-amplitude conclusion follows from(1), even if one additionally knows regular variation or concavity; see amplitude-interface.md.
