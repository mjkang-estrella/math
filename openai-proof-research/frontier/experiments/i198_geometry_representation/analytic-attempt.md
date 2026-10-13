# I198 analytic record

2026-10-12. Completed bounded screen. **NO VIABLE TARGET IN THIS ROUND.** The propositions below are proved technical deductions or counterexamples to proposed extensions. None is presented as a substantial nomination. All corpus theorems and proof operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted, without an upstream audit. Two different routes were developed for the strongest quantitative candidate in §3; two obstruction routes were also tested in §1.

## 1. Family 095: the exact obstruction and regularization

### 1.1 Source contracts

Let H be the 36-dimensional space of quadratics in eight variables, with H=L⊕P, dim L=8. The nonliftability manuscript's `lem:seed`, `prop:finite-normalized-fiber`, and `lem:inverse-limits` produce a rank-20 positive semidefinite Hankel matrix T, a 20-dimensional W, and finitely many projective inverse-limit directions. Its `lem:generic-wu` and `lem:separation` then supply N>10·36², r=20N−1, a unit w∈W^N and an r-dimensional U⊂w⊥⊂H^N, such that w is outside the closure of

    S_U = {(I_N⊗Y)u : u∈U, Y Hankel}.

Consequently there is η>0 such that ||P_(w⊥)z||≥η||z|| for z∈S_U. With

    g = η^(-2) P_(w⊥) − P_(Rw),
    G(y)=I_N⊗Y(y),  y∈R^330,
    Q(y)=U^T G(y) g G(y) U,

one has Q(y)≽0 for every real y and w^Tgw=−1. The basis matrix U is fixed; no orthonormal-column normalization is needed below.

The source's `prop:hyperbolic` makes

    p_Q(X,Z,y)=det((det X)Z−Φ_y(adj X)),
    e=(I_(r+1),I_(r+1),0),

hyperbolic of degree (r+1)(r+2). Its `prop:epigraph` identifies a projection of an affine section of K_Q with

    E_Q={(A,t,y): A≽0, ran Q(y)⊂ran A,
                     t≥tr(A†Q(y))}.

This is an exact equality including singular A. The pointwise Gram factors in `prop:hyperbolic` depend on y and are not a joint LMI.

On an open ball Ω⊂R^7, `lem:polynomial-patch` gives a degree-four patch

    x(s)=(M(s)M(s)^T, tr(gG(y_s)), y_s),
    M(s)=U^T(I_N⊗v(s)),   rank M(s)=N,

where y_s evaluates quartics at (1,s). The range condition and the trace inequality hold, the latter with equality. `lem:moment-violation` supplies a normalized positive-definite degree-four moment functional Λ such that for every c in a smaller open ball,

    x_(c,ε)=Λ_s x(c+εs)=(A_ε,t_ε,y_ε),
    A_ε≽a_c ε^4 I,
    t_ε−tr(A_ε^(-1)Q(y_ε))=−κ_c ε^4+o(ε^4),

with a_c,κ_c>0 and bounded coordinates. The finite moment-extension, analytic-Gram-selection and near-feasibility lemmas give, for any hypothetical finite lift, feasible points at distance O(ε^16) on a nonempty open subpatch. `prop:no-lift` excludes the lift.

The 23-variable companion is a different Q: the 3×3 Choi–Lam quadratic matrix. Its original polynomial has degree 20; the quotient by det X has degree 16 and the same cone. The exact-lift companion's `lem:gram`, `lem:slice`, `lem:matching`, and `prop:lift` construct a 100×100 homogeneous pencil with 307 auxiliary variables for the entire closed cone. The matching identity is of trigonometric degree two. A feasible functional need not be a measure; matching directly recovers the range condition at singular X. Non-SOS behavior of a chosen Q, or failure of an original-coordinate LMI, is therefore insufficient to exclude all lifts.

### 1.2 Route A: coefficient perturbation of the local obstruction

**Technical exact threshold.** With the fixed source data above, put, for τ≥0,

    g_τ=g+τI,   Q_τ(y)=U^TG(y)g_τG(y)U.

Every Q_τ is positive semidefinite-valued. For 0≤τ<1, K_(Q_τ) admits no finite affine semidefinite lift. For τ≥1, K_(Q_τ) is spectrahedral.

**Proof.** On S_U, adding τ||z||² preserves nonnegativity. At w the value is −1+τ. For each fixed τ<1, the entire source moment-patch argument applies with g_τ in place of g: the patch t-coordinate becomes tr(g_τG(y_s)), the range identity is unchanged, and the rank-one residual at (c,S)=(0,T) has coefficient αw^Tg_τw<0. Continuity chooses a positive-definite Hankel S near T and a nonempty ball of centers, now allowed to depend on τ. All hypotheses of the accepted no-lift argument are preserved. This is direct substitution into that proof, not an additional separation theorem.

For τ≥1, g_τ≽0, and R_τ(y)=g_τ^(1/2)G(y)U is linear in y with Q_τ(y)=R_τ(y)^TR_τ(y). Write the columns of R_τ(y)^T as b_j(y), and let B_j(y) be the skew block matrix built from b_j as in `prop:hyperbolic`. The block matrix with diagonal blocks X,...,X,Z and last-column off-diagonal blocks B_j(y) is a linear pencil. By the generalized Schur complement its positivity is equivalent to X≽0, the corresponding range conditions, and Z≽Σ_j B_j(y)^TX†B_j(y). These conditions depend only on Σ_j b_j(y)b_j(y)^T=Q_τ(y), hence agree with the source's pointwise Gram characterization of K_(Q_τ), including singular X. There can be more global linear Gram columns than the r+1 pointwise columns used for the determinant identity; the Schur conditions are nevertheless identical. This gives a finite LMI. □

**Contribution boundary.** This phase transition is a precise structural description, not dismissed merely because it is short. Its entire negative side is the strict sign already used by `lem:moment-violation`; its positive side is the standard global Gram-to-block-LMI construction already visible in `prop:hyperbolic`. It adds no new patch, inverse-limit separation, or control beyond those accepted operations. It is a technical reassembly, not the unpaid stability bridge requested by the brief.

A more demanding target is:

    for the same Q, Q^δ(y)=Q(y)+δ||y||²I_r,
    does there exist δ0>0 such that K_(Q^δ) has no finite lift
    for every 0<δ<δ0?

No answer is proved here. There is a concrete failure of the proposed proof: every y_s is nonzero, so Q^δ(y_s) has rank r. But A(s)=M(s)M(s)^T has rank N<r. Thus ran Q^δ(y_s) is not contained in ran A(s). Changing only t cannot make the old patch feasible, however small δ is. At every fixed δ>0, a replacement full-rank A has a nonzero small-eigenvalue floor as ε→0; the singular ε^4 scaling behind the source residual cannot simply be reused. What is missing is a new feasible patch and moment deformation with a negative leading coefficient that survives this floor, or another obstruction. Failure of this proof is not a counterexample to the stated target.

Broad smooth-regularization nonliftability is not a plausible replacement: Netzer–Sanyal's smooth-boundary theorem and Nuij approximation give arbitrarily close liftable approximants; Scheiderer's Nash-smooth theorem is stronger. These are compatible with the singular source examples and do not create an inconsistency in the accepted premises.

### 1.3 Route B: quantitative separation and approximate lifts

There is a simple technical strengthening of the source's final estimate. Fix c and its Λ. In a fixed product norm, for some d_c>0 and all sufficiently small ε,

    dist(x_(c,ε),E_Q) ≥ d_c ε^12.                       (095-D)

**Proof.** Put f(A,t,y)=t−tr(A^(-1)Q(y)) on A≻0. The source gives f(x_ε)≤−(κ_c/2)ε^4. If a perturbation h=(ΔA,Δt,Δy) has norm ≤dε^12, then for small ε its A-coordinate is still at least (a_c/2)ε^4I. Both inverses have norm O(ε^−4), and

    ||(A+ΔA)^(-1)−A^(-1)|| ≤ C ε^−8 ||ΔA||.

On the fixed bounded y-neighborhood, Q and its first derivative are bounded. Consequently

    |f(x_ε+h)−f(x_ε)| ≤ C' ε^−8 ||h||.

Choose d<κ_c/(4C'). Then f(x_ε+h)<0 throughout this ball, excluding E_Q. This proves (095-D). Constants depend on the fixed data and c, not on ε. □

This does not produce a lower bound on lift size versus approximation error. A fixed positive Hausdorff error eventually exceeds d_c ε^12 as ε→0. Nor does bounded matrix size alone give a common analytic selection neighborhood and uniform Taylor constants for a varying family of lifts. Those missing uniform controls are exactly what would be needed to combine an approximate-lift hypothesis with (095-D). Finite nonnegative matrices of bounded psd rank have a classical compactness/lower-semicontinuity theorem, but it contains no effective error-versus-size rate for these cones. No transfer from that theorem to a quantitative cone bound is asserted.

## 2. Family 100: scope of finite approximation and an actual failed extension

The ruled-set paper proves finite square-intercept covers of

    E(D,V,L)={(s,p+sV(p)):p∈D, |s|≤L}

for every compact D⊂R², V∈C¹ near D, L,h>0, assuming tr DV=0 and −L^−2<det DV≤0 on D. Cost is hΣ|T_i|J_h(g_i), J_h(g)=(1+g_1²+h²g_2²)^−1/2, and is at most h∫_D J_h(V)+any prescribed positive tolerance. Square orientations may vary. All labels, including positive-measure boundaries and measure-zero compact sets, are covered. The full affine square-grid and finite-retention proofs were read. They already include square-zero derivatives with unrestricted shear and mixed hyperbolic/nilpotent regimes. Their inverse constant is (1+LM)/σ with σ=min_D(1+L²det DV)>0; it is not uniform when σ vanishes.

The radial companion adds prescribed tags and one triangular cylinder per interval when w'(t)=λ(t)(a+tb), including the apex and vanishing radial caps. The slope-field companion already has rational, singular and nilpotent constructions; the angular companion already supplies explicit counts, remainder and cubic-buffer refinements. Affine transport of their normalized tetrahedral counterexample is explicitly supplied. Those are not new targets.

A tempting unpaid extension was to retain trace zero but allow elliptic differentials, with the same integral cost. It is **false**, even without restricting the directions or shapes of the proposed finite cylinders.

**Counterexample.** Take L=h=ω=1, ρ=1/10, D={p:||p||≤ρ}, and V(p)=Jp, where J(p_1,p_2)=(−p_2,p_1). Then tr DV=0 and det DV=1. At height s the swept slice is the disk of radius ρ√(1+s²). Hence

    |E|=∫_(−1)^1 πρ²(1+s²)ds=(8/3)πρ²,
    diam E≤2√(1+2ρ²).

For every measurable cylinder C=B+Ru with unit u, Fubini gives

    |E∩C|≤(diam E)|B|,

because the length of E on each line parallel to u is at most its diameter, whether or not E is convex. Any finite cover therefore has

    Σ|B_i| ≥ |E|/diam E
            ≥ [4/(3√(1+2ρ²))]πρ² > πρ².

The last inequality follows from 1+2ρ²=51/50<16/9. But the proposed integral bound is

    ∫_D (1+||V(p)||²)^−1/2 dp
      =2π(√(1+ρ²)−1)<πρ².

There is a fixed positive gap, so choosing the tolerance smaller than that gap contradicts the extension. □

This is a standard volume/chord obstruction applied to a linear field, not a substantial discovery. It explains why a trace-only hypothesis is insufficient. A corrected elliptic theory would need an expansion-dependent cost, and a boundary-of-spectral-range theory would need a new finite-retention argument. Neither is supplied. The body need not be convex for this diagnostic, since the proposed ruled-set extension did not assume convexity. No claim about the optimal tetrahedral covering constant follows.

## 3. Family 210: strongest quantitative candidate, two distinct routes

### 3.1 Contracts and exact target

Write R_j=((Sym^j V)^(⊗a))^(S_a), with normalized averaging, R=⊕R_j, and A⊂R the subalgebra generated by R_1=Sym^a V. The canonical map is

    μ_(a,b,V):Sym^b(Sym^a V) → Sym^a(Sym^b V)=R_b,

the multiplication map, with image A_b. The quadratic paper proves surjectivity for b≥a(a−1). Its annihilator criterion says this is equivalent to the following: a symmetric a-linear T on Sym^b V vanishing at (P,...,P) for every product P of b vectors is zero. The sixth-power paper proves the ordinary representation comparison for all b≥6, not canonical injectivity for that entire range. In particular its diagonal comparison does not remove the known canonical kernels.

The strongest technical statement established here is:

**Proposition F210.** For every integer a≥2, every integer b≥(a−1)², and every finite-dimensional complex V, the specified canonical map μ_(a,b,V) is surjective. Consequently R_b=A_b in this range, and there exists a GL(V)-equivariant embedding in the reverse direction. For a=1 the map is the identity for every b≥0.

This improves the sufficient threshold by a−1, with no dimension bound. For a=6 it gives canonical surjectivity from b=25 instead of b=30. It does not establish the seventh ordinary Foulkes case throughout b≥7, and it does not claim a sharp threshold. It is already obtainable from the two companions' lower operations, as explained below.

### 3.2 Route 1: annihilator induction with whole differential powers — complete

For independent vector variables U,Y, let D=Y·∂_U and E=U·∂_Y. On a homogeneous polynomial space these satisfy

    E=D*,  [E,D]=N_U−N_Y,

for the Fischer Hermitian inner product. For every k≥0, D^k is injective on bidegree (p,q) whenever p−q≥k; all other variables can be spectators. This whole-power statement is explicitly proved/used in the sixth-power companion's `lem:polarization`, not only an external fact.

For clarity, its elementary string justification is as follows. At a highest vector v with Ev=0 and (N_U−N_Y)v=ℓv, the commutator gives

    E D^j v = j(ℓ−j+1)D^(j−1)v.

Adjointness yields nonzero vectors through D^ℓv and zero thereafter. The finite-dimensional polynomial space splits into such strings: their span and its orthogonal complement are invariant under the adjoint pair and the self-adjoint weight operator; induction decomposes the complement. On a string of highest weight ℓ, weight h=p−q occurs at j=(ℓ−h)/2, and has (ℓ+h)/2≥h steps left to the bottom. Thus k≤h ensures D^k is nonzero there. Decomposition proves injectivity on the full bidegree space.

Now induct on a, allowing b≥0 for a=1. Dimension zero is trivial in the claimed positive-b ranges. Let a≥2, r=a−1, b≥r², and m=b−r≥r(r−1)≥0. Let T satisfy the annihilator condition. Products of zero vectors mean the unit of Sym^0 V.

1. For Q=y_1···y_m, the binary form x^r+c t^r splits into r linear factors over C for every c. Thus (x^r+c t^r)Q is a product of b vectors. The coefficient of c in its diagonal T-evaluation is

       a T(x^rQ,...,x^rQ,t^rQ)=0.                     (F1)

2. Fix x and set H=T(x^rQ,...,x^rQ,t^b). Apply D_(y_m,t)···D_(y_1,t). The result is the nonzero scalar b!/r! times (F1), hence zero. Before the ith transfer, the t-degree is b−i+1 and the y_i-degree is r, so their difference is m−i+1≥1. The source's one-step differential injectivity applies at each step. If m=0 there is no operator and (F1) is already H=0. Therefore H=0 identically.

3. For fixed x,t the expression

       (Q_1,...,Q_r) ↦ T(x^rQ_1,...,x^rQ_r,t^b)

is a symmetric r-linear form on Sym^m V, with diagonal zero on products. If r=1, the degree-zero case is included in the identity base case. Otherwise m≥r(r−1)≥(r−1)², so the induction hypothesis applies. It follows that

       T(x^rQ_1,...,x^rQ_r,t^b)=0                    (F2)

for all Q_i∈Sym^m V and all x,t.

4. Fix t, introduce independent v_1,...,v_r,x, and set f=T(v_1^b,...,v_r^b,t^b). Apply the r blocks D_(x,v_i)^r in order i=1,...,r. The result is

       (b!/m!)^r T(x^rv_1^m,...,x^rv_r^m,t^b)=0

by (F2). Before block i, v_i has degree b and x has degree (i−1)r. Whole-power injectivity applies because

       b−(i−1)r ≥ r,   since b≥r²≥ir.

Each block is injective on the entire appropriate homogeneous space, so the composition is injective and f=0. Pure powers span Sym^b V by characteristic-zero polarization. Since t was arbitrary, multilinearity gives T=0.

The accepted annihilator criterion proves canonical surjectivity. Equivariance and complete reducibility supply the reverse embedding. □

**Endpoint validation.** The equality b=r² is retained at the final block, where its starting weight is exactly r. Whole-power injectivity includes equality, though one-step injectivity fails near the bottom of that block. At a=2,b=1, m=0 and the above empty-product convention agrees with the identity μ_(2,1,V). No assertion is made in positive characteristic.

**Weak-step attack.** One cannot improve this full-space block argument by simply permitting starting weight r−1. For r≥2 set q=r(r−1), p=r²−1, use two U and two Y coordinates, and consider

    h=(U_1Y_2−U_2Y_1)^q U_1^(r−1).

This is nonzero of bidegree (p,q). D annihilates the determinant factor, so D^r h=0. This is a counterexample to the proposed full-space cancellation, not a T satisfying all preceding constraints. It therefore does not disprove better stabilization bounds obtained by another method.

### 3.3 Route 2: chart, conductor and polarization — independent but stops earlier

The sixth-power companion proves, for arbitrary a, a chart lemma and a polarization lemma:

* R is generated over A by degrees 0,...,a−1.
* For z(v)=v^(⊗a), one has z(v)^L f∈A_(k+L) for every f∈R_k when L≥(a−1)k.
* For j≥aL, R_j is spanned by z(v)^L R_(j−L), with v ranging over V.

These give the independent cubic threshold a(a−1)²: choose L=(a−1)², which clears every generator, and then j≥aL gives R_j=A_j. This proof uses chart denominators and module generation, rather than the annihilator/binary-factor induction.

Attempting to lower its last condition to j≈L would produce the desired quadratic threshold by a different route. The ambient polarization statement cannot have that improvement. Take dim V≥a, independent vector variables x_1,...,x_a and y, and let

    f(x_1,...,x_a)=det(x_1,...,x_a)^j

in an a-coordinate subspace. It is nonzero and homogeneous of degree j in each x_i. Since a determinant with two columns equal to y is zero,

    det(x_1+t_1y,...,x_a+t_ay)

has total degree at most one in all the t_i together. Its jth power has total t-degree at most j. Therefore the coefficient of t_1^L···t_a^L is zero whenever aL>j, and

    ∏_(i=1)^a (y·∂_(x_i))^L f=0.

This gives a nonzero annihilator to the corresponding span on W_j=(Sym^j V)^(⊗a). If j is even, f is also invariant under permutations of the x_i and gives the same obstruction for R_j. Thus the universal ambient polarization threshold in the accepted chart route cannot simply be reduced. A new argument would need to exploit the actual conductor quotient, not all of R_j, or substantially improve chart denominator clearing. Neither was constructed.

### 3.4 Novelty and significance decision

The two original sources already contain both nontrivial ingredients of F210: the complete binary-factor/annihilator induction in the quadratic paper, and exactly the whole-power weight-string lemma in `lem:polarization` of the sixth-power companion. F210 replaces the final sequence of one-step bounds by that already-paid lemma and changes no other construction. It is more precise than merely quoting the headline, but is a technical consequence of the accepted lower operations. The improvement is additive a−1, remains quadratic, and supplies neither a new linear bound nor a new family of representations or a new seventh-case comparison in the unresolved range.

The primary comparison with Ikenmeyer §5 also confirms that weight-string injectivity is established methodology. Raicu–Sam–Weyman §2 identifies the same canonical map and finite-length normalization quotient. Their characteristic-zero statements do not themselves supply this exact uniform bound; absence of the number (a−1)² from inspected sources does not establish priority. No worldwide novelty claim is made. The failure to meet the contribution gate is the explicit source-operation overlap, not the brevity of the proof or an unsupported assertion that every nearby result is known.

## 4. Final scope

All three authorized families were screened, in order 095, 100, 210. No additional families were substituted. The exact Q+δ||y||²I stability target and a quantitative approximation-size estimate remain unproved; the trace-only cylinder extension is refuted; F210 and the g_τ transition are technical deductions. No target in this round has both a substantive unpaid bridge and a complete proof. Eight substantial findings remain accepted, two remain; the parent retains both independent acceptance gates.
