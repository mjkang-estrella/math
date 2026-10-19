# T085E111: affine contacts and the unresolved common-price interface

This is an author research notebook, not a completed proof or a nominated result. The full target in frozen-target.md is unchanged. All upstream theorem statements and operative proof operations are stipulated true at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The statements below distinguish credited operations, directly justified calculations, and the missing step. No statement about worldwide priority is made.

## 1. Exact envelopes and the strongest immediate reduction

Write B for the unit disk, and let S_E be exactly the compact shape set in the frozen target. For smooth real g put

    U(r,A,x) = (pi r^2)^(-1) integral_(x+rAB) g,
    F_[a,b](x) = max_(a<=r<=b,A in S_E) U(r,A,x).

The input is signed here, for the same local mean-subtraction reason as source085 Proposition prop:finite-band. On a finite radius band the parameter set is compact and the envelope is locally Lipschitz. At a differentiability point its gradient agrees with the spatial gradient of every active smooth branch: the difference of the envelope and a touching branch has a local minimum. This remains true at ties. It neither assumes a differentiable optimizer nor differentiates its orientation.

For one fixed A, change coordinates x=Ay and put g_A(y)=g(Ay). The source disk estimate gives

    integral |grad M_A f| <= C ||A^(-T)|| ||A^T|| integral |grad f|
                          <= CE integral |grad f|.

For N fixed shapes the maximum rule gives at most CEN. Approximation by finite nets therefore has an uncontrolled cardinality factor. There is no estimate here uniform in the net size. The inclusion AB subset sqrt(E)B also gives M_E f <= E M f, which proves local integrability from the stipulated disk theorem. An order inequality between functions supplies no order inequality between their variations.

The entire affine reduction, finite-maximum rule, touching argument and local integrability are credited. They do not constitute the attempted new operation.

## 2. What affine optimality actually supplies

Translate x to zero and let K=rAB. For a matrix H use L_t=I+tH. Differentiating the normalized average by the change of variables y=L_t z gives

    d/dt average_(L_tK) g |_(t=0) = |K|^(-1) integral_K grad g(z) dot H z.

The determinant normalization cancels in the change of variables; it is incorrect to add a second trace term to this formula. Define M_ij=integral_K (partial_i g) z_j. The derivative is |K|^(-1) sum_ij H_ij M_ij. This is the elementary affine-variation operation already present in Luiro, Proposition2.3/Lemma2.4 and their proofs; the ball contracts there are not asserted to be literal ellipse theorems.

If K is a radius-interior maximum and has aspect ratio strictly below E, with E>1, every sufficiently small real linear deformation still represents an allowed ellipse with some radius. Thus M=0. This includes the circle, which is an interior point of the physical shape space for E>1 despite the polar-coordinate singularity at s=0.

At aspect ratio exactly E>1, take principal coordinates K={z: z_1^2/a^2+z_2^2/b^2<1}, a>b. Dilation gives M11+M22=0. Physical rotation gives -M12+M21=0. The infinitesimal map H=AJA^(-1) is tangent to the same ellipse, so its derivative vanishes identically for every g:

    -(a/b) M12 + (b/a) M21 = 0.

Hence M12=M21=0. The derivative in increasing logarithmic aspect is M11-M22. A constrained maximum at the upper endpoint only implies that this outward derivative is nonnegative. Therefore

    M = m diag(1,-1),  m>=0,

not M=0. This calculation is exact and also applies when the constrained maximum is not strict. For E=1 the additional aspect variations do not exist; that case is already the stipulated disk theorem. At forced radius endpoints even the zero-trace identity is unavailable. Both boundary cases belong to the full target and cannot be dropped.

## 3. A finite contact calculation that motivated the attempt

Let Q=A^(-2) at normalized radius one. On the boundary n(z)=Qz/|Qz|. The divergence theorem gives the exact identity

    M = integral_(boundary K) g n(z) z^T dH^1(z) - (integral_K g) I.

At an interior shape optimum M=0, so three separated boundary directions can be tested by the independent symmetric matrices z_i z_i^T. Specifically, the matrix with rows (z_i1^2, 2 z_i1 z_i2, z_i2^2), i=1,2,3, has determinant

    2 det(z_1,z_2) det(z_1,z_3) det(z_2,z_3).

One proof factors the determinant, a degree-six alternating polynomial, by the three displayed degree-two factors: if any pair is parallel the corresponding rows are proportional. The degrees agree, and evaluation at (1,0),(0,1),(1,1) fixes the factor2. This proves the identity for all real vectors, including degenerate ones.

Here is the precise restricted estimate this calculation can support. Fix E>1, kappa>0, a normalized ellipse K with aspect <E, and three boundary points z_i with |det(z_i,z_j)|>=kappa. Suppose g is smooth and compactly supported in three mutually disjoint balls B(z_i,epsilon), with epsilon sufficiently small depending only on E and kappa, and M=0. Then

    |integral_K grad g| <= C(E,kappa) epsilon integral_R2 |grad g|.

Proof: put V=integral|grad g| and b_i=integral_(boundary K intersect B(z_i,epsilon)) g. The elementary support Poincare bound is ||g||_1<=C epsilon V: integrate along a coordinate line through each ball, where g is zero at the ends of the containing interval, and sum. On each small ball the ellipse is a graph in a direction whose angle with the normal is bounded away from pi/2. Integrating g along that transverse direction to the edge of its support, and then over graph coordinates, gives integral_(boundary K)|g|<=C(E)V. Uniform bounds on curvature, n and z imply

    sum_i b_i n(z_i) z_i^T = O_E(epsilon V).

Multiply on the left by Q^(-1). The resulting sum is sum_i [b_i/|Qz_i|] z_i z_i^T. The determinant identity, the separation assumption, and the E-dependent bounds for z_i and Q give an inverse matrix bounded by C(E,kappa). Thus sum_i |b_i|<=C(E,kappa)epsilon V. Finally integral_K grad g=integral_(boundary K)g n; replacing the normals by n(z_i) costs O_E(epsilon V). This proves the displayed restricted estimate.

This is not a version of the frozen theorem. In the actual source decomposition the individual small pieces are vector measures, not compactly supported gradient fields. The whole input is not concentrated in three caps. The cone part can be large. At constrained aspect maxima the right side of the matrix identity contains the uncontrolled nonnegative multiplier m. None of these restrictions has been removed. The estimate is recorded to explain the attempted finite mechanism, with no nomination or contribution rating.

## 4. Four contacts give a conic incidence condition, not a charging theorem

Four fixed distinct contact points y_i on a centered ellipse with center x=(u,v) necessarily satisfy

    D(x)=det_i [(y_i1-u)^2, 2(y_i1-u)(y_i2-v), (y_i2-v)^2, 1] = 0.

For any four fixed points this polynomial has degree at most two in x. To verify this and its possible degeneracy, use an affine change of coordinates sending three noncollinear points to (0,0),(1,0),(0,1), and write the fourth as (a,b). Elementary row subtraction gives D=-P, where

    P=(2u-1)[2u b(b-1)-2ab(2v-1)] + 2v(2v-1)a(a-1).

Its coefficients of u^2,v^2,uv respectively are 4b(b-1), 4a(a-1), -8ab. If P is identically zero, a and b are each0 or1 and ab=0; the fourth point duplicates one of the first three. Conversely those duplicates plainly give zero. Thus for four distinct points with a noncollinear first triple, the condition is a nonzero quadratic. The affine coordinate change only multiplies the determinant by a nonzero constant and changes its variables affinely.

This is a necessary condition only. It neither guarantees that the conic is a positive-definite ellipse of allowed aspect nor controls the mass of a continuum of near-contact quadruples. As points approach a degenerate configuration the polynomial coefficients can become small. We did not obtain a uniform quantitative incidence bound after integrating against the actual error/cone measures, or a suitable decomposition paying all nearly collinear and nearly antipodal cases. No unproved sublevel estimate is used downstream. The exact rational diagnostics merely check sample evaluations of this general identity.

## 5. Why the disk proof's balancing step does not automatically extend

Source085 local.tex, lem:local-balanced, smooths a maximizing radius by a positive one-dimensional mixture while preserving the requisite disk moment. A tempting replacement is a uniformly bounded density on a small ball in all shape parameters, annihilating all averaged parameter derivatives. Such a statement is false for arbitrary smooth parameter functions of dimension at least two.

Here is a complete diagnostic, not a counterexample to ellipse averages. Choose a nonnegative smooth bump phi on R2, supported in the unit ball, with phi(0)=1. On the closed unit parameter disk define

    u_epsilon(q)=q_1-2+2 phi(q/epsilon),  0<epsilon<1/4.

Outside the epsilon ball, u_epsilon<=-1, whereas u_epsilon(0)=0. Therefore its maximum is attained in the interior epsilon ball. Fix any C<infinity. For any nonnegative probability density k on the unit disk satisfying k<=C,

    integral k partial_1 u_epsilon
       >= 1 - 2C epsilon integral_R2 |partial_1 phi| > 0

when epsilon is sufficiently small. Indeed the perturbation derivative has size 2/epsilon and support of area O(epsilon^2); a change of variables gives exactly the displayed error bound. Thus no such density can annihilate the vector of averaged derivatives. Allowing an atomic measure at the optimizer avoids this diagnostic but supplies no boundary smoothing.

The same argument works on a fixed-radius parameter neighborhood centered at the actual maximizer, after enlarging the domain and adjusting the fixed normalization constants. It does not show that the special functions (r,A)->U(r,A,x) can realize this pathology, and it does not refute T085E111. A special balancing theorem for actual ellipse averages, or a proof avoiding shape smoothing, remains possible. Neither is established here.

## 6. Actual source interface, including the parts that are already paid

The relevant input is not just source085 thm:main. Its local.tex lem:local has a decomposition on a neighborhood of a unit square,

    h=grad g dx=sum_i v_i sigma_i + sum_d beta_d,
    S=sum_i sigma_i,  Price=sum_d s_d^alpha |beta_d|(R2), alpha=1/100.

The sigma_i are positive, the v_i fixed unit vectors, and the beta_d are absolutely continuous vector measures. Pieces of size s_d<1 have total vector mass zero and support in a ball of radius C_s s_d. At size1 they need not cancel. The unfavorable directional estimate assumes e dot v_i>=kappa>0 and charges Price alone. The size and value estimates may charge Price+S(R2).

The cancelling pieces are actually produced in prices.tex, lem:prices-remove and lem:prices-scalar-pairing, by proportional removal of positive and negative measures in scalar coordinates, then recombination in a cone basis. Equations eq:prices-vertex-reconstruction and eq:prices-scalar-defect-budget provide a full measure identity and telescoping budget. Multiplying scalar pieces by fixed vectors does not make them curl-free. For example, the vector field (partial_1 psi,0) has zero total vector integral and compact support but curl=-partial_2 partial_1 psi, generally nonzero. Thus it is invalid to impose the affine moment identities separately on every beta_d. Nor can one replace this construction by a Helmholtz projection without proving compatible support and discounted-budget bounds.

For one ellipse shape the entire disk local argument can be transported affinely, including the cone distortion, with constants depending on E. But the integral of a supremum over shapes is not bounded by the supremum of the separately bounded integrals. A union over a fine net loses its cardinality, just as in Section1. The genuinely missing interface in this route is simultaneous charging, not an affine coordinate computation.

The local value bound is already compatible. Enlarge E_Q and Omega by constants depending on E, so all ellipses of radius <=4 are contained. The segment kernel L(x,y) in source equations eq:local-value-kernel through eq:local-value-lp retains bounds C(E)/|x-y| and C(E)/|x-y|^2. Its near/far zero-mass calculation gives an L^(3/2) contribution <=C(E)s_d^(1/3)|beta_d| from each small piece. For f_Q=(g-c)1_(E_Q), the supremum of differences of two allowed ellipse averages is at most 2E M f_Q. The classical disk L^(3/2) maximal bound therefore pays the value estimate with Price+S. This is a literal compatible use of the read source proof and is credited, not nominated.

Conditional on the missing directional/size estimates below, the source common-price sum has geometric weight 2^(-alpha(l-k)) for any fixed alpha>0. Its direction labels, switch costs and differentiated-row cancellation are already paid operations: labels.tex prop:label-packing and assembly.tex eq:row-derivative-zero/eq:prefix-subtraction. The local neighborhood and fixed palette constants can depend on E. The source's signed cutoff, local mean subtraction and large-radius/small-radius split in extension.tex then remove the singular derivative part. We have not supplied an independent new assembly theorem; the conditional plan cannot be used to announce W11 regularity.

## 7. Precise missing estimate and final status

For the same local decomposition, on a sufficiently enlarged E-dependent neighborhood, define I_E(x) to consist of pairs (r,A), 1<=r<=2, A in S_E, whose value is at least U(t,B,x) for every B in S_E and every positive t with |t-r|<=1/4. Define J_E(x) to consist of maximizers over [1,2]xS_E, together with all shape maximizers at r=1 and r=2. The forced endpoints are shape-maximized; they are not arbitrary shapes at those radii. All these are compact-parameter conditions for smooth g.

The route needs some alpha_E>0 and finite constants depending only on E,C_s,kappa such that, with Price_E=sum_d s_d^(alpha_E)|beta_d|,

    integral_Q sup_((r,A) in I_E(x)) (-e dot grad_x U(r,A,x))_+
        <= C(E,C_s,kappa) Price_E,

and

    integral_Q sup_((r,A) in J_E(x)) |grad_x U(r,A,x)|
        <= C(E,C_s) (Price_E+S(R2)).

It would suffice to take alpha_E<=1/100; lowering a proved positive exponent to this range is harmless. These are UNPROVED prospective sufficient estimates, not new assumptions in the target and not asserted consequences of the pinned source. A successful proof must simultaneously cover all orientations and aspect ratios, boundary multipliers, radius endpoints, ties, arbitrary small zero-mass vector errors and the favorable cone without an unbudgeted S term in the first estimate. It must obtain a single exceptional-center budget before taking the continuum shape supremum.

The isolated contact estimate and quadratic incidence identity do not supply this weighted, simultaneous interface. A scalar parameter-smoothing counterexample only rejects a generic auxiliary lemma. No counterexample to the full frozen theorem was found. No proof of its full scope was obtained. The correct disposition is UNRESOLVED / NO NOMINEE. No gate, acceptance, count or substantiality judgment is assigned. Further formalization, manuscript and publication work is not started.
