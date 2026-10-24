# T333Q209 — author proof at the unchanged frozen scope

This is an author research proof, relative to the stipulated Source333 operations. It is not an independent correctness or contribution review. The exact target is FROZEN-STATEMENT.md, SHA256 9008ac4ac426a6ff7f4419aaab3f6dcd0e48b73b3186f53b0122b3ab3248091a. No downstream manuscript or formalization is being prepared.

## 1. Conventions and the linear obstruction

Let all functions be 2π-periodic in x and y. The average is

    av f = (4π²)^(-1) ∫_[0,2π]² f dx dy.

Use the coordinate norms specified in the frozen statement. Put

    n1=(cos x,sin x,0,0),       e1=(-sin x,cos x,0,0),
    n2=(0,0,cos y,sin y),       e2=(0,0,-sin y,cos y).

This is a global orthonormal frame along F0=n1+n2, and F0_x=e1, F0_y=e2. For a vector field along F0 write

    U=u1 e1+u2 e2+v1 n1+v2 n2.

Define γ(F)ij=<F_i,F_j>, L=Dγ(F0), and the symmetric bilinear tensor

    B(U,V)ij = (<U_i,V_j>+<V_i,U_j>)/2,     Q(U)=B(U,U).

This B is polarization of the quadratic metric term, not the second fundamental form. Direct differentiation of the frame gives

    (LU)11=2(∂x u1+v1),
    (LU)12=∂x u2+∂y u1,
    (LU)22=2(∂y u2+v2).                                  (1.1)

Consequently γ(F0+U)=g0+LU+Q(U) exactly, with no higher remainder. Let ℓ(A)=av A12. Integration of derivatives shows ℓ(LU)=0.

Conversely every smooth symmetric A with ℓ(A)=0 is in the range of L. Let Δ=∂x²+∂y², and define Δ^(-1) on mean-zero periodic functions by Fourier multiplier -1/(p²+q²) for (p,q)≠(0,0), with zero constant coefficient. Set

    u1=∂y Δ^(-1) A12,       u2=∂x Δ^(-1) A12,
    v1=A11/2-∂x u1,        v2=A22/2-∂y u2.                (1.2)

Let P(A) be the field with these frame coefficients. Then LP(A)=A. This is a global periodic operator. It does not require a global transversal on an open coordinate domain.

We use the deliberately conservative bound

    ||P(A)||_(Cs) <= C_s ||A||_(C^(s+4)),   s≥0.           (1.3)

To prove it, each scalar multiplier in (1.2) has bounded magnitude on nonzero Fourier indices; those with one derivative have still smaller magnitude. Integration by parts in the coordinate with larger frequency bounds a Fourier coefficient of a C^(s+4) function by C_s ||A||_(C^(s+4))(1+|(p,q)|)^(-s-4). After s derivatives the absolute sum is bounded by a constant times ∑_(p,q) (1+|(p,q)|)^(-4)<∞. Derivatives of the fixed frame only change the constant. Smooth inputs give smooth outputs by applying this estimate at every s. Thus range L=ker ℓ, including a proved right inverse on that codimension-one subspace.

The usual full linear right-inverse premise fails at F0. This is an explicit periodic obstruction, not a claim that an open-domain or generic-map theorem is false.

## 2. Two bending modes and a nonsingular scalar adjustment

For a smooth scalar φ set

    V(φ)=φ_x e1-φ_y e2-φ_xx n1+φ_yy n2.                  (2.1)

Equation (1.1) gives LV(φ)=0. For φ=cos(px+qy), with θ=px+qy, the derivatives have the following frame components, ordered as (n1,e1,n2,e2):

    V_x=(p(1-p²)sinθ, 0, pq²sinθ, pq cosθ),
    V_y=(-p²q sinθ, -pq cosθ, q(q²-1)sinθ, 0).          (2.2)

It follows that

    ℓ(Q(V(φ))) = (pq/2)[p²(p²-1)+q²(q²-1)].             (2.3)

Let

    V+=V(cos(2x+y))/sqrt(12),
    V-=V(cos(2x-y))/sqrt(12).

Then ℓ(Q(V+))=1 and ℓ(Q(V-))=-1. Also ℓ(B(V+,V-))=0. Indeed, in the orthonormal frame (2.2), every mixed product is a constant multiple of sin(2x+y)sin(2x-y), cos(2x+y)cos(2x-y), or a sine–cosine product. Each has zero average on the torus. The moving ambient frame contributes no extra factor to a dot product because the components are taken in the same orthonormal frame at the same point.

For any symmetric H with ||H||_(C0)≤1 put c=ℓ(H), so |c|≤1, and define

    a=(1+c/2)^(1/2),    b=(1-c/2)^(1/2),
    W1=V(H)=a V+ + b V-.                                (2.4)

Then

    LW1=0,       ℓ(Q(W1))=a²-b²=c,
    2ℓ(B(W1,V+))=2a ≥ sqrt(2).                           (2.5)

All spatial derivatives of W1 are bounded by constants depending only on their order. The amplitudes a,b are numbers depending smoothly on c on a neighborhood of [-1,1]. Crucially, the scalar derivative in (2.5) stays nonzero even when the requested obstruction c is zero. This permits one uniform finite construction for perturbations of both signs and for vanishing mean shear.

## 3. Finite coefficient construction for arbitrary nearby metrics

Fix J≥2. For a smooth H with ||H||_(C0)≤1, we construct smooth W1,...,WJ such that

    Fapp=F0+∑_(j=1)^J ε^j Wj,
    γ(Fapp)=g0+ε²H+∑_(j=J+1)^(2J) ε^j Ej,               (3.1)

where all Wj and Ej depend on H but not on ε. All equalities here are exact polynomial identities.

Start with W1 from (2.4). Since ℓ(H-Q(W1))=0, define a provisional

    W2=P(H-Q(W1)).                                       (3.2)

This cancels the degree-two coefficient. Suppose coefficients below degree j have been canceled, where 3≤j≤J, and W_(j-1) is currently provisional. Form

    Zj=∑_(a+b=j; a,b≥1) B(Wa,Wb).                        (3.3)

Only already defined indices a,b≤j-1 occur. Let

    βj= -ℓ(Zj)/(2a),                                    (3.4)

where a is the positive scalar from (2.4). Replace W_(j-1) by W_(j-1)+βj V+. Its L-image is unchanged. Its effect on the degree-j quadratic coefficient is exactly 2βj B(W1,V+), because the only degree-j pairs containing index j-1 are (1,j-1) and (j-1,1). The coefficient has become

    Zj'=Zj+2βj B(W1,V+),       ℓ(Zj')=0.

Set Wj=-P(Zj'). This cancels degree j. The alteration does not affect any lower coefficient: L(V+)=0, and its first quadratic interaction has degree j. Its square has degree 2j-2≥j+1, since j≥3. Thus the induction is triangular. WJ need not receive any further scalar adjustment. Expanding the exact quadratic metric map proves (3.1).

Here is a finite derivative budget valid uniformly for this recursion. For every s≥0 and every index j≤J,

    ||Wj||_(Cs) ≤ C_(s,J)
    whenever ||H||_(C^(s+6j))≤1.                        (3.5)

For a provisional coefficient the same, or a stronger bound, holds. The proof is a finite induction using (1.3),

    ||B(U,V)||_(Cs) ≤ C_s ||U||_(C^(s+1))||V||_(C^(s+1)), (3.6)

and |ℓ(A)|≤||A||_(C0). To construct Wj in Cs, the quadratic coefficient in (3.3) is needed through s+4; previously constructed fields are therefore needed through s+5. The largest previous index is j-1, costing at most s+5+6(j-1)≤s+6j derivatives of H. Finalizing a provisional Wj adds a scalar determined from a first derivative of Wj and first derivatives of the preceding coefficients. For s=0 this additional derivative is covered by the sixth derivative in the budget; for s≥1 it is already included in the observation order. More explicitly, the provisional Wj requires at most s+6j-1 derivatives for s≥0, so its C1 bound uses at most 6j derivatives; this bounds its scalar adjustment even when the requested output order is zero. The denominator 2a is bounded below by sqrt(2), and the fixed modes have bounded derivatives of every order. Product norms yield constants independent of H on each displayed unit ball. For j=2, (3.2) starts with loss four, within this bound. This proves (3.5), including its stated provisional strengthening.

As a consequence, for any R≥0, taking

    r=R+2+6J                                             (3.7)

and ||H||_(Cr)≤1 gives

    ||Fapp||_(C^(R+2)) ≤ A_(R,J),
    ||Fapp-F0||_(C^(R+2)) ≤ A_(R,J) ε,
    ||γ(Fapp)-(g0+ε²H)||_(CR) ≤ A_(R,J) ε^(J+1),          (3.8)

for 0<ε≤1. In the remainder, each Ej is a finite sum of products of first derivatives of W_a,W_b, so the first two inequalities supply its CR bound. In particular Fapp is immersive and has a uniformly nonzero vector-valued second fundamental form for all sufficiently small ε, uniformly over the input unit ball. This follows from C2 closeness to F0: at F0 the pure normal components are -n1 and -n2 and the induced metric is g0.

No convergence of the formal series is asserted or needed. J will be a fixed finite integer depending only on the requested output order.

## 4. Exact correction with a fixed positive reference

We now carry the compatible paid Source333 smoothing mechanism far enough to obtain a uniform finite-input estimate. This step is necessary: merely substituting a varying target into the statement of its exact-correction proposition would not justify uniformity over a finite-norm ball.

Use the following Source333 interfaces, all at the stipulated pin:

- preliminaries.tex, Lemma `lem:phase-data`: fixed positive good-phase data on a C2 neighborhood of an immersion with nowhere-zero second fundamental form;
- small-modes.tex, Proposition `prop:small-increment`, in its unperturbed case, including finite weighted-input dependence and support formulas;
- exact-correction.tex, Lemma `lem:finite-order-smoothing`, equations `eq:exact-smoothing-tail`, `eq:exact-error-identity`, `eq:exact-all-order-recurrence`, and its finite-block convergence construction.

Choose the phase data once at F0 with reference g0, and a fixed C2 neighborhood O of F0 where all their metric, phase, and second-form margins persist. Choose concentric tensor neighborhoods of g0 as in the source small-increment proposition. All these choices are independent of the eventual perturbation H.

Fix m≥2 and put

    k0=max(10,2m+2),     R=40(k0+1),     J=8k0+2.          (4.1)

We prove the following precise bridge. Suppose for each sufficiently small ε a smooth f and a smooth target metric g satisfy

    ||f-F0||_(C2) ≤ A ε,
    ||f||_(C^(R+2)) + ||g||_(CR) ≤ A,
    ||g-g0||_(C0) ≤ A ε²,
    ||γ(f)-g||_(CR) ≤ A ε^(J+1).                         (4.2)

Then there is a smooth exact immersion F with γ(F)=g and

    ||F-f||_(Cm) ≤ ε³                                   (4.3)

for all sufficiently small ε. The threshold depends only on m,A and the fixed phase/atlas data, not on any derivatives of f or g above the finite orders in (4.2). Higher derivatives may affect the finite waiting times, but not the estimate or initial threshold. No regularity of the choices in ε or g is asserted.

### 4.1. One step and its target-independent constants

For a current map G, scale t, and integer k≥k0, set

    β=6/5, λ=11/10, τ=t^β, s=t^λ, δ=t^k,
    r(k)=q(k)=40(k+1),
    H=δ^(-2)(g-γ(G)),
    S_l(t;G,H)=∑_(i=0)^l t^i (||G||_(C^(i+2))+||H||_(Ci)).

The letter H in this subsection is the normalized current defect; it need not be the initial normalized metric perturbation in Section 3. Assume G lies in a fixed smaller C2 neighborhood within O, H is in the smaller C0 neighborhood of g0, and S_(r(k))≤B, for a fixed sufficiently large B.

Smooth G and H at scale s with moment order r(k). Apply the paid small-increment construction at G_s=S_sG to

    H_s-(δ'/δ)²g0,

where either δ'=τ^k or δ'=τ^(k+1). This input lies in the permitted positive tensor neighborhood when t is small. All its weighted derivatives required at any fixed finite stage are bounded using B and the fixed derivatives of g0. In particular, no unprescribed high derivative of g enters here. The result U satisfies

    |U|_(l,τ) ≤ C_(l,k) δτ,
    |E|_(l,τ) ≤ C_(l,k)[δ(τ/s)^q+δ³/τ],                 (4.4)

where

    E=γ(G_s+U)-γ(G_s)-δ²[H_s-(δ'/δ)²g0].

Put G'=G+U and H'=δ'^(-2)(g-γ(G')). Quadraticity of γ gives the exact identity

    δ'²(H'-g0)=δ²(H-H_s)-E-C(G-G_s,U),                   (4.5)

with C(A,U)ij=<A_i,U_j>+<A_j,U_i>. There is no square of the smoothing tail. This is the source error identity with a fixed positive reference in place of its target as reference; the actual target g cancels algebraically.

The paid smoothing-tail bound is

    |j²(G-G_s)|_(l,τ)+|H-H_s|_(l,τ)
      ≤ C_(l,k)[B(s/t)^r+S_l(t;G,H)(τ/t)^r].             (4.6)

Here the constants in (4.4) use finitely many weighted derivatives of the smoothed input, all supplied by the finite bound S_r≤B. The potentially large true-input derivatives in (4.6) enter only linearly. Multiplying (4.6) by |dU|_(l,τ)≤Cδ and using (4.5) therefore preserves this linear dependence.

For the more demanding choice δ'=τ^(k+1), the six relevant exponents of t after division by δ'² are, respectively,

    δ(τ/s)^q:                (13k+8)/5,
    δ³/τ:                   (3k-18)/5,
    δ² B(s/t)^r:             (18k+8)/5,
    δ² S_l(τ/t)^r:           (38k+28)/5,
    δ B(s/t)^r:              (13k+8)/5,
    δ S_l(τ/t)^r:            (33k+28)/5.

They are all positive for k≥10. Thus, in every fixed observation order l,

    |H'-g0|_(l,τ) ≤ C_(l,k)t^(1/5)(1+S_l),
    S_l(τ;G',H') ≤ ||G||_(C2)+||g0||_(C0)
                         +C_(l,k)t^(1/5)(1+S_l).        (4.7)

The map part follows because every inherited weighted derivative of positive order gains τ/t=t^(1/5), and |j²U|_(l,τ)≤Cδ/τ. These are precisely the source all-order estimates, now with constants depending only on B, k,l, fixed geometry and fixed g0. The scale threshold for the controlled order and defect neighborhood also has this uniformity. Smallness of δ/τ keeps the small-increment segment in the same permitted geometry.

### 4.2. Initialization from finite norms

Let e=γ(f)-g, t0=ε⁴, δ0=t0^k0=ε^(4k0), and

    G0=sqrt(1-δ0²) f.

Then its normalized defect is exactly

    H0=g+(1-δ0^(-2))e.                                  (4.8)

Since J+1-8k0=3, (4.2) implies ||H0-g||_(CR)≤C_A ε³. It is therefore in the required C0 neighborhood of g0, and its CR norm is bounded uniformly. The C^(R+2) norm of G0 is also bounded uniformly. Choose B, depending on A,m and the fixed data, so large that

    ||G||_(C2)+||g0||_(C0)<B/4

throughout the small C2 neighborhood of f used below. For small ε, the weighted positive-order terms in S_R(t0;G0,H0) tend to zero uniformly; enlarge B once if necessary to obtain S_R≤B/2. Thus every initial controlled-order hypothesis holds with an ε threshold independent of all higher derivatives.

The initial displacement satisfies

    ||G0-f||_(Cm)≤C_A δ0²=C_A ε^(8k0)≤ε³/4.             (4.9)

The last inequality is uniform because m≤R+2 and k0≥10.

### 4.3. Summability and passage through all orders

At each step replace t by t^(6/5). The scales are

    t_n=t0^((6/5)^n),       ∑_(n≥0)t_n<1/4

after decreasing the uniform ε threshold. Within block k impose, in addition to the controlled-order conditions, the bound

    ||U||_(C^floor(k/2))≤ε³ t.                            (4.10)

This threshold exists by (4.4), because

    ||U||_(C^floor(k/2))≤C_k t^(k+(6/5)(1-floor(k/2)))

and the exponent exceeds 1. In the initial block it holds uniformly at t0=ε⁴: for k0≥10,

    4[k0+(6/5)(1-floor(k0/2))-1]>3.

Subsequent k-dependent thresholds may be smaller, but the scale tends to zero and each is a strictly positive number for fixed ε and k.

Equations (4.9) and (4.10) keep every finite-stage map within ε³/2 of f in Cm, hence also in C2 since m≥2. The fixed geometry therefore persists throughout, uniformly for small ε. The controlled-order recurrence (4.7) preserves S_(r(k))≤B and the defect neighborhood if t is below its fixed-block threshold.

For completeness, high derivatives cause no infinite stall. While k is fixed, apply (4.7) in any fixed order l, without assuming a bound there. Writing x_n=S_l(t_n;G_n,H_n), it gives

    x_(n+1) ≤ B/4+c_n(1+x_n),  c_n=C_(l,k)t_n^(1/5)→0.

Each x_n is finite because all finite stages are smooth. Once c_n≤1/4 the sequence is bounded; then limsup x_n≤B/4. In particular it is eventually ≤B. Apply this with l=r(k+1), wait also until the next block's scale and (4.10) thresholds hold, and impose C_(r(k+1),k)t^(1/5)(1+B)≤B/2. Now make one transition using δ'=τ^(k+1). Equation (4.7) gives the new higher norm <B. Every block has finite length; k tends to infinity.

Since floor(k0/2)≥m, all increments already satisfy the Cm summability bound (4.10). For every higher fixed order l, sufficiently late blocks have floor(k/2)≥l, so the same estimate makes the tail summable in Cl. Thus there is a single limit F smooth in x,y. The defects δ²H tend to zero in C0, while G_n→F in C1, so γ(F)=g exactly. Positive definiteness of g gives rank two at every point. Summing (4.9)–(4.10) gives ||F-f||_(Cm)≤ε³/2, in particular (4.3).

Higher derivatives affect only the finite waits just described. No compactness of a finite-norm ball in C-infinity was used, and no smooth dependence on data was inferred. This proves the bridge with its complete uniformity claim.

## 5. Completion of the frozen estimate and global embedding

Fix m≥2 and let k0,R,J be (4.1). Formula (3.7) gives exactly

    r=R+2+6J=88k0+54=r_m.

For h≠0 put ε=||h||_(Cr)^(1/2) and H=h/ε². Then ||H||_(Cr)=1. Section 3 supplies f=Fapp with all estimates (4.2), for one A depending only on m and the fixed torus data. Take g=g0+h. Section 4 gives a smooth immersion F with this exact metric and

    ||F-F0||_(Cm) ≤ ||Fapp-F0||_(Cm)+||F-Fapp||_(Cm)
                  ≤ A_m ε+ε³ ≤ C_m ε.                 (5.1)

Choose eta_m>0 so that ε<sqrt(eta_m) satisfies every uniform threshold in Sections 3 and 4 and the compact embedding condition below. The constants depend only on m and the fixed coordinate/atlas/norm conventions. If h=0 use F0.

We give the global embedding argument to distinguish it from mere rank. A smooth embedding of a compact manifold is open in C1. At each point of F0 choose a fixed linear projection of R4 to R2 whose derivative on the tangent plane is invertible. In sufficiently small convex coordinate balls, after an invertible linear normalization, the projected derivative of F0 is within 1/4 of the identity. For sufficiently C1-close F it is within 1/2. Integration along line segments then gives a uniform positive lower Lipschitz bound for the projected F on each such ball, hence local injectivity. A finite cover with smaller balls and a Lebesgue number handles all pairs close to the diagonal of T²×T². On the complement of this neighborhood of the diagonal, |F0(p)-F0(q)| has a positive minimum. C0 closeness prevents collisions there. F is therefore injective and immersive; compactness makes it a homeomorphism onto its image. It is a smooth embedding.

Apply this argument using (5.1), since m≥2. This is compatible with the source's immersion correction: it requires only its established C1 proximity, not exterior equality or an embedding assertion in Source333. The earlier r107 proof already contains compact embedding openness and a stronger oblique-projection primitive argument; neither is claimed as a new operation here.

## 6. Exact lower bound and optimality

Let h_t have the entries in the frozen statement, and let a C1 map F induce g0+h_t. Put U=F-F0. The mixed metric identity is

    t=<e1,U_y>+<e2,U_x>+<U_x,U_y>.

For each fixed x, e1 depends only on x, so the integral of <e1,U_y> in y vanishes by periodicity. Similarly the integral of <e2,U_x> in x vanishes. Thus

    4π² t=∫_T² <U_x,U_y> dxdy.                          (6.1)

Cauchy–Schwarz in R4, followed by 2ab≤a²+b², yields

    ∫_T²(|U_x|²+|U_y|²) dxdy ≥8π²|t|.                  (6.2)

Also |t|≤sup|U_x| sup|U_y|≤||U||_(C1)², proving the exact norm lower bound. No smallness of U, injectivity of F, second derivative, or selection regularity is used in this argument.

For every finite r, ||h_t||_(Cr)=|t|, and g0+h_t is positive definite for |t|<1. If an estimate with exponent α>1/2 held with any fixed C,eta,r, choose a nonzero |t|<min(eta,1) so small that C|t|^α<|t|^(1/2). Equations (6.1)–(6.2) contradict the estimate for every possible realizing map. This proves exactly the frozen optimality assertion.

## 7. Scope, attribution and remaining review obligations

The author argument covers the entire unchanged frozen statement. No unresolved mathematical bridge is being withheld from that statement. This assertion is an author submission, not a correctness verdict. Independent adversarial checking should focus particularly on the six-derivative finite recursion budget and on the fixed-reference identity (4.5), initial finite norms and later waiting-time quantifiers.

The genuinely additional author work offered for review is the two-sign periodic cokernel construction, its finite all-orders cancellation with uniform denominators, the finite-input fixed-reference correction bridge, and the matching lower bound. Fourier inversion, coefficient matching, partitions, smoothing, good-phase small modes, the exact block mechanism and compact embedding openness are credited to elementary/classical/source/prior-history operations. No claim is made that the abstract idea of resolving a cokernel quadratically is new.

This does not assert a global metric-space section, a parametric h-principle, relative prescribed jets, equivariance, a nonorientable normal-bundle classification, finite-regularity input, ambient metric changes, or a simultaneous estimate in all norms for one selected map. The normal frame used in Sections 1–3 is the explicit frame of the fixed orientable product torus; no global frame is inferred for arbitrary surfaces. All actual exact corrections remain in Euclidean R4.

The pinned comparator is only a declaration completed with `sorry`; there is no proved Lean endpoint support for Source333 from that file and no formal support for this author theorem. Primary literature and guarded history access limits are detailed separately. The parent alone may arrange independent reviews, integrate, assign grades, or change counts.
