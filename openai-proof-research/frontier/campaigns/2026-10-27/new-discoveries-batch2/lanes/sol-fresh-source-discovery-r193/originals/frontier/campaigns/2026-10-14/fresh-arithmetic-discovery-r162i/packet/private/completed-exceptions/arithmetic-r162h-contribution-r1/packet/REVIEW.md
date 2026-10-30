# Arithmetic162h: independent full-scope contribution review

**Contribution verdict: TECHNICAL, conditional on the full correctness of the unchanged frozen theorem.** This review assigns no correctness, repair, acceptance, or count decision. It neither consulted nor waited for the other review.

The object assessed is the entire 2,064-byte FROZEN-STATEMENT.md, SHA256 `1d2799dba1c5bffca37724769974e56dc0e6c6ec2ac0196a01c3f15039ce6133`, together with the complete unchanged 23,791-byte AUTHOR-PROOF.md, SHA256 `92fe6bd2f718c85e558861588c3828dfdc039cff22f5e19fabcc67daa211db01`.

The conclusion assessed includes the uniform **expected squared** compact C^m error with exponent **1/4**, a **single Borel parameter choice** independent of the law, exponent, compact and order, **every** exact covariant probability on the full normalized univalent class, and the **complete critical probability law**, including its existence for every nonnegative Borel test and its zero affine mass. No weaker equality-only result is substituted.

The decisive reduction is not an assertion that the source already states the theorem. Finite component persistence, quantitative local Taylor expansion, and the actual source rank/transport construction fit together without a further nonroutine infinite-fiber selection operation. In fact the component injection can be used only to establish a counting inequality: order the saddles by an increased scalar height and apply the source's own Borel rank assignment. The analytic continuation to the entire frozen conclusion is given below, with the power and quantifiers retained. This is an independent comparison derivation; no author file is changed or proposed for repair.

## 1. Actual dependencies and what they pay

Write B for the pinned manuscript *Brennan's conjecture and sharp inverse-square integral means*, and S for *A strict inverse-first-power bound for univalent functions*, both September 24, 2026 at commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Exact paths, sizes, Git blob hashes and SHA256 are in private/canonical-authentication.json. All 23 text blobs were read, including both complete proofs, actual nested includes, figure definitions, wrappers and bibliographies; the two compiled PDFs were authenticated, not read. The full-tree authentication is independent of the inherited manifest.

B, `01-preliminaries`, Lemma `lem:compact-class`, pays the full compact normalized class and uniform local jets of F and Q=1/F'. Its `02-weighted-law` pays the affine identities and the differentiation mechanism for the logarithmic-derivative moments. The law construction in that section requires rho>2: its horizontal endpoint error is C(2/rho)^n. This review uses **only the exact covariance stipulated in the frozen hypotheses**, never an endpoint eigenmeasure construction.

B, `03-escape`, pays the actual inverse-area change of variables, tail-to-escape estimate, horizontal preimage-length bound and dyadic target cover. Its proof uses k>1/2 in the final summation, not k>1. B, `04-critical-pairing`, pays the determinant/Hessian formulas, finite critical counts above positive levels, Jordan superlevels, countable continuous root branches, Borel ranks and affine invariance. S, `04-strict-pairing`, Lemma `lem:good`, additionally pays the target-nullity of tied critical values. S, `05-strict-transport`, already carries the **full ratio of paired weights**, even if not uniformly bounded, through the displacement cutoffs and ordered box limits. B supplies exactly the fourth-power version of the target-area weight. These are actual proof operations, not just theorem labels.

The primary persistence input is Edelsbrunner--Letscher--Zomorodian, *Topological Persistence and Simplification*, published DCG 28 (2002), pp.511--533. Sections 2--4 were read completely, together with the introduction. The abstract pairing and its proof on pp.518--522 identify the younger surviving generator at a merger; printed p.523 gives its zero-dimensional implementation explicitly: a component is represented by its oldest unpaired vertex, merging two components retires the younger representative and keeps the older. The actual formulas and algorithm on printed pp.517--523 were also inspected in our own PDF renders. The input is finite, and is not represented as a theorem about Borel families of infinite conformal fibers. The finite-to-infinite and measurable interfaces needed here are proved below.

Hedenmalm--Shimorin, *Weighted Bergman spaces and the integral means spectrum of conformal mappings*, arXiv math/0406345v1, was independently read through the complete first four sections, beyond the author's selective first two sections. Section 2 rebases the Prawitz area inequality into a bidisk norm; Section 3 decomposes that norm by order of vanishing on the diagonal and expresses the components through derivatives; Section 4 integrates the rebased inequality and computes the analytic and complementary projections, obtaining its full main inequality. These are stronger antecedent analytic operations than merely citing a pointwise distortion theorem. They do not directly identify the frozen scaling deficit with a norm remainder in the portions read. I do not assert such an identification or use their unread recursive Prawitz/Milin proof as a premise. The elementary determinant identity and local energy estimate in §7 below independently supply the required analytic interface. The HS weighted-space parameter called beta is not identified with the law exponent in this review.

The original project-history bodies were read directly by the two authorized byte extents of i135, `[22410,25351)` and `[25351,35297)`, through the permitted heading boundary. They pay the subpower-gauge summation, conditional finite-boundary-measure weak estimate and one-map meromorphic tail analysis, while recording the unresolved E_gamma/W2 and critical-operator questions. None gives the present theorem by itself; none is settled by the theorem under review. No larger history clearance is claimed.

## 2. Exact-law geometry at the full frozen parameter range

Let eta=1-beta, k=(beta+3)/4, so beta in [3/4,1], k in [15/16,1]. Fix **any** Borel probability P satisfying the frozen covariance for every z=x+iy and every nonnegative Borel test. Put

    q=-iy F''/F'=a+ib,
    G_k=F-iy F'/k,
    J_k=det(DG_k)/|F'|^2.

The affine identities give q_(T_z F)(w)=q_F(z dot w) and the same identity for J_k. In particular, compactness of K bounds J_k **on all source points** uniformly over F and k by rebasing to i. No compact exhaustion constant enters this bound.

The constant covariance test gives E|Q(x+iy)|^2=y^(-beta). Uniform local jets justify two real derivatives under the expectation. At i, Q=1, and

    E a=-beta/2,   E b=0,   E|q|^2=beta(beta+1)/4.

The source's real columns of DG_k are (F'/k)(k+q) and (iF'/k)(k-1+q). Hence

    k^2 J_k=k(k-1)+(2k-1)a+|q|^2,
    E J_k(i)=(k-1)/k=-eta/(beta+3).                 (2.1)

These computations use the exact law, not its origin from an operator.

For clarity, the source escape mechanism remains valid throughout this range. On S0={|(z-i)/(z+i)|>=1/2}, |F|>=1/16. Test covariance with |F(z#)|^(-4), z#=(-x+i)/y, to get

    E[|F'(z)|^2 |F(z)|^(-4)]
        =y^(-beta-4) E|F(z#)|^(-4).

The involution preserves S0, sends y to 1/y and has absolute Jacobian y^(-3). Injective area change bounds the left spatial integral by 256 pi, so

    E integral_S0 y^(beta+1)|F|^(-4) dA <=256 pi.   (2.2)

For a map with finite integral, submean on B(z,y/2) gives

    (y^k/|F(z)|)^4
      <=C integral_(B(z,y/2)) (Im w)^(beta+1)|F(w)|^(-4)dA(w)
      ->0 as |x|+y->infinity.

The balls eventually avoid i and their integrands are tails of one finite integral. Constants in this local comparison can be uniform over the closed beta interval. The preimage of a compact target at heights bounded below is compact; its entire preimage has bounded height. For smooth compactly supported nonnegative psi on the target, integrate the horizontal second derivative to zero and the vertical second derivative twice to obtain

    integral_R psi(F(x+is)) dx
      =integral_(y>s) (y-s)|F'|^2 (Delta psi)(F) dA.

Injective target change bounds its absolute value by a finite height bound times ||Delta psi||_1, independently of s. For omitted targets in a bounded target disk, a witness V_xi=y^k/|F-xi|>=delta at height h<=y<=2h has y|F'|<=4|F-xi| by the quarter theorem. Rebasing on a fixed compact controls the image of the entire horizontal cell of length h by a disk of radius C_delta h^k. The trace estimate bounds the number of such cells by C_F/h. Their total target area is O(h^(2k-1)); since 2k-1>=7/8, its dyadic sum converges. Countably many radii and thresholds remove one target-null set. For interior targets a small target disk has compact inverse image, giving the same small-height exclusion. These facts and source-infinity escape give compact closed positive superlevels for almost every target, for almost every F. The map-dependent trace constants never become constants in the final quantitative estimate; they establish qualitative nullity only.

S's tie exclusion is also parameter-independent here. On two distinct regular branches z_j(xi),

    d_xi log V_xi(z_j(xi))(v)=Re[v/(F(z_j(xi))-xi)].

Injectivity makes the two real linear functionals different, so a tie set is locally a smooth curve. Countably many inverse charts plus planar Sard give a null set of singular or tied targets. Compact-source projection tests and rational-point superlevel tests make the combined good set Borel and affine invariant, with k fixed (or included as an additional compact parameter).

For each good pair (F,xi), the critical points are the regular roots of G_k=xi and satisfy

    V_xi(z)=k y^(k-1)|Q(z)|,
    Hess(log V)=(k/y^2) [[-(k+a),b],[b,k-1+a]],
    trace Hess(log V)=-k/y^2,
    det Hess(log V)=-k^4 J_k/y^4.                 (2.3)

Thus the positive sign is a saddle and the negative sign a finite maximum. There are finitely many critical points above every positive level: they form a closed discrete subset of a compact superlevel; a pole is not a root and cannot be an accumulation point of roots. The source minimum-principle proof makes every regular positive superlevel a finite union of Jordan disks. Its use of Delta log V=-k/y^2 needs k>0 only.

## 3. What the actual persistence operation supplies, including infinite fibers

At a saddle s, the two rising local germs belong to two different components of {V>V(s)}. This is a consequence of the source's no-hole geometry, not an additional persistence theorem. To check it directly, use the nondegenerate saddle normal form. It follows elementarily by solving the derivative in a negative direction for its critical graph, completing a negative square, and rescaling the remaining positive quadratic term. A path in the upper set connecting the two rising germs, together with the two arcs to s and loop removal, would give a Jordan curve on which log V>=log V(s), enclosing one descending sector. Its bounded interior lies in H. The strictly smaller interior values force an interior minimum, contradicting Delta log V<0; a possible pole is removed by a small circle on which log V is large. Thus the two components are distinct.

Each component has a largest representative: the pole if present, otherwise its greatest finite maximum. Its closure is inside the compact V(s)-superlevel. A point of larger value lies in its interior, so its supremum cannot be attained only on the boundary. If a pole belongs to the closure, a whole sufficiently small neighborhood of that pole lies in the upper set, and the pole is in the same component. Otherwise compactness gives a finite interior maximum. The good-target no-tie condition makes that representative unique.

Sweep the superlevel downward. On a compact slab without critical points, grad(log V)/|grad(log V)|^2 transports levels and components. At a finite maximum a component is born; at a saddle the two different components merge, with no hole created. A possible pole is the single oldest component. Above any chosen positive regular cutoff there are only finitely many critical events, so this is a finite forest of births and mergers. It can equally be encoded as a finite filtered graph, one vertex per birth, one edge per merger, with an initial vertex for the pole. It is precisely the zero-dimensional operation on ELZ p.523, with descending V corresponding to increasing time.

At each merger, pair the saddle with the smaller of the two representatives and keep the larger. The pole is always retained, so the retired representative is finite. A retired representative never becomes a representative again. This proves injectivity in every finite cutoff diagram. The choice at a saddle uses only the strict upper components and their greatest values; lowering the cutoff cannot change it. Any two saddles are covered by one common positive cutoff. Hence the component assignment is injective on the **entire possibly infinite** good fiber. Different target fibers are disjoint, so the same statement holds for fixed F on all its good saddles.

This extension does not require an infinite simplicial persistence theorem, a limiting matching, a choice of a uniform cutoff over F, or a positive lower bound on critical-value separations. Local finiteness above each level, already paid by the source, is exactly the compatibility that permits the finite primary operation to extend.

## 4. Quantitative gain and two complete measurable interfaces

Rebase at s. Its location becomes i and its target -i/k. On one fixed disk B(i,r0), the potentials

    ell_(F,k)(w)=k log(Im w)-log|F(w)+i/k|

have uniformly bounded derivatives through order three for every F in K and k in [15/16,1]. Indeed choose r0 so |F(w)|<=1/2 uniformly, using F(i)=0 and the compact-family derivative bound. Then |F(w)+i/k|>=1/2, and Im w stays away from zero. Let lambda be the positive Hessian eigenvalue at the rebased saddle, j=J_k(s)>0. Equation (2.3) gives

    lambda(lambda+k)=k^4 j.

Both lambda and j have universal upper bounds. Thus lambda>=c0 j with c0>0 universal. If e is a unit positive eigenvector, Taylor's estimate has the form

    ell(i +/- t e)-ell(i)>=lambda t^2/2-M t^3.

Choose one d>0 with d lambda<=r0/2 and M d<=1/4 for every permitted lambda. For 0<t<=d lambda the gain is at least lambda t^2/4. The two punctured segments stay in the two rising germs. At their endpoints it is at least d^2 lambda^3/4>=alpha j^3, with one alpha>0 independent of F,k,P. Both upper components consequently have representatives at least this high. The retired representative m(s) therefore satisfies

    V(m(s))>=V(s) exp(alpha J_k(s)^3).             (4.1)

This is more than strict rank comparison, but it is the direct local Taylor estimate for a uniformly C^3 bounded saddle, followed by the exact greatest-representative rule of the primary operation. The exponent three is lambda times a displacement of order lambda squared. No further quantitative topological theorem is hidden in it.

The author's literal component map is Borel by the following complete interface. The source contraction/second-countability argument enumerates nonsingular roots by countably many continuous local branches, activating only the first occurrence. The pole has at most one inverse branch. A Borel positive eigenvector and the endpoints just constructed give Borel points in the two components. Connectivity in the open set {V>h} can be tested by polygons with these endpoints and finitely many rational intermediate vertices. Each segment is required to have a positive rational margin both in its height and in

    (Im w)^k/h-|F(w)-xi|.

Checking all rational segment parameters with a fixed positive margin is a countable Borel test; the union over polygons and margins is equivalent to connectivity by openness and compactness of each path. This expression is continuous even at a pole. The predicate that an enumerated maximum belongs to a component and exceeds every other maximum in it is countable and Borel; first test for the pole, whose representative has value infinity. Select the smaller of the two unique representatives. The construction is intrinsic under source positive affine maps and target similarities: V is multiplied by one positive factor, and components, greatest representatives and the unordered two germs correspond. The eigenvector sign and root enumeration prove measurability but do not affect the geometric choice. Thus the literal component operation is Borel and affine equivariant on all good infinite fibers.

There is an even stronger integrated reduction which removes any need to transport that component selection. Set

    W(s)=V(s) exp(alpha J_k(s)^3)   for saddles.

A global universal bound J_k<=Jmax gives W<=M0 V, M0=exp(alpha Jmax^3). Thus only finitely many saddles satisfy W>=h for any h>0. The component injection (4.1), used just as a set-theoretic witness, proves

    #{finite maxima with V>=h} >= #{saddles with W>=h}.   (4.2)

Order saddles by decreasing W and maxima by decreasing V, breaking any ties lexicographically in source (x,y). Each point has finitely many predecessors; there are no missing ranks below an attained rank. Equation (4.2) implies that the maximum at the same rank as a saddle exists and has V>=W(s). The source's continuous root enumeration and countable predecessor sums prove that this **increased-height rank assignment** R is Borel. It is injective on every fiber. Under rebasing, J_k is unchanged and V and W acquire the same positive multiplicative constant; positive real source similarities preserve lexicographic order. Thus it is affine equivariant, exactly as in B's actual proof, and it still satisfies (4.1).

This alternate assignment is not a narrower theorem, a repair verdict, or an assertion about equality of the two assignments. It demonstrates that the proposed measurable infinite component interface is already covered by a finite primary counting operation plus the source's actual full measurable rank machinery. It establishes the strongest compatible reduction rather than stopping at failure of the naive raw-rank gain.

## 5. The gain survives the exact fourth-power transport

Take either assignment in §4. Write J_+=max(J_k,0), J_-=max(-J_k,0), and omega=y^(beta-1)|Q|^2. Disjoint local diffeomorphism charts for G_k give, for nonnegative Borel h,

    integral_H h omega J_+/- dA
      =integral_C sum_(G_k(z)=xi, +/-J_k(z)>0)
                  h(z)y^(beta-1)|Q(z)|^4 dA(xi).       (5.1)

This is the actual source area formula: division by |det DG_k|=|F'|^2 |J_k| supplies the extra |Q|^2. At a root, **exactly**

    y^(beta-1)|Q(z)|^4=(V_xi(z)/k)^4,
    4(k-1)=beta-1.                                  (5.2)

Define the pair ratio c_F(s)=[V(R_F(s))/V(s)]^4. It is Borel and equivariant and, by (4.1),

    c_F(s)>=exp(4 alpha J_k(s)^3)>=1+4 alpha J_k(s)^3.  (5.3)

A target-null statement cannot be inserted at the fixed root -i/k without proof. Apply (5.1) to bad targets in B0={|x|<=1,1<=y<=2}. Its target integral is zero for almost every F. Taking expectation and using equivariance and exact covariance gives

    0=2 log 2 E[J_+(i) 1_(bad at (F,-i/k))].          (5.4)

Only this weighted assertion is needed. Since J_+(i) is bounded it also disposes of its fourth power on the exceptional part. No unweighted almost-sure claim about goodness is inserted.

For N>=1, restrict to good saddles whose partner s'=x'+iy' satisfies

    N^(-1)<=y'/y<=N,   |x'-x|<=Ny.

Call the resulting equivariant Borel set D_N. These sets increase to all good saddles because each selected finite maximum is a point of H. For

    B={|x|<=S,1<=y<=Y},
    B'={|x|<=S+NY,N^(-1)<=y<=NY},

fiberwise injectivity and (5.2) give

    integral_B omega J_+ c_F 1_(D_N) dA
      <=integral_B' omega J_- dA.

This is the strict companion's actual proof with the inverse-square/fourth-power weights of B. The equality of target weights is retained, not replaced by a proportionality depending on a saddle. Taking expectation converts every equivariant nonnegative test to density dx dy/y. Thus

    2S log Y E[J_+(i)c_F(i)1_(D_N)]
      <=2(S+NY)(log Y+2 log N) E J_-(i).

At fixed N first let S tend to infinity, then Y tend to infinity. The finite right side bounds the left expectation even if c_F was initially unbounded. Finally let N increase to infinity by monotone convergence. Combining (5.3)--(5.4) yields

    E J_+(i)+4 alpha E[J_+(i)^4] <= E J_-(i).         (5.5)

The gain has no displacement or cutoff loss. Equation (2.1) now gives

    E[J_+(i)^4] <= eta/[4 alpha (beta+3)],
    E|J_k(i)|=2 E J_+(i)+eta/(beta+3)
             <= C eta^(1/4).                       (5.6)

The last step is the probability-space fourth-moment inequality and eta<=1/4; constants are uniform over beta and P. At eta=0 the same nonnegative inequalities apply. This completes the full proposed persistence-to-transport operation, not just a finite-fiber or equality version.

## 6. Covariance gives local determinant control uniformly over laws

J_1 below is defined by parameter k=1 for the same F, without changing the law's beta. The explicit quadratic formula for J_k and the uniform compact jets give, on each compact L in H,

    |J_1(z)-J_k(z)|<=C_L eta.

Use exact covariance with Phi(F)=|J_k,F(i)|. Since J_k is equivariant,

    E[|Q_F(z)|^2 |J_k,F(z)|]=y^(-beta) E|J_k,F(i)|.

Compactness of K and nonvanishing of Q give a positive minimum of |Q| on K times L; y^(-beta) is uniformly bounded on L times [3/4,1]. Therefore

    sup_(z in L) E|J_1,F(z)|<=C_L eta^(1/4).          (6.1)

These constants involve only L and the fixed normalized class and parameter interval. No support restriction on P has been introduced.

## 7. Determinant to analytic approximation without another exponent loss

Put g=F', D=det D(F-iyF'), and H_F=D/y. Directly from the real determinant,

    D=y^2|g'|^2+y Im(g' conjugate(g)),
    H_F=y|g'|^2+Im(g' conjugate(g)).

The elementary identity that closes the analytic comparison is

    Delta H_F=4y |g''|^2=4y |F'''|^2.                (7.1)

Here is its full algebraic mechanism, rather than an appeal to a named estimate. With z and conjugate(z) as Wirtinger variables,

    2i H_F=(z-conjugate(z))g' conjugate(g')
                       +g' conjugate(g)-g conjugate(g'),
    partial_z(2i H_F)=g''[(z-conjugate(z))conjugate(g')+conjugate(g)],
    partial_bar_z partial_z(2i H_F)
                       =(z-conjugate(z))|g''|^2.

Since Delta=4 partial_z partial_bar_z and z-conjugate(z)=2iy, (7.1) follows for every holomorphic F, without polynomial approximation or division by F''. This is a local product-rule cancellation, not an unidentified global analytic stability theorem. The finite algebra check in the author packet is not used as its certificate.

Choose a fixed nonnegative smooth compactly supported chi in H which equals one on a neighborhood U of a prescribed compact. Integrating (7.1) twice by parts gives

    4 integral chi y |F'''|^2 dA = integral H_F Delta chi dA.

On the support of chi, |H_F|=|F'|^2 |J_1|/y. Compact-family bounds and (6.1) consequently imply

    E integral_U |F'''|^2 dA <= C_U eta^(1/4).       (7.2)

All integrals over this support are uniformly finite; the signed right side is bounded by its absolute integral before taking expectation. No boundary behavior of F is assumed.

For any smaller compact L with a fixed disk neighborhood inside U, submean bounds sup_L |F'''|^2 by a constant times the **single** area integral in (7.2). Cauchy's formula on a further nested fixed neighborhood bounds every higher derivative in the same way. Thus for each finite j>=3,

    E sup_L |F^(j)|^2 <= C_(L,j) eta^(1/4).          (7.3)

This is a deterministic supremum bound before expectation; it is not an illicit interchange of E and sup. The maximum over finitely many orders is bounded by their sum, costing only an order-dependent constant.

Let c(F)=F''(i) and P_c(z)=(z-i)+(c/2)(z-i)^2. For a given nonempty compact E, its convex hull with {i} is a compact subset of H. Taylor's integral remainders along its segments bound the C^0, C^1 and C^2 errors from P_c by constants times the supremum of |F'''| on that hull. For orders >=3 the derivatives of P_c vanish. Equation (7.3) therefore yields, for every finite m>=0,

    E [max_(0<=j<=m) sup_E |F^(j)-P_c^(j)|]^2
        <=C_(E,m) eta^(1/4).                        (7.4)

The same exponent remains because every analytic estimate controls a squared norm linearly in the expected absolute determinant. There is no square root of eta^(1/4) taken in the desired squared error.

## 8. One Borel choice for all compacts, orders, exponents and laws

Let C0={c:|c+i/2|=1/2}. Define the fixed radial projection

    pi(c)=-i/2+(c+i/2)/(2|c+i/2|),  c!=-i/2;
    pi(-i/2)=0.

It is Borel everywhere. Including the center convention,

    |c-pi(c)|=abs(|c+i/2|-1/2)
      <=2 abs(|c+i/2|^2-1/4)
      =2 abs(|c|^2+Im c)=2|J_1,F(i)|.              (8.1)

The elementary radius inequality uses r+1/2>=1/2, including r=0. The equality J_1(i)=|c|^2+Im c follows from q(i)=-ic and the k=1 formula. Uniform boundedness of J_1(i) turns (6.1) and (8.1) into

    E|c-pi(c)|^2 <= C E|J_1(i)| <= C eta^(1/4).     (8.2)

For c0 in C0 other than zero, |c0|^2+Im c0=0 implies Im(1/c0)=1. Hence a=i-1/c0 is real. Define A(F)=i-1/pi(F''(i)) when pi(F''(i))!=0 and A(F)=infinity otherwise. The circle-to-compactified-line map is a homeomorphism; A is Borel and involves **none** of P, beta, E or m.

P_c0 equals the frozen F_a for this a, and P_0=F_infinity. These all belong to K: F_a'= (z-a)/(i-a), and F_a(z)=F_a(w) implies z=w or z+w=2a, the latter impossible for z,w in H. The affine case is immediate. The compact C^m distance from P_c to P_pi(c) is bounded by C_(E,m)|c-pi(c)|; the derivatives of order above two vanish. Combining (7.4), (8.2) and (u+v)^2<=2u^2+2v^2 gives exactly

    E [max_(0<=j<=m) sup_(z in E)
           |F^(j)(z)-F_(A(F))^(j)(z)|]^2
       <=C_(E,m)(1-beta)^(1/4).                     (8.3)

Every constant is selected from fixed compact-family, local-radius, cutoff and finite-order bounds. None depends on P or beta. E need not have interior or a smooth boundary; its slightly larger neighborhoods are auxiliary only. The argument is valid for every finite m and every nonempty compact E, using the same A. It proves the all-law statement on the full K, not on power maps or a finite-dimensional subclass.

## 9. Complete critical classification and all Borel tests

At beta=1, (8.3) is zero. Apply it on one countable compact exhaustion of H, with m=0. Outside one null set, F=F_(A(F)) everywhere. The map a->F_a from the compactified real line into K is continuous, including infinity, and injective; it is therefore a homeomorphism onto a compact Borel subset. Let mu be the induced parameter law.

For finite a the affine identities are

    T_(x+iy)F_a=F_((a-x)/y),
    |Q_(F_a)(x+iy)|^2=(1+a^2)/[(a-x)^2+y^2].        (9.1)

The affine model is fixed and Q=1. Since T_z is invertible on K, its preimage of the affine model is that model itself. Test covariance on this singleton: mu({infinity})=y^(-1)mu({infinity}) for every y>0. Thus the affine mass is zero.

Set y=1 and use the nonnegative Borel parameter test phi(b)=(1+b^2)psi(b), where psi is compactly supported and nonnegative. Extend this test by zero off the compact model subset of K. Equation (9.1) and covariance give

    integral psi(a-x)(1+a^2)dmu(a)
      =integral psi(a)(1+a^2)dmu(a).

The measure sigma=(1+a^2)mu is locally finite and translation invariant. Such a measure is c da: equal-length half-open intervals have equal mass, subdivision gives rational proportionality and monotone limits give all lengths. Local finiteness rules out atoms; intervals determine the measure. Therefore mu=c da/(1+a^2), and total probability fixes c=1/pi. This proves uniqueness of the entire law, not merely its possible support.

Conversely, the Cauchy parameter law gives a probability on K and for every nonnegative Borel phi, with infinite values and infinite integrals allowed, the substitution a=x+yb gives

    integral_R [(1+a^2)/((a-x)^2+y^2)]
          phi((a-x)/y) da/[pi(1+a^2)]
       =y^(-1) integral_R phi(b) db/[pi(1+b^2)].     (9.2)

There is no integrability restriction in this nonnegative change of variables. Taking phi(a)=Phi(F_a) verifies precisely the original covariance for every required Borel Phi. This proves critical existence, uniqueness, the zero affine mass, and the full test-function assertion together.

## 10. Contribution judgment and boundaries

The author correctly identifies an addition beyond raw-rank strictness: a quantitative gain tied to J_+ and a rate for the whole exact-law family. Raw strictness by itself supplies no uniform rate; equality classification plus compactness supplies at most an unspecified modulus. Neither insufficient shortcut is the basis of this verdict.

After the strongest compatible reduction, however, each added operation is paid at the required interface. The source already supplies finite-above-level Jordan geometry, countable root branches and the full Borel/affine rank argument. The primary elder rule supplies the injective component witness; the uniformly bounded C^3 saddle estimate supplies its cubic gain. Its finite cutoff consistency is explicit, and the increased-height rank construction shows why the infinite Borel transport presents no new selection obstruction. The source strict transport accepts the entire ratio; the exact inverse-square weight makes it the fourth power, yielding (5.6). The local product-rule identity, cutoff integration, holomorphic estimates and one fixed coefficient-circle projection give the squared compact error with no further exponent loss. The critical measure then follows by elementary weighted translation invariance and the full nonnegative change of variables.

Consequently there is no specific closed **nonroutine** residual operation left after this composition. TECHNICAL is the full-scope contribution judgment even if the unchanged author theorem and proof are wholly correct. This does not claim that the exact statement appeared verbatim in the primary literature, that its assembly required no care, or that no neighboring theorem could be substantial. It is the acceptance-rule comparison of proof operations actually needed by this frozen statement.

The exact covariance hypothesis is retained throughout. Nothing here constructs a law at critical operator radius two, controls finite-scale extremizers or approximate laws, supplies uniform critical operator growth, or settles E_gamma/W2, radial/weak/Lorentz/Orlicz endpoints, boundary representations or older countable-contact problems. Those applications are neither repair requirements nor extra contribution credit. All supplied old frozen scopes and dispositions remain unchanged. This review assigns no campaign count and makes no worldwide-priority or exhaustive-literature assertion.

## 11. Reading and isolation limits

The separate private READING-ISOLATION.md and machine-readable reading records are part of this review. All mandatory author inputs were read completely; the three notes and both FINAL and outside REPORT were read as author claims, not independent gates. All 25 canonical blobs matched the complete 13,223-entry tree at the prescribed hash. Actual semantic reading covers all 23 canonical text files, not the two source PDFs. All local mathematical includes were resolved. Four glyph-to-Unicode system includes are typography and were not read.

ELZ semantic reading ends with the opening of Section 5 on printed p.523; its later simplification/experiments are not invoked. HS semantic reading covers the preamble and complete Sections 1--4, ending at byte 68139. Later Sections 5--7, bibliography and recursively cited primary proofs were not read. No essential step in the integrated derivation is delegated to them. No additional download, external search, browser operation or literature-completeness claim occurred. Protected source/primary/history bodies and their metadata remain local/private.

Only the admitted immutable packet and exact direct paths/extents were selected. There was no broader campaign, eligible-history scan or excluded-body traversal, no nested agent, and no inspection or query of the other review or any peer activity. Therefore there are no new broad-scan false admissions; this also means no new clearance of omitted originals. The supplied coarse guards can omit useful originals and opaque aliases can escape them; perfect classification is not claimed. Exact exceptions did not widen any namespace.

The author files' hashes, sizes and modes were recorded before mathematical reading and compared again at the end. Own manifest, detached anchors, read-only verifier and tiny copied controls concern exact artifacts only. They are not theorem certificates or mathematical gates.
