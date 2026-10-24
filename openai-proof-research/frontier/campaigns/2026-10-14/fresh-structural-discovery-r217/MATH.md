# r217 durable mathematical derivations — prefreeze

No theorem frozen. No author correctness/contribution/count assessment.

## Exact working objects

X is a closed connected oriented smooth four-manifold; ordered smooth closed two-forms omega_i span a positive three-plane at every point for the wedge product. The integrated Gram matrix is G_ij=int omega_i wedge omega_j; G=I is a cohomology normalization, not a pointwise orthogonality condition. For arbitrary positive mu, omega_i wedge omega_j=2Q_ij mu. The determinant-one volume convention fixes mu from det Q=1. A normalized hyperkahler endpoint has Q=I and int mu=1/2. Constant GL(3,R) normalization is already paid; retain original ordered cohomology marking and orientation, not an implicit SO(3) quotient.

## Integrated source operation actually read

Both pinned versions have the same operative sections 02–11, preamble and endpoint diagram by direct byte comparison. October sections 01–11 were read completely in bounded line chunks; September introduction changes were read as complete differing hunks and unchanged blocks compared byte-for-byte. Driver include order is 01,02,...,11, with endpoint figure included within 11; preamble's glyphtounicode-cmex.tex is a TeX font mapping, not a mathematical dependency. Both full bibliographies are accounted for by full October reading plus actual-byte unchanged-block equality and the sole September companion citation difference. No source PDF semantic reading is claimed; the authenticated TeX includes provide operative statements/proofs.

The complete paid construction is: normalized triple -> definite pair and b+=3 -> closed lift dd dd*G+H0 -> quadratic current mass and resolvent angular energy -> smooth density-weight closedness -> compatible form existence and prescribed taming class criterion -> coefficient-sphere wall crossing including the evaluation line E+eh -> null-class curves through every point and root exclusion -> Eichler/finite-coset chamber class F -> nonsplitting -> exact-pair first-jet transversality, retaining immersed spheres and endpoint model subdisks -> normal operator D alpha=(d alpha,d(x alpha+y*alpha)) with kernel H^1(L) -> unique sphere continuation and torus foliation -> exact node insertion via radial and logarithmic cutoffs -> torus fibration -> affine-monodromy-covariant averaging -> exact basic orthogonality corrections -> periodic nodal model with two matching annular periods -> auxiliary volume solution with exponentially small defect versus polynomial losses -> uniform chamber transfer for every later curve -> two Kahler/Yau steps -> smooth convex third-tamer selection with both endpoints prescribed.

The source's family assertions are substantive, but not a stated deformation retraction of the full space of triples. Section 05 families are over the coefficient sphere and include varying-background compactness with incidence; section 07 also proves genericity for paths and relative endpoints. None of these may be sold anew.

## Exact-form inverse and a possible local lifting calculation

For ANY normalized positive closed triple E=(E1,E2,E3), the metric whose self-dual space is span(E) has b+=3, so E_i span its harmonic self-dual forms. Given three top forms f_i of integral zero, the equations E_i wedge h=f_i have a unique exact two-form solution. The proof in source lemma auxiliary-inverse applies verbatim (the collapsing parameter only affects estimates): solve algebraically for phi=h+, enforce harmonic orthogonality via int f_i=0, and put h=2dd*G phi. Stokes gives ||h||_2=sqrt(2)||h+||_2, uniqueness, and higher estimates using d h=0 and d*h=-2*d phi. This is a paid operator, not a new result.

Apply it separately to the columns of a symmetric 3 by 3 top-form matrix F whose entries have zero integrals: choose exact h_j with E_i wedge h_j=F_ij/2. Then the differential of the full wedge map W(E)_ij=E_i wedge E_j is F. Thus the wedge map on ordered triples in fixed classes has a bounded local right inverse onto the affine space of symmetric top-form matrices with prescribed entry integrals. Nonlinear error is h_i wedge h_j; its entry integrals vanish by exactness. A contraction argument with a fixed background inverse gives local smooth lifts of sufficiently small prescribed wedge changes. Uniform constants hold only for an explicitly compact smooth family with a common positive margin and finite geometry bounds. A local submersion or local projection near a hyperkahler triple is not global path lifting or a deformation retraction: continuation can lose positivity/ellipticity or leave controlled charts. Comparison with original elliptic-deformation literature is required before any novelty claim.

## Dimension at which the pencil method changes

In source lemma pencil-jets, the universal critical-sphere problem has index 4 before quotient by the free six-dimensional PSL(2,C) action. With a d-dimensional parameter base, its expected quotient dimension is d-2. Thus d=0,1 allow generic absence of critical spheres; d=2 permits isolated events. This is a calculation from an already paid transversality proof, not proof that no alternative family construction exists. For fixed ordered cohomology, P is constant and the chamber F may be fixed once, removing a naive lattice-choice objection. Smooth tamers patch by partitions of unity on any compact base once pointwise class availability is proved. Smooth finite-dimensional inverse corrections patch/continue locally with fixed choices. The outstanding family issue must therefore be addressed after these operations, not by simply pointing to pointwise source existence.

## Executed full local Gram lifting, with quantitative constants

This is a derived local construction from the paid inverse, not a frozen substantial nominee. Fix a smooth normalized positive closed ordered triple E on X and a smooth background metric to define Sobolev norms. Fix an integer s>=6. Let Z_s be the closed Banach subspace of H^s two-forms which are closed with zero de Rham class. Equivalently use the image of d on H^{s+1} one-forms; the fixed background Hodge decomposition proves this image is closed. Let Y_s consist of H^s top-forms with integral zero. All norms below include the finitely many component norms and a chosen Sobolev multiplication constant.

Define B_E:Z_s -> Y_s^3 by (B_E h)_i=E_i wedge h. This is an isomorphism. Indeed, choose the metric with self-dual space span(E); the E_i are closed self-dual, hence harmonic. Since b+=3, they form a basis of harmonic self-dual forms. Given f_i with zero integrals, pointwise linear algebra uniquely determines the self-dual phi with E_i wedge phi=f_i. Its inner products with all harmonic self-dual forms integrate to zero. With G the Hodge Green operator, h=2dd*G phi is exact and h+=phi. To check this identity, decompose phi=dd*G phi+d*dG phi; self-duality interchanges these two summands. If exact h has h+=0, Stokes gives 0=int h^2=-||h||_2^2, so h=0. General H^s data follow by continuity of the order-zero operator and density. This proves both existence and uniqueness, not just a formal symbol inverse.

For symmetric F in Sym_3(Y_s), put (R_E F)_j=B_E^{-1}((F_ij/2)_{i=1}^3). Then T_E R_E=Id for
T_E(h)_ij=E_i wedge h_j+E_j wedge h_i.
The image of R_E is the fixed complement specified by
E_i wedge h_j=E_j wedge h_i.
The kernel of T_E is the complementary skew part. No pointwise trace equation or mean equation is dropped: there are six symmetric equations and six zero-integral conditions. For exact h_i,h_j, int h_i wedge h_j=0, by approximation or Stokes. Thus N(h)_ij=h_i wedge h_j lies in Sym_3(Y_s).

Write M=||R_E||, and choose C so
||N(h)||_s<=C||h||_s^2,
||N(h)-N(k)||_s<=C(||h||_s+||k||_s)||h-k||_s.
For delta=||F||_s, take r=2M delta. If delta<=1/(8CM^2), the map
h -> R_E(F-N(h))
maps the closed radius-r ball in Z_s^3 into itself, with Lipschitz constant at most 1/2: its norm is at most M delta+MC r^2<=3r/4. Its unique fixed point in this chosen slice satisfies
W(E+h)=W(E)+F, ||h||_s<=2M||F||_s.
Choose delta smaller if needed so r lies in a C^0 neighborhood where every E+u with ||u||_s<=r remains positive. Positivity is open on the compact manifold; this is a definite explicit additional threshold depending on the minimum eigenvalue of W(E) relative to the background volume, the maximum coefficient size of E, and the Sobolev embedding constant. For a fully specified threshold, write W(E)=M_E dV_0, let lambda=min lambda_min(M_E), A=max_i||E_i||_infinity, let c_s control H^s to C^0, and let C_w bound the pointwise wedge pairing in this background. A componentwise estimate gives ||W(E+u)-W(E)||_op <=3 C_w(2A epsilon+epsilon^2)dV_0 when max_i|u_i|<=epsilon. Thus epsilon<=min(1,lambda/[6 C_w(2A+1)]) and delta<=epsilon/(2M c_s), together with the contraction threshold, suffice. It is not a universal threshold depending only on integrated normalization. For fixed E, two targets in the ball give ||h(F)-h(F')||_s<=2M||F-F'||_s.

Smooth dependence does not require claiming smooth dependence of rough Hodge Green operators. In a fixed-class neighborhood of E, B_beta-B_E is multiplication by beta-E on the same fixed domain and target. If ||(B_beta-B_E)B_E^{-1}||<1/2, then
B_beta^{-1}=B_E^{-1}[Id+(B_beta-B_E)B_E^{-1}]^{-1}.
The convergent Neumann series is a smooth Banach map in beta. Therefore R_beta, and then the fixed point h(beta,F), depend smoothly on beta,F. The derivative in h of its defining equation is Id+R_beta DN(h), whose inverse has norm <=2 under the same contraction bound. This is a genuine parameter construction, not pointwise choices followed by an unsupported continuity claim.

For smooth spatial input, the solution is spatially smooth. Here is the relevant elliptic gauge rather than an assertion that order zero automatically smooths. Write h_j=da_j using the unique coexact potential a_j orthogonal to harmonic one-forms for a fixed smooth background. The equations are the six wedge equations, the three slice equations E_i wedge da_j-E_j wedge da_i=0, and the three equations d*a_j=0. At h=0 the nine wedge/slice equations give the three self-dual parts of da. For nonzero xi, (xi wedge a)+=0 forces xi wedge a=0: that decomposable two-form has square zero, whereas a nonzero anti-self-dual form has negative square. Thus a is a multiple of xi; the fixed positive-metric symbol of d*a=0 forces that multiple to vanish. This proves ellipticity even if the potential gauge metric differs from the metric with self-dual frame E. It is a square first-order elliptic symbol. Small C^0 h preserves ellipticity of the linearization. Differentiating the quasilinear equations, applying interior first-order elliptic regularity in charts, and bootstrapping gives all higher spatial derivatives for smooth E,F. There is no boundary and no claimed boundary extension. Parameter derivatives satisfy the same invertible linearized equations; smooth finite-dimensional parameter inputs therefore give jointly smooth forms. Higher derivative constants depend on higher input norms and the local ellipticity bounds; the displayed H^s threshold alone is not a uniform C^infinity estimate.

For a compact parameter space covered by such charts, a uniform local theorem requires a specified compact family of smooth E and a common positivity margin; finite subcovers bound M and the multiplication/embedding constants. A merely bounded infinite-dimensional class is not silently called compact. If F vanishes on a closed parameter subset A, uniqueness gives h=0 there. If it vanishes on a collar, all collar jets are fixed. Infinite-order agreement at a general closed subset requires F flat there; value-wise vanishing alone does not preserve jets.

## Local relative endpoint correction and extension of a chosen deformation

Let H be a normalized hyperkahler triple. For beta near H in the SAME three ordered classes define nu_beta=(beta_1^2+beta_2^2+beta_3^2)/3, so int nu_beta=1, and set F_beta,ij=delta_ij nu_beta-beta_i wedge beta_j. Each entry has integral zero. Apply the preceding construction based at beta to obtain h_beta. Then r(beta)=beta+h_beta satisfies r_i wedge r_j=delta_ij nu_beta, so its closed positive forms are a hyperkahler triple by the closed orthonormal-triple argument already in Source341. Whenever beta was already hyperkahler, F_beta=0 and r(beta)=beta. The straight segment beta+u h_beta, 0<=u<=1, stays positive after shrinking the neighborhood. Thus a neighborhood has a smooth local homotopy into the hyperkahler subspace fixing every hyperkahler point in its domain. The target may lie in a slightly larger chosen chart; no invariant neighborhood or global strong deformation retraction is asserted. The factor 2 in the source convention is restored by mu=nu_beta/2.

Now carry a single complete paid source deformation gamma(t) from alpha to H, flattened at both time endpoints. For beta=alpha+u sufficiently close to alpha in fixed classes, the explicit path gamma(t)+u is positive for all t: compactness of X times [0,1] supplies one C^0 margin. It starts at beta and ends at H+u, which lies in the local correction chart just constructed. Append the correction segment H+u -> r(H+u), with a smooth time flattening at the junction. This gives a smooth family of full deformations for EVERY beta in a neighborhood of alpha. At u=0 it is gamma followed by a stationary segment. In particular it is not necessary to parameterize all the source's node choices merely to obtain local families. This is a concrete integrated construction using the complete source path and the local elliptic inverse.

For a compact family of inputs, finitely many such neighborhoods provide finitely many local smooth deformations. The overlaps do not automatically carry homotopies between the assigned full paths or their hyperkahler endpoints. Local existence is proved; the compatibility data on overlaps are precisely not supplied by this argument.

A further global case is elementary and must not be called unpaid. If B is a compact smooth parameter manifold admitting a specified smooth contraction c:B times [0,1]->B to b0, and beta(b) is a smooth family on ONE fixed X in the same ordered classes, concatenate beta(c(b,t)) with one source path from beta(b0). This is a smooth family after time flattening and has constant hyperkahler endpoint. It changes no class. It generally does not fix a subset on which beta was hyperkahler, and it does not automatically apply to a nontrivial X-bundle over B: identifying different fibers is additional data. This disposes of the unrestricted contractible-base route without a new lifting theorem.

## Canonical horizontal continuation: executed reduction and exact remaining estimate

There is a particularly concrete candidate continuation that bypasses the pencil choices. Starting at E0, define the positive symmetric top-form matrix
K(t)=(1-t)W(E0)+t Id nu_E0,
where nu_E0=trace(W(E0))/3. Its six integrals remain those of Id, and positivity is uniform in t in the fixed background volume. On the positive fixed-class Banach manifold solve the ODE
E'(t)=R_{E(t)} K'(t), E(0)=E0.
The inverse above makes its vector field smooth locally in H^s. Picard iteration gives a unique maximal local lift, and the chain rule gives W(E(t))=K(t). Every derivative E'_i is exact. Local parameter dependence and relative stationarity at hyperkahler inputs follow from ODE uniqueness, because then K'=0. If this particular lift exists to t=1 smoothly, it gives the desired endpoint. Uniqueness of B_E also shows covariance under orientation-preserving diffeomorphisms, with forms and target matrices pulled back together; no averaging is involved. This covariance is just algebraic uniqueness of the paid inverse, not the excluded finite-group target.

The actual continuation burden is global control of this solution in the positive Sobolev manifold. A compact subset of that manifold permits continuation by finitely many charts. A quantitative sufficient condition along a solution is bounded inverse norm M(t) together with integrable ||R_{E(t)}K'(t)||_s and convergence to an interior positive H^s triple; this gives an H^s limit and restarts the local ODE. The target K controls the wedge matrix but does not by itself provide these analytic hypotheses. The finite-step continuation and endpoint limit have NOT been proved. This is not an assertion that the ODE blows up.

An explicit check explains why coordinate norm control cannot be inferred only from K. On the oriented flat torus R^4/Z^4 take
E1=(dx1 dx2+dx3 dx4)/sqrt(2),
E2=(dx1 dx3-dx2 dx4)/sqrt(2),
E3=(dx1 dx4+dx2 dx3)/sqrt(2),
where juxtaposition is wedge. They satisfy Ei Ej=delta_ij dx1 dx2 dx3 dx4 and the integrated normalization. For a fixed a nonzero and integer n, let
f_n(x)=(x1,x2+a sin(2pi n x1),x3,x4).
It is a volume-preserving diffeomorphism isotopic to the identity. The pulled-back triples have exactly the same ordered classes and exactly the SAME pointwise matrix K=Id dx1 dx2 dx3 dx4. Yet E2 gains the term -a(2pi n)cos(2pi n x1)dx1 dx4/sqrt(2), and E3 gains +a(2pi n)cos(2pi n x1)dx1 dx3/sqrt(2). Their fixed-coordinate C^k norms diverge at least on the order of n^{k+1}. This does not show degeneration modulo diffeomorphisms: all these triples are isometric pullbacks. Indeed K'=0 and our horizontal ODE is stationary at each one. Hence the example invalidates only a proposed bound from K alone, not global existence of the canonical ODE or existence of a good gauge.

Donaldson's original local negative-tangent theory and oscillation-based regularity, the closed exact inverse already in Source341, and Fine–Lotay–Singer's elliptic slice all support the local calculation. Fine–Yao's actual extension proof is stronger than a naive curvature estimate: bounded torsion leads to noncollapse, blowup limits, an ALE root sphere, and a lattice finiteness contradiction. Its finite-time lower bound depends on initial Tr Q and |dQ|^2, and its global continuation hypothesis has not been established for the horizontal ODE here (which is a different flow). No transfer of its torsion equation to this ODE has been justified.

## What a higher-parameter pencil construction must still do after paid operations

With constant ordered classes, fix P and choose the source's F once. Compact local families have uniform tame margins; convex tamers in each fixed class can be patched with smooth partitions of unity. Relative finite node models and the normal-operator continuation already work on one-parameter paths, including endpoint disks. Affine torus transition maps do not obstruct the source's averaging homotopy. Gross–Wilson's actual torsor gluing similarly uses flat Gauss–Manin translation differences so local forms agree, with the Cech class accounting for the B-field. These operations remove naive chamber-choice, tamer-choice and unlabelled-torus objections.

A two-parameter filling still encounters an index-zero critical-sphere locus in the generic universal problem (d-2=0). Transversality provides a discrete event set; it does not give a positive exact replacement across those events or a homotopy of the resulting node insertions. Even avoiding those events locally, the finite local endpoint constructions need compatible path homotopies on overlaps and higher compatibility on multiple overlaps. A simplex can be contracted without relative conditions as above; that does not fill a simplex with already prescribed boundary deformation. No signed count of these events, nonvanishing obstruction, relative filling theorem or monodromy invariant has been proved here. In particular this is a precisely retained unsolved construction, not a new obstruction theorem.

No candidate with a demonstrated substantial operation beyond these paid/local constructions has emerged. No target is frozen, narrowed from an older target, or nominated. The full-scope questions of globally continuing the canonical wedge lift and of building coherent relative endpoint deformations remain open in this notebook, with no claim of literature priority or exhaustion.

## A global-in-time action bound up to the unknown continuation time

The canonical wedge lift has more control than just local existence. This estimate uses the strongest Stokes identity above and must be retained before describing the continuation gap. Fix the smooth volume nu=nu_E0 throughout this calculation, and write K(t)=M(t,x)nu and K'(t)=A(x)nu. The interpolation gives M(t)=(1-t)M(0)+t Id, while A=Id-M(0). Set lambda=min(1,min_x lambda_min(M(0,x)))>0. For each existing solution E(t), choose the metric g(t) with self-dual plane span(E(t)) and volume nu. This is a conformal normalization for the calculation, not the determinant-one convention for the source's Q.

For h_j=E'_j, the horizontal definition gives E_i wedge h_j=A_ij nu/2. Thus phi_j=h_j^+ has coefficients (M^{-1}A_column_j)/2 in the E frame, and pointwise
sum_j |phi_j|_{g(t)}^2=(1/4)tr(A^T M^{-1} A).
Each h_j is exact, so the integrated Stokes identity gives the EXACT identity
sum_j ||E'_j||_{L^2(g(t))}^2=(1/2)int_X tr(A^T M^{-1} A)nu.
Consequently, on any interval [0,T] of existence with T<=1,
int_0^T sum_j ||E'_j||_{L^2(g(t))}^2 dt
 <= T/(2lambda) int_X |Id-M(0)|_F^2 nu.
The corresponding moving-metric L^2 path length is at most
T [ (1/(2lambda)) int_X |Id-M(0)|_F^2 nu ]^{1/2}.
These constants are actual input quantities; no unknown inverse norm appears. They also hold uniformly for a compact smooth initial family with a common lambda. For a hyperkahler initial triple A=0, the estimate and uniqueness correctly give stationarity.

This does not furnish the missing compactness. The identity controls the anti-self-dual part only in integrated L^2, since its squared L^2 norm equals that of phi. It provides neither a pointwise bound nor a bound on spatial derivatives of that part. The metric in these norms is itself evolving, so it is not a bound in the fixed H^s chart used for ODE continuation. A positive lower bound for M controls the wedge pairing relative to nu but not the coordinate condition number of g(t), as the explicit shear calculation illustrates for triples with the same wedge data. I have not established a gauge with uniform elliptic constants from this action estimate, nor a weak compactness theorem whose limit is smooth and positive. The action bound is a concrete surviving reduction, not a claimed global convergence proof or substantial nominee.

Late primary comparison: Draghici–Zhang, Section 3, proves the self-dual/exact Hodge mechanism and emphasizes its linear nature. Elkhadhra's Section 3 requires an already closed positive current and a J-analytic restriction set; it does not replace the source's coupled P+Q density-cutoff argument. Gross–Wilson Sections 3–5 supply the torsor cocycle compatibility and exponential-defect/polynomial-loss correction actually used above. Their constants are tied to a fixed Jacobian and bounded B-field representatives, not uniform over all initial triples. These late reads did not reveal an unpaid operation and did not change or weaken a frozen target: none was frozen.

## Sharpening the continuation reduction: exact action and almost-everywhere limits

Because A=Id-M(0) commutes with M(t), the preceding action can actually be integrated. If m_1(x),m_2(x),m_3(x)>0 are the eigenvalues of M(0,x), then for every existing time T,
Action(0,T)=(1/2)int_X sum_i (1-m_i) log[(m_i+T(1-m_i))/m_i] nu.
The summand is zero at m_i=1 by continuous extension. Hence for every T<=1 the action is bounded by
(1/2)int_X tr[(M(0)-Id) log M(0)] nu.
This is finite for the smooth positive initial triple on compact X. No claim of an effective spatial regularity bound follows. This exact expression strengthens the crude lambda estimate while using precisely the same paid inverse and Stokes operation.

There is also a concrete endpoint statement for any maximal lift interval [0,T*) with T*<=1. The finite action permits a pointwise positive limit almost everywhere, but not yet a distributionally closed limit. To see exactly what is available, put S=g^{-1}g', so tr S=0 because the volume nu is fixed. For a self-dual orthonormal frame zeta_i=(M^{-1/2}E)_i, differentiate *zeta_i=zeta_i to obtain
(*')zeta_i=2(zeta'_i)^-=2(M^{-1/2}E')_i^-.
The map from trace-free symmetric metric variation S to *' restricted to Lambda+ has Hilbert–Schmidt norm |S|. For verification, orthogonally diagonalize S with eigenvalues s1,...,s4 of sum zero. On the normalized pairs (e12+e34), (e13-e24), (e14+e23), the squared norm is
(s1+s2)^2+(s1+s3)^2+(s1+s4)^2=sum_a s_a^2.
Thus, pointwise,
|S|^2 <=4 lambda^{-1} sum_i |(E'_i)^-|_g^2.
Let q(x)=int_0^{T*}(sum_i |(E'_i)^-|_g^2)^{1/2} dt. Cauchy–Schwarz, Tonelli and Stokes give
int_X q^2 nu <= (T*/2) Action(0,T*) < infinity.
For almost every x, q(x) is finite and metric comparison along the path gives
exp[-2lambda^{-1/2}q(x)] g(0,x) <= g(t,x)
 <=exp[2lambda^{-1/2}q(x)] g(0,x).
The time integral of |S| is finite at such x, so g(t,x) is Cauchy in the fixed finite-dimensional matrix space and converges to a positive definite matrix of the same volume. The self-dual part of E' is bounded pointwise in time by the explicit smooth M,A formula; the anti-self-dual part has finite time integral q(x). The comparison above then makes E'(t,x) integrable in the fixed initial norm. Therefore E(t,x) also converges at almost every x, and its limit has wedge matrix K(T*,x). This gives a measurable positive endpoint frame almost everywhere, with a logarithmic metric-distortion tail controlled by q in L^2(nu).

This is the strongest continuation consequence established in these notes. It still does not identify a hypersymplectic endpoint. Exponentials of arbitrary L^2 functions need not be integrable, so the displayed comparison alone gives no uniform integrability of E(t) in fixed coordinates. Passing dE(t)=0 and the three classes to the measurable limit would require additional integrability/compactness; upgrading that limit to a smooth positive triple requires further elliptic control. Neither step is supplied by the almost-everywhere convergence. I do not assert that these failures occur for this ODE. They are the exact missing implications after the action and distortion estimates have been executed.
