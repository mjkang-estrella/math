# r225 — integrated feasibility derivations, not a frozen nominee

These are durable mathematical calculations for the one Source349 family. They do not assert a contribution grade, correctness grade, acceptance, or priority. No target from a prior round was read or reopened. No new theorem has been frozen. The point of carrying these calculations is to identify what the strongest compatible paid construction already supplies before deciding whether a distinct substantial target remains.

## 1. Categories and normalization

Fix an integer m >= 2 and the unit round S^(m+1). Set sigma_m = |S^m| and a_m = min_k |C_(k,m-k)|. An input F:M -> S^(m+1) is a smooth immersion of a closed connected smooth domain. Its area is the induced domain volume, with every sheet counted. No orientability is assumed at this stage. Write H for the mean-curvature VECTOR in the sphere, with trace rather than averaged convention. Thus |H| is defined on a one-sided immersion also. Whenever a global normal is available we use A=-dN and scalar H=tr A; changing N changes scalar H's sign but not its norms.

The source's main volume statement applies to the image being non-totally-geodesic, not to a parametrization. Its index theorem instead applies to an embedded, hence two-sided, hypersurface. We never apply a scalar Jacobi calculation to a one-sided immersion, nor replace a domain volume by an image measure. No orientable cover is needed below. Were such a connected finite degree-d cover used, its induced domain area would be multiplied by d and its function spectrum would include additional modes; the index need not be multiplied by d. That invalid shortcut is not used.

A smooth compact immersion has an integral pushforward varifold V_F. The associated mod-two chain is F_#[M]_2, by the area formula with multiplicity reduced modulo two, and has zero boundary. This statement does not need transversality or analyticity of self-intersections: the rectifiable pushforward formula is the relevant operation (White 2009, §2.3). The generalized mean curvature of the pushforward, at coincident sheets, is the sheet-weighted average of their mean curvatures, so Jensen's inequality gives ||H_V||_(L^q(V)) <= ||H_F||_(L^q(M)) for q >= 1. In particular, ||delta V|| <= integral_M |H_F| for tangent fields in the sphere. This is the correct compactness input for arbitrary immersed domains.

## 2. Equality is already forced by the paid family and min-max operations

Suppose the minimal immersion has domain area a_m. Since a_m < 2 sigma_m, source Proposition `prop:immersion-reduction` makes F injective and hence an embedding. Its index is at least m+3. If greater, source Proposition `prop:lorentz-family` gives a Z_2 flat-continuous detecting family on RP^(m+3), without mass concentration, of maximal mass D<a_m. Its central deformation is supported in an interior ball of Q=Bbar^(m+2) x [-1,1], hence preserves the boundary complement relation, the pulled-back filling cover, and the nonzero cup power. Cubical replacement preserves its image and mass supremum; its cubical dimension is irrelevant to the source min-max input.

The paid min-max theorem then produces a stationary integral V of mass in [gamma_m,D], with gamma_m>sigma_m. For m=2,3 take the smooth low-dimensional output so its cone is cyclic. For m>=4 the supplied stationary-integral regularity suffices. Source `cor:cones-spherical-output` makes V a smooth connected multiplicity-one non-equatorial minimal hypersurface of mass below a_m, contradicting the stipulated main theorem. Thus index=m+3, and the paid index classification makes the equality immersion a single-sheeted Clifford product. This is a full compatible equality reduction, not a new equality mechanism.

The minimizing splitting is also determined by an elementary part of the paid volume calculation. With d_t=sigma_t(t/(2 pi e))^(t/2), the source proves strict convexity of g(t)=log d_t. For fixed integer m, g(k)+g(m-k) is strictly decreasing for k<m/2 and increasing for k>m/2, because its derivative is g'(k)-g'(m-k). Consequently only {k,l}={floor(m/2),ceil(m/2)} minimizes. Interchanging factors gives the same orbit under O(m+2). There is no continuous free splitting parameter and no unbalanced threshold example. At fixed m, the finitely many other splitting volumes have a positive gap from a_m.

## 3. The strongest low-density regularity window

Keep cyclicity modulo two even in high dimension; it is available for limits of these immersions. Define

    b_2 = 2,
    b_m = theta_(m-1) = a_(m-1)/sigma_(m-1)  (m >= 3).

Then theta_m < b_m and b_m <= 2. The exact radial-splitting proof in Source349 extends to the following window: a nonzero stationary integral cyclic k-cone in R^(k+1) of density <b_m is a multiplicity-one plane for k<=m, and has a smooth, connected, multiplicity-one link for k=m+1.

Here is the complete induction needed for that extension. A stationary one-cone has integer-weighted rays, total weight N and density N/2. Cyclicity makes N even; N<4 and stationarity force N=2 with opposite unit rays. At a nonzero point of a k-cone, a tangent splits as R times a stationary integral cyclic (k-1)-cone of the same density. The source's proof retains integer multiplicity and derives cyclicity by almost-everywhere slicing, not by assuming the zero slice is good. Induction makes this tangent a multiplicity-one plane. Allard then gives a smooth multiplicity-one link. Each closed connected component of the link contributes density at least one, so density<2 gives connectedness. In link dimension one, the link is a great circle. In link dimension j between 2 and m-1, a non-equatorial link would have density at least theta_j >= theta_(m-1)=b_m, by the stipulated theorem in dimension j and the strict decrease proved in the source. Thus the link is equatorial. For k=m+1 only smoothness of the link is asserted; no volume theorem is applied at that step.

Therefore every stationary integral cyclic m-varifold V in the round sphere with mass < sigma_m b_m is a smooth connected embedded multiplicity-one minimal hypersurface. Coning preserves mass exactly and stationarity; cyclicity of a spherical cycle passes to its cone, with the vertex cutoff boundary mass O(r^m). This includes a genuine open mass window above a_m in every dimension. In particular, the m=4 branch must RETAIN cyclicity to get above theta_4=3/2; discarding it admits the Y-junction base obstruction. No hidden high-dimensional singular limit remains inside this window.

For a sequence of smooth minimal immersions in a compact mass subwindow, integral-varifold compactness and White's theorem give a stationary integral cyclic limit. Cone density gives a smooth multiplicity-one limit. Allard's local graph theorem, applied on finitely many small balls in that limit, yields single-sheeted C^(1,alpha) convergence; the minimal graph equation gives C^k convergence for every fixed k. This is area-only smooth compactness HERE because of the derived density window, not a general area-only compactness assertion.

## 4. Full Clifford Jacobi calculation and the isometry gauge

For C=C_(k,l), k+l=m, with radii sqrt(k/m),sqrt(l/m), one has |A|^2=m and L=Delta+2m. Product spherical harmonics of degrees (a,b), a,b nonnegative integers, have Laplace eigenvalue

    mu_(a,b) = (m/k) a(a+k-1) + (m/l) b(b+l-1),
    lambda_(a,b)(L) = 2m-mu_(a,b).

This follows by restricting homogeneous harmonic polynomials to each factor and taking tensor products; these give a complete orthogonal basis. On S^1, degrees a>=1 have multiplicity two, while degree zero has multiplicity one, so no circle exception is omitted.

The positive spectrum is lambda_(0,0)=2m and lambda_(1,0)=lambda_(0,1)=m, with total multiplicity 1+(k+1)+(l+1)=m+3. If a>=2 then the first factor contribution is at least 2m(k+1)/k>2m; the analogous statement holds for b>=2. The only zero eigenspace is therefore (a,b)=(1,1), of dimension (k+1)(l+1). The closest negative eigenvalue is -2m/max(k,l), attained at degree two on a largest factor. If k=l, both such degree-two spaces attain it.

All zero fields are ambient rotations. Write F(x,y)=(r x,s y), N=(s x,-r y), with x in S^k(1), y in S^l(1), r^2=k/m, s^2=l/m. A skew block matrix B_T with off-diagonal block T sends F to (s T y,-r T^t x). Its normal component is

    <B_T F,N> = s^2 <x,T y> + r^2 <x,T y> = <x,T y>.

These products span exactly the kernel. Thus null directions are integrable by actual isometries; there are no additional parity, covering, or volume-constraint conditions in this embedded two-sided calculation. The index here is unconstrained area index. Imposing enclosed-volume constraints changes the constant mode and is not part of this calculation.

For a nearby hypersurface, take its spherical normal graph over C and apply a small rotation transverse to the stabilizer O(k+1)xO(l+1). The derivative of its kernel moments in the rotation directions is the invertible Gram matrix of the displayed kernel basis. The finite-dimensional implicit function theorem gives a gauge with u orthogonal to ker L in L^2(C). This is a pointwise local choice, not a continuously selected global gauge over a parameter family. Compactness of the isometry orbit makes the constants uniform. The stabilizer, and the factor swap when k=l, are not incorrectly treated as new deformations.

On this complement, the elliptic estimate

    ||u||_(W^(2,q)(C)) <= C_(m,q) ||Lu||_(L^q(C)),  1<q<infinity,

follows from the ordinary elliptic estimate plus the absence of kernel. For clarity, if the L^q zeroth-order term could not be removed, a normalized countersequence, compactness W^(2,q)->L^q, and distributional passage to Lu=0 would produce a nonzero kernel vector orthogonal to the kernel. This proves the required inverse bound. Only fixed compact model geometry enters.

## 5. Executing the supercritical almost-minimal reduction

First, the preceding facts imply a volume isolation interval for exact minimal immersions around a_m. If non-Clifford minimal immersions had areas tending to a_m, the density-window compactness would yield smooth single-sheeted convergence to an equality Clifford. The gauge and inverse estimate in §4, together with the nonlinear mean-curvature equation below with H=0, force u=0 for all sufficiently close members, a contradiction. Choose a fixed interval [a_m-delta,a_m+delta] strictly inside (sigma_m,sigma_m b_m), containing no stationary integral cyclic minimal varifolds other than the minimizing Clifford orbit. The existence of delta is qualitative; no effective numerical value has been derived.

Now take smooth closed connected immersions with areas in this interval and ||H||_(L^q(M))->0, where q>m is FIXED. Their pushforward varifolds have bounded mass, uniformly bounded Euclidean first variation (the round sphere contributes the fixed radial term -mF), and spherical first variation tending to zero. Allard compactness and White give a stationary integral cyclic limit whose mass is the limit of the domain areas, since the ambient Grassmann bundle is compact. The preceding isolation interval makes it a minimizing Clifford.

To obtain C^1 convergence rather than merely varifold convergence, fix a sufficiently small ball about any point of that smooth limit. At this fixed scale the limit has normalized mass arbitrarily close to one, and the radial ambient mean-curvature contribution has scale-normalized L^q norm O(r). For the sequence, the remaining contribution is at most r^(1-m/q)||H||_q, hence tends to zero. The p>n hypothesis and single-sheeted conclusion of Simon Chapter 5, Theorem 5.2 apply. There can be no extra sheets or a remote component: the L^q monotonicity lower mass bound at every support point rules out support separated from the compact limit, and the finite graph cover rules out local extras. Thus the entire image is a single normal graph after a diffeomorphism of the domain. Multiplicity one rules out a nontrivial covering. Consequently nonorientable and one-sided domains are automatically excluded in this small regime; they were not silently omitted from the input class.

For the model normal graph F_u=cos(u)F+sin(u)N put B(u)=cos(u)I-sin(u)A. Its exact area density is

    J(u,Du)=det B(u) * sqrt(1+|B(u)^(-1) Du|^2)

when ||u||_C1 is small enough that B is positive definite. Its expansion and the trace-mean-curvature linearization give

    A(u)-a_m = -(1/2) integral_C uLu + R_A,
    |R_A| <= C ||u||_C1 ||u||_H1^2,
    H(u) = Lu + R_H,
    ||R_H||_q <= C ||u||_C1 ||u||_W2q.

The last estimate is a quasilinear coefficient estimate: the coefficients multiplying D^2u differ from those at zero by O(|u|+|Du|); the remaining Taylor remainder is bounded by C(|u|+|Du|)^2. There is no assumed bound on second derivatives hidden in the constant. Pullback area measures and intrinsic norms on the graph and model are uniformly equivalent as ||u||_C1->0. Applying the inverse estimate on the gauge complement and absorbing C||u||_C1||u||_W2q yields

    ||u||_W2q <= C_(m,q) ||H||_Lq(M).

This also gives C^(1,1-m/q) control by Sobolev embedding. The mean curvature is the trace mean curvature; replacing it by average mean curvature would insert a factor m. Repeating the same absorption in L^2 yields ||u||_W22 <= C_m ||H||_L2(M), even though q>m was needed for the initial graphical entry.

The spectral calculation gives the precise leading area coefficients. With l=max(k,l),

    -(1/(2m)) ||Lu||_2^2 <= -(1/2) integral uLu
                              <= (l/(4m)) ||Lu||_2^2.

Indeed, on each nonzero eigenspace the ratio is -1/(2 lambda), whose negative extremum is -1/(2m), and whose positive extremum is l/(4m). Remainders and measure comparison imply that, for every eta>0, a sufficiently small mean-curvature regime in the isolated area interval has

    -(1/(2m)+eta) integral_M |H|^2 <= A(M)-a_m
                    <= (ceil(m/2)/(4m)+eta) integral_M |H|^2.

Both coefficients have actual examples under the joint hypotheses: take small smooth normal graphs u=t phi, with phi in a degree-one factor space for the lower coefficient or a degree-two space on a largest factor for the upper coefficient. These graphs are embedded and connected, their areas tend to a_m, and their L^q mean-curvature norms tend to zero. The kernel gauge affects only higher-order terms. This checks compatibility and optimal leading constants; it is not numerical evidence.

In m=2, the lower coefficient 1/4 is already the familiar trace-normalized Willmore coefficient. More generally, after the paid source cone/family reduction, all the operations above are standard single-sheet compactness, integrable Jacobi-kernel reduction and elliptic absorption. No separate nonroutine operation has been identified here merely by stating the estimates with sharper constants. This is why these calculations have not been frozen as a substantial nominee.

## 6. Critical exponent: a concrete logarithmic tilt, including exact area normalization

The preceding failure at q=m can be made geometric, without changing topology or adding covers. Fix a minimizing Clifford C and o in C. Choose a tangent unit vector e_1 and its spherical unit normal N_o. In T_o S^(m+1), let J generate rotations in span{e_1,N_o} and be zero on its orthogonal complement. Write R_t=exp(tJ). Choose chi in C^infinity(R), equal to zero on (-infinity,0] and one on [1,infinity), with all endpoint jets compatible. Let alpha=pi/2, 0<R<inj(o), L large, and

    theta(r)=alpha chi(log(R/r)/L),
    Psi_(R,L)(exp_o z)=exp_o(R_(theta(|z|)) z).

Extend by the identity outside B_R(o), and by the constant rotation R_alpha near o (r<=R exp(-L)). This is a smooth ambient diffeomorphism: it preserves radius, and its inverse rotates by -theta(r). Since every fixed R_t is induced by a round-sphere isometry fixing o, the core and the exterior of the moved Clifford remain exactly minimal. On the transition annulus,

    r|theta'(r)| + r^2|theta''(r)| <= C/L.

In polar coordinates the round metric is dr^2+sin^2(r)g_(S^m). The differential of Psi is a rotation plus a radial/angular shear whose norm is at most C/L. Its inverse has the same bound. After freezing theta at a point, differentiating the varying rotation adds terms bounded by C/(Lr) to the second fundamental form; the change in the trace of the original second fundamental form is O(|A_C|/L). Since |A_C|=sqrt(m) is fixed and r<1, this proves the concrete trace-mean-curvature bound

    |H_(Psi C)| <= C_m/(Lr)

on the transition, and H=0 on the core and exterior. One can check this bound directly without a compactness assertion. In normal coordinates write P(z)=Q(r)z, Q(r)=R_(theta(r)). Then

    DP=Q+Q' z tensor dr,
    |D^2P| <= C(|theta'|+r|theta''|+r|theta'|^2) <= C/(Lr).

Freeze Q at the evaluation point. That constant map is an exact round isometry. The difference of the first derivatives from this frozen isometry is O(1/L); its second covariant derivative has the displayed bound, with round-connection error O(r/L) absorbed into it. For a unit frame on C, the transformed induced metric differs from the frozen one by O(1/L). Contracting the transformed second fundamental form against the inverse metric thus adds at most C|A_C|/L plus C/(Lr) to the zero original mean curvature. This proves the bound for the trace convention, with constants independent of R,L. No merely conformal preservation of minimality is assumed: only constant rotations on the two constant-angle regions preserve it. The transition error is explicitly retained.

Radial coarea for C near o has cross-sectional area at most C_m r^(m-1), and the hypersurface Jacobian of Psi is between 1-C/L and 1+C/L. Therefore

    integral_(Psi C) |H|^m <= C_m L^(-m) integral_(R e^-L)^R dr/r
                              <= C_m L^(1-m),
    |A(Psi C)-a_m| <= C_m R^m/L.

For m>=2, choose R_j->0 and L_j->infinity. The images converge as varifolds and in Hausdorff distance to C, and their critical mean-curvature norms tend to zero, but at o their tangent plane is R_alpha(T_o C), which makes a fixed right angle with T_o C in one direction. This destroys C^1 convergence. It also destroys C^1 closeness modulo ALL ambient isometries: if there were Q_j C and normal graphs with C^1 norm tending to zero, compactness of O(m+2) would give Q_j->Q. Hausdorff convergence forces QC=C. Smooth convergence of this model orbit then gives model tangent T_o C at o, contradicting the fixed rotated tangent of the constructed images. This argument requires neither a chosen normal orientation nor a unique orbit representative. In fact the construction already executes a stronger compatible alternative: the ambient map and its inverse have differential singular values in [1-C/L,1+C/L] everywhere. Integrating along ambient geodesics makes Psi a (1+C/L)-bi-Lipschitz ambient map, with the same near-isometry bound on the induced intrinsic metrics of C and Psi C. Large pointwise tangent rotation is therefore compatible with parametrizations whose metric distortion tends to one. The small supported area correction below changes this distortion by only O(|t|). The obstruction is specifically to extrinsic C^1 closeness, not to metric or bi-Lipschitz stability.

One can make the domain area EXACTLY a_m, rather than only asymptotic to it. Here is the full correction mechanism. Choose two smooth functions f_- and f_+ on C, both vanishing on a fixed neighborhood of o, with

    Q(f_-)=integral (|Df_-|^2-2m f_-^2)<0,
    Q(f_+)>0.

Existence of f_- follows by cutting off the constant function near o in H^1. A point has zero H^1 capacity in m>=2: for m>2 the cutoff energy is O(r^(m-2)); for m=2 use a logarithmic annular cutoff with energy O(1/log(R/r)). The cutoff converges to one in H^1, so Q stays negative. For f_+, take a high-frequency compactly supported bump in a disjoint coordinate ball. Its gradient energy eventually dominates 2m times its squared norm. Thus these are real allowed deformation directions, not fictitious free parameters.

Normal graph deformations t f_±, supported away from o, have area changes (Q(f_±)/2)t^2+O(t^3), and mean curvature bounded by C|t|. Write d_(R,L)=A(Psi_(R,L)C)-a_m. Use the f_- branch if d>=0, and the f_+ branch if d<0. By the sign of the quadratic coefficient, continuity (or monotonicity for small positive t) gives an exact solution t_(R,L) with

    A(Psi_(R,L)(C_(t f_±)))=a_m,
    |t_(R,L)| <= C sqrt(|d_(R,L)|).

The area changes add EXACTLY because the two ambient modifications have disjoint supports. This does not rely on replacing a domain area by an image area. The result is still an embedding diffeomorphic and ambiently isotopic to C, with tangent R_alpha T_o C at o, and

    integral |H|^m <= C_m L^(1-m)+C_m |d_(R,L)|^(m/2) -> 0.

Thus a uniform C^1 graph conclusion from only the exact least area and small L^m trace mean curvature is false, even for this fixed embedded orientable topology. It is not repaired by asking for one sheet, an orientable domain, or exact deficit zero. This explicit endpoint obstruction is retained as a calculation, not offered as a claim of new-to-literature discovery.

## 7. What the weaker alternative actually supplies, and what remains

For any sequence in the isolated area interval with integral |H|->0, varifold compactness and cyclicity still give a stationary cyclic limit. The density window and minimal isolation still identify the limit as a minimizing Clifford. Thus there is a qualitative modulus of weak varifold closeness, depending only on dimension and the chosen fixed interval, as the L^1 mean-curvature norm tends to zero. For example use the bounded-Lipschitz metric on the compact Grassmann bundle of the round sphere, and minimize it over the Clifford orbit. A contrary sequence with distance bounded below would have the just-described limit, a contradiction. This is a compactness modulus; no rate is extracted from it, and support/C^1 or topology conclusions do not follow merely from weak convergence.

At the critical two-dimensional exponent there is a stronger primary construction: Zhou arXiv:2212.03043v1 obtains local bi-Lipschitz parametrization under critical Allard hypotheses. The actual final proof in §6 uses conformal parametrization, an A_2-weighted elliptic estimate, an orthonormal frame, and the Wente/compensated-compactness equation -Delta w=*(de_1 wedge de_2). This is compatible with the logarithmic tilt, which obstructs C^1 graphs but not bi-Lipschitz parametrizations. Therefore the tilt is NOT evidence that all critical geometric stability is impossible. Only §6 and the indicated statement are read; the full upstream chain through §§2–5 and §8 has not been read, so no new global theorem is based on it.

The present work leaves no hidden compactness lemma inside a claimed extension. The full-scope positive C^1 endpoint is explicitly obstructed. The supercritical construction closes at the level of feasibility calculations but supplies no identified substantial operation beyond the paid source and the classical tools. An effective critical weak-distance estimate or a genuinely stronger compatible global parametrization theorem would require an additional proved operation; none has been established here. A perturbed-ambient theorem, a new family-selection bridge, and a worldwide-priority claim are NOT asserted. No manuscript, formalization or release was prepared.
