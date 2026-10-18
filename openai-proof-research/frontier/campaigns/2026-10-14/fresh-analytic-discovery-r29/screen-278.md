# Family 278: exact continuations and their barriers

This is author-side exploratory mathematics, not an independently reviewed candidate. The source at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb is stipulated true. Its actual theorem and section 7, not catalogue inference, give a finite three-electron Coulomb density n with no representing real spin-independent potential in V=L^(3/2)(R^3)+L^infinity(R^3) and with empty V-subdifferential of the ensemble kinetic functional T at n. The source's own section 4 already supplies a kinetic minimizing determinant and the exact formal potential; section 5 proves its nonmembership in V.

## 1. Full approximation question, gauge, and the already-paid conclusion

Fix the physical source density n, of integral 3. Let X=L^1(R^3;R) intersect L^3(R^3;R), with norm ||f||_1+||f||_3. Let X_0={f in X: integral f=0}. Define the gauge-invariant potential size

    M(v)=||v restricted to X_0||_(X_0)*
        =inf_(c in R) ||v+c||_(X*).

Here the X* norm is the operator dual norm. This definition avoids ambiguities between equivalent sum-space norms. Hahn–Banach gives the quotient equality; the annihilator of X_0 is precisely the constant functions. The infimum need not be attained, but representatives within any positive error exist. Adding a constant does not change a fixed-three-electron ground space.

Consider EVERY sequence v_j in V and EVERY sequence of trace-one positive ensembles Gamma_j on wedge^3 L^2(R^3;C^2), supported at the spectral bottom of the corresponding noninteracting Hamiltonian. Let n_j be their spin-summed densities, and assume ||n_j-n||_X -> 0. No restriction is made on rank, degeneracy, spin coherences, or shape of v_j. Existence of each such ensemble entails an attained ground energy; no uniform distance below the essential threshold is assumed. There is no independently imposed tightness hypothesis: L1 convergence to n with mass 3 already entails spatial tightness of the densities. The intended quantitative question is a source-specific lower divergence bound for M(v_j) in terms of ||n_j-n||_X alone, uniformly over all these approximants. A rate was not selected/frozen or proved.

The qualitative implication M(v_j)->infinity is a routine consequence of subgradient graph closure. Here is its precise abstract argument. For any proper convex lower semicontinuous functional F on X, any x_j->x with F(x)<infinity, and any uniformly bounded u_j in partial F(x_j), choose a weak-star subsequential limit u (X is separable). The inequality at x gives

    F(x_j) <= F(x)+<u_j,x_j-x>.

Lower semicontinuity then proves F(x_j)->F(x). Passing the inequality at any fixed competitor y gives u in partial F(x). Consequently an empty subdifferential at x rules out any bounded subsequence of subgradients. For kinetic constrained search, a representing ground ensemble gives -v_j in partial T(n_j); every constant shift also does, because finite T densities have integral 3. The standard convex lower-semicontinuous ensemble kinetic functional therefore yields the implication. Its lsc is a conventional constrained-search compactness input, not established by a new theorem here. It can also be obtained from the Lieb functional representation; no claim that the source's short section 7 alone proves all of this background is made.

Equivalently, for each finite M the infimum of ||m-n||_X over represented m with M(v)<=M is strictly positive (infinity if the set is empty). Defining that infimum as a modulus is not an explicit quantitative rate or an unpaid mechanism. It is not nominated.

Empty subdifferential has no universal quantitative inverse rate even in one dimension. Let L:(0,1]->(0,infinity) be continuous, nonincreasing, integrable, and divergent at zero. Put F(0)=0 and F(x)=-integral_0^x L(t)dt for 0<x<=1, extending F by infinity outside [0,1]. Then F is proper lsc convex, partial F(0) is empty, and at 0<x<1 its subgradient is -L(x). Thus arbitrarily slowly divergent L are possible. This abstract example does not disprove a source-specific Coulomb rate; it proves that empty subdifferential/graph closure alone supplies none.

## 2. Generalized realization is paid by the ground-state transform

The source produces g>0, h, d>0 with g,h in H1 intersect H2_loc, ||g||²=2, ||h||²=1, g orthogonal to h, n=g²+h², and

    V=Delta g/(2g) in L2_loc, integral n|V|<infinity,
    (-Delta/2+V)g=0, (-Delta/2+V)h=d h.

The supplied weighted gap is (1/2)integral g²|grad xi|² >= d Var_(g²)(xi). Source section 4 already proves the identity on compact smooth test functions

    q_V[f]=(1/2)integral g²|grad(f/g)|².

The right side is a densely defined nonnegative closable weighted Dirichlet form after the unitary multiplication xi -> g xi from L2(g² dx) to L2(dx). Its closure defines a self-adjoint realization. On compact sets positivity and local regularity of g make the ordinary local weighted Sobolev theory applicable; cutoffs exhaust the weighted form domain. The original compact-test Schrödinger form therefore has this Friedrichs realization.

Cutoffs of g converge in the form norm to g, with energy going to zero. For h, the source's integrability and orbital equation give q_V[chi_R h]=d||chi_R h||²+(1/2)integral |grad chi_R|²h². The compact-test identity and Fatou imply finite weighted energy of h/g; its weighted L2 norm is ||h||. Weighted cutoff approximation then identifies its energy as d and its weak eigen-equation as the d-eigenfunction equation. The weighted gap extends by closure and gives H>=d(I-P_g), with g spanning the zero eigenspace. After adding spin, that zero eigenspace has rank two. Pauli exclusion gives the three-electron lower bound d, attained by the determinant with g/sqrt(2) in both spin states and h in one. Hence n is representable for this generalized form realization.

This uses exactly the source's orbital/gap data, its Pauli certificate, and the classical ground-state form closure. Frank–Seiringer (0803.0503v2), section 2.3, equation (2.12) at p=2, explicitly identifies the classical identity. No frontier nomination is justified by calling this a new potential class. In particular, the closure need not have the ordinary H1 form domain or the absolute-integral expression on every form-domain element. The source's exclusion of V is not contradicted. Thresholds or multiplicity above d do not matter for this technical construction.

## 3. The transverse curvature shortcut cancels, even at fixed d>0

The source's fixed-coupling channel expansion has planar amplitude of order A(p)p^-4, whereas a fixed transverse displacement has amplitude of order A(p)z/p. This suggests a transverse scale of order p^-3. But the exact potential formula is

    V=Delta sqrt(n)/(2sqrt(n)) - |grad theta|²/2 + d sin²(theta).

It does not permit omission of the angle-gradient term. The first diagnostic used n=e^(-2kx)(z²+epsilon²), theta=arctan(z/epsilon): the singular curvature and angle terms cancel exactly. That elementary version has d=0 and is insufficient to test the positive-gap interface. The following strengthened model was then derived.

Fix arbitrary k>0, d>0, epsilon>0 and s=sqrt(2d), in coordinates (x,y,z). Set

    g_epsilon=epsilon e^(-kx) cosh(sz),
    h_epsilon=z e^(-kx),
    V_epsilon=k²/2+d,
    n_epsilon=g_epsilon²+h_epsilon²,
    theta_epsilon=arctan(h_epsilon/g_epsilon).

Direct differentiation gives Delta g=(k²+2d)g and Delta h=k²h. Thus the two exact orbital equations hold at energies 0,d in one bounded constant potential, with positive even g and odd h positive above z=0. Consequently the angle Euler equation also holds with exactly this fixed positive d. For every bounded displacement set,

    n_epsilon -> z²e^(-2kx) uniformly as epsilon->0,
    n_epsilon(x,y,0)=epsilon²e^(-2kx).

The transverse density scale is epsilon, arbitrarily small. No local potential divergence occurs. At z=0 the identity is especially transparent: theta_z=1/epsilon, Delta sqrt(n)/(2sqrt(n))=k²/2+d+1/(2epsilon²), and the negative gradient term cancels 1/(2epsilon²).

This is a local diagnostic only. These g,h are not globally square integrable, the global mass constraints are absent, and cosh growth obstructs a global physical model. It is NOT a counterexample to any stipulated source theorem or the full quantitative approximation question. It proves that the exact orbital equations, positive d, fixed-window density limit and small planar amplitude alone do not force a quantitative local ridge. The source's global integrability, angle comparison and weighted trace contradiction do essential work. No finite collection of these local windows resolves the rate question.

In the actual source, angle convergence is as lambda->0 on each FIXED compact set. It is not an estimate for theta at p->infinity at fixed lambda. The channel proof provides detailed density remainders and derivative controls; the obstacle is not absence of all density rates. The qualitative exterior translated-limit argument assumes V in the admissible sum space and then uses compactness without a uniform radius bound. It does not provide quantitative stability for arbitrary approximating densities in X, which controls neither planar traces nor second derivatives. A lower ridge estimate would require a quantitative global angle boundary-layer result that survives the cancellation; a norm-escape rate for arbitrary n_j would further require a quantitative bridge from X-closeness to that mechanism. Neither was proved.

## 4. Actual closest-primary comparison and disposition

Gori-Giorgi–Gál–Baerends, 1109.2204v2, section V: their coupled Dyson-orbital expansion gives polynomial suppression on the plane, and section V.B explicitly shows that differing angular approach laws can produce negative divergence or a negative constant on the plane accompanied by growing off-plane peaks. Those examples support caution about extracting potential behavior solely from an exponent. They do not give a uniform rate for arbitrary representable densities approaching the pinned Coulomb example in X.

Herbst–Bakkestuen–Laestadius, 2409.04372v3, section II: their inversion uses periodic H^-1 density and H^1 potential spaces. Section II.B explicitly assumes noninteracting v-representability for convergence to a finite inverse potential, and derives nonexpansive proximal/error estimates. Importing it as an inversion theorem for this nonrepresentable whole-space X-density changes both the hypothesis and the spaces. Abstract proximal blowup at an empty subdifferential is another standard convex consequence, not a new route to a rate.

No substantial theorem, candidate freeze, independent verdict, or count results from these three screens. A future contribution would need the quantitative global angle/stability bridge at the full scope of section 1, or a genuinely different full natural theorem. The present local diagnostic could be formalized by elementary differentiation/algebra, but that would certify only the displayed example, not the missing Coulomb theorem. No Lean artifact is claimed or needed for a no-nominee checkpoint.
