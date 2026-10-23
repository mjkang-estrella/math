# Arithmetic162d: full relative-transport test and its obstruction

PREFREEZE. No viable theorem has been frozen. This note retains feasibility calculations for one specified positive operation, the full obstruction discovered during that test, and its strongest-payment comparison. It is not an author-proof nominee. The pin and all its operative proofs are stipulated true.

## 1. Exact operation tested

Let S be an arbitrary connected compact Kähler parameter manifold. Consider a smooth proper holomorphic family f:mathcal X->S with connected compact Kähler fibres X_s and nef holomorphic tangent T_(X_s). Suppose a simultaneous maximal-irregularity cover and relative Albanese bundle have already been supplied:

    alpha: mathcal Y -> mathcal A,    a: mathcal A -> S,

where mathcal Y->mathcal X is finite étale, the maps alpha_s are the maximal-irregularity Albanese maps, and d_s=dim(X_s)-qtilde(X_s)<=6. The desired operation would produce, after a compatible finite étale replacement, a holomorphic splitting

    0 -> T_(mathcal Y/mathcal A) -> T_(mathcal Y/S)
         -> alpha* T_(mathcal A/S) -> 0

whose horizontal distribution is integrable in each fibre over S. No prescribed central splitting, monodromy representation, polarization, or fibre marking is required. Both nonprojective tori and nonsemisimple monodromy are allowed. The parameter S is not restricted to a Stein open set. The supplied family must be retained, not replaced by a different deformation with the same central member. The point case is included.

This is the exact positive question tested, not a frozen assertion. Providing the simultaneous cover in the hypotheses isolates the actual new interface; the example below already has it. Thus the failure cannot be blamed on the absence of a relative Albanese construction.

## 2. Strongest compatible construction before gluing

For each member, Source067 identifies the Fano Albanese fibre as a fixed rational homogeneous F. Cao's stronger construction embeds it by anticanonical sections and carries the defining ideal subbundle into a flat symmetric power. All equations are parallel. Thus locally constant transition maps preserve the WHOLE embedded fibre. This retains the algebraic group action and equations, rather than only its cohomology or a flag type.

For a prescribed parameter family, use local trivializations of its F-bundle and let g_ij be the holomorphic Aut(F)-valued transition functions on mathcal A. A relative connection consists of Lie-algebra-valued one-forms A_i along mathcal A/S satisfying, in one consistent right-frame convention,

    A_j = Ad(g_ij^-1) A_i + g_ij^-1 d_(mathcal A/S)g_ij.

The affine inhomogeneous term is the relative Atiyah cocycle. A fibrewise flat structure proves its restriction to each individual A_s vanishes; it does not set the global class to zero. If a connection exists, its curvature in that same convention is

    R_i = d_rel A_i + (1/2)[A_i,A_i].

The gluing obstruction precedes this nonlinear equation. For an elliptic base in each fibre, Omega^2_(mathcal A/S)=0 and every relative connection is automatically flat. Consequently a failure of the LINEAR gluing problem there already disproves the full operation; it cannot be repaired by a different curvature argument.

Poddar-Singh Section 2.A constructs exactly this extension and its class. Their Theorem 2.6 identifies a sufficient vanishing of H1(S,a_*(Omega^1_(mathcal A/S) tensor ad(P))). It does not remove that hypothesis for arbitrary compact S. Their Example 2.8 supplies the Stein-base curve case. Rothstein's tautological extension has the identity as its extension class, and his Poincaré connection cocycle supplies the concrete model of this obstruction. None of those classical restricted or conditional mechanisms is nominated here.

## 3. An explicit family in the full sixfold-fibre scope

Choose an elliptic curve A=C/(Z+tau Z), Im(tau)>0, identify its dual S=Pic^0(A) with A by the origin polarization, and put B=A x S. Let P be the normalized Poincaré line bundle. Equivalently,

    P = O_(A x A)(Delta - A x {0} - {0} x A).

Thus P_s=O_A(s-0), P_0=O_A, and P|_({0} x S)=O_S. Define

    E = O_B^4 direct-sum P,
    mathcal X = Gr_B(2,E),
    alpha: mathcal X -> B,
    f = pr_S alpha.

Here Gr(2,E) means two-dimensional SUBSPACES in a rank-five vector bundle; this explicit convention is independent of the source's quotient-projectivization convention. Alpha is a smooth projective Gr(2,5)-bundle. Its homogeneous fibre F has dimension 2(5-2)=6, so every X_s has dimension seven. This uses exactly the source's torus-reduced dimension six, not an unsupported assertion about seven-dimensional Fano manifolds.

Every P_s is a degree-zero line bundle on an elliptic curve and admits a unitary flat metric. Consequently E_s and End(E_s) are unitary flat. On the relative Grassmannian, the infinitesimal linear action gives a surjection

    alpha_s* End(E_s) -> T_(X_s/A).

At a two-plane U in a vector space V, this is End(V)->Hom(U,V/U), which is surjective by extending a linear map from U to V. The unitary flat bundle is nef; a quotient is nef. The tangent sequence

    0 -> T_(X_s/A) -> T_(X_s) -> O_(X_s) -> 0

therefore shows T_(X_s) is nef by the extension property for nef bundles. No claim that T_(mathcal X) is nef is made or needed.

Each X_s is smooth connected projective. Its Grassmannian fibres are simply connected with H^i(O_F)=0 for i>0. The homotopy sequence and Leray give pi1(X_s)=pi1(A)=Z^2 and H1(O_(X_s))=H1(O_A). Every connected finite étale cover of X_s is pulled back from an isogeny A'->A and still has irregularity one. Hence qtilde(X_s)=q(X_s)=1, alpha_s is its Albanese map (after the origin choice), and d_s=7-1=6. The required simultaneous cover is the identity. These statements check every source applicability interface.

The fibrewise flat structures are completely explicit: the unitary character for P_s induces a diagonal representation into PGL5, which acts on Gr(2,5). Thus each X_s is a suspension with ordinary universal cover Gr(2,5) x C. The following obstruction is entirely in the parameter direction.

## 4. The mixed Poincaré class, including an explicit cocycle

Let z,w be coordinates on the universal covers of A and S. Up to the harmless choice of P versus its inverse, normalized P has factors of automorphy

    z -> z+1:       1,
    z -> z+tau:     exp(2 pi i w),
    w -> w+1:       1,
    w -> w+tau:     exp(2 pi i z).

They commute: the two tau-shifts give the same extra factor exp(2 pi i tau), and the shifts by 1 contribute exp(2 pi i)=1. They trivialize at either origin, and their restrictions in the z-direction give the degree-zero line class parameterized by w.

On A x U, where U is a small coordinate chart in S, d_z is a relative holomorphic flat connection, since the z-transition multipliers are independent of z. Across the parameter tau-shift the frame change is h(z)=exp(2 pi i z), and the relative connection changes by d_z log h=2 pi i dz (with the opposite sign if connection rather than frame transformations are used). The parameter 1-shift gives zero.

In the quotient convention where sections satisfy s(w+tau)=h(z)s(w), a global connection d_z+b(w)dz would require

    b(w+1)=b(w),          b(w+tau)=b(w)-2 pi i.               (1)

Any holomorphic relative connection differs from d_z by a holomorphic section of pr_A*Omega_A^1. Compactness of A makes its coefficient independent of z, so b is an entire function of w. Differentiating (1) makes b' a doubly periodic entire function and hence constant. Periodicity by 1 then forces b'=0; the tau identity contradicts this. Thus no relative holomorphic connection on P exists globally over S.

There is a smooth choice,

    b(w) = -2 pi i Im(w)/Im(tau),

which satisfies (1) and gives the fibrewise unitary connections. Its antiholomorphic parameter dependence is the missing compatibility, not a failure of existence for any individual fibre. Restricting to a small chart U permits the holomorphic choice b=0. Neither observation solves the global problem.

The same fact has a cohomological calculation. Normalize the point class of A by

    omega = i dz wedge dbar(z)/(2 Im(tau)).

The difference map delta(z,w)=z-w gives

    c1(P)=delta*omega-pr_A*omega-pr_S*omega
         =-i (dz wedge dbar(w)+dw wedge dbar(z))/(2 Im(tau)).

The projection to H1(B,Omega^1_(B/S)) retains the dz tensor [dbar(w)] term and kills the dw term. This is nonzero. Up to the conventional fixed 2 pi i factor and Cech sign, it is precisely [d_rel log p_ij], the relative Atiyah class kappa of P. This second computation agrees with the explicit nontrivial additive cocycle (1); no Fourier-Mukai equivalence is needed.

## 5. Why the Grassmannian cannot conceal the obstruction

It is not enough to show that E itself has no connection: an associated homogeneous bundle might admit one without preserving a chosen linear lift. We explicitly pass to the projective obstruction and then recover it intrinsically from the Grassmannian.

For the projective-space bundle of lines P_lines(E), local transition matrices are diag(1,1,1,1,p_ij). The projective Atiyah cocycle is

    [ diag(0,0,0,0,d_rel log p_ij) ]

in Omega^1_(B/S) tensor (End(E)/O_B Id). It can equivalently be represented by the traceless matrix

    diag(-kappa/5,-kappa/5,-kappa/5,-kappa/5,4kappa/5).       (2)

The functional M -> M_55-M_11 is a GLOBAL holomorphic map End(E)/O Id -> O_B. It is invariant under conjugation by all the actual diagonal transition matrices and kills scalars. It sends (2) to kappa. Thus a zero projective Atiyah class would force kappa=0, which has just been excluded. Allowing arbitrary off-diagonal changes of connection cannot affect this conclusion: a coboundary remains a coboundary under that global linear functional. In particular, changing E by a line-bundle twist only adds a scalar class and cannot remove the obstruction.

To relate this to Gr(2,E), recall the intrinsic family of maximal projective LINEAR spaces in its Plücker embedding. They have two types:

    {U: fixed line ell subset U} = P(V/ell), dimension 3;
    {U: U subset fixed three-space W} = Gr(2,W), dimension 2.

For completeness, the linear-algebra distinction comes from decomposable bivectors. Two independent decomposable bivectors whose entire span is decomposable have underlying two-planes meeting in a line. Write them a wedge b and a wedge c. If every other plane contains a, the space is contained in a wedge V. If some other plane does not contain a, it lies in span(a,b,c); imposing wedge-zero with that plane forces every further plane into that same three-space. Maximality gives the two displayed types. The dimension-three type therefore has parameter space P_lines(V).

Any automorphism of Gr(2,5) preserves its ample Picard generator, hence the Plücker linear systems and the dimensions of these maximal linear spaces. It consequently induces an automorphism of their P4 parameter space. Applied to a bundle, the parameter spaces glue as P_lines(E).

If alpha had a relative holomorphic splitting, its one-dimensional horizontal distribution would be integrable. Locally solving its holomorphic ordinary differential equation gives biholomorphisms between whole compact Grassmannian fibres; compactness supplies a common sufficiently small time interval. These biholomorphisms preserve the intrinsic dimension-three linear-space family. They induce compatible local parallel transport on P_lines(E), hence a relative holomorphic connection on P_lines(E). That contradicts (2). This argument does not assume a prescribed group marking, and does not infer a connection on E merely from a connection on the Grassmannian.

Equivalently one could use Aut^0(Gr(2,5))=PGL5, but the explicit reconstruction above avoids importing an unexamined automorphism classification as the crucial interface.

## 6. Finite étale replacement does not repair it

Let p:B'->B be any connected finite étale cover. The base map B'->S is still a submersion, with

    Omega^1_(B'/S)=p*Omega^1_(B/S).

For any locally free sheaf V on B, the finite trace gives a left inverse to pullback on H1, after division by deg(p): the composite pullback followed by trace is deg(p) Id. Therefore

    p*:H1(B,V)->H1(B',p*V)

is injective over C. Apply this to V=Omega^1_(B/S). The class p*kappa is nonzero. The diagonal functional and the intrinsic projective-space reconstruction pull back unchanged. Thus the pulled-back Grassmannian bundle has no relative holomorphic connection either. In particular, separate finite étale changes of the parameter S and of the elliptic Albanese base cannot help. Ramified base changes or a nonproper affine torsor are different operations and were not authorized substitutes for the tested conclusion.

This also covers finite étale replacement of the TOTAL SPACE compatible with its original relative Albanese map. Since Gr(2,5) is simply connected, pi1(mathcal X)->pi1(B) is an isomorphism. Every connected finite étale cover of mathcal X is the pullback from the corresponding finite étale cover B' of B. This follows from ordinary covering-space classification, with the unique induced analytic structure; there is no quasi-étale or orbifold substitution. Hence an additional compatible finite étale total-space cover cannot remove the obstruction.

## 7. The exact outcome of the test

The positive global operation of Section 1 fails on this explicitly constructed smooth projective family. The failure is already the nonzero class kappa, not an unconstructed named hard gap, and it persists under the stipulated type of finite replacement. Its fibres have augmented irregularity one and homogeneous Fano Albanese fibres of dimension six, so no source hypothesis has been weakened in applying the source separately to each member.

This is not a counterexample to Source067, DPS, or Cao. Their pointwise uniformization, flatification, and purpose-built fixed-monodromy deformations are all retained. Cao's construction keeps the equations and representation fixed while changing the torus; the present family moves the degree-zero line class around its compact moduli torus. Rothstein's nontrivial universal extension and Poddar-Singh's parameter H1 already account for this difference. Packaging their obstruction into a Grassmannian is not proposed as a new substantial theorem.

The precise additional operation that the tested positive claim would need is a holomorphic global selection of the relative connections, i.e. a section of the relevant affine connection torsor. Here that torsor has the displayed nonzero mixed class, so such a selection cannot be supplied by finite étale pullback. There is no remaining unsolved obligation for this particular obstruction calculation. No viable alternate full-scope operation was closed; no smaller Stein-base, fixed-monodromy, chosen-filtration, or pointwise statement is substituted as a nominee. This conclusion concerns this test only and makes no exhaustion or global-impossibility claim for Source067 research.
