# Prefreeze calculations: topological height kernels and the missing global operation

These are feasibility calculations, not a frozen theorem or author-proof nominee. The stipulated recognition proof and principal envelope operations were read before this extended note. The later weighted-box example, metric-amenability proof and original lattice realization statement are explicitly recorded as late reads. The remaining internal stationary/profile/label/offset proof ancestry was completed after these extended calculations; this ordering limitation is recorded, not backdated. Protected labels, versions and read boundaries are in private/operative-comparison.md. Nothing below assigns correctness, substantial contribution, acceptance or count.

## 1. Concrete setting and geometric reduction

Let L be a compactly generated totally disconnected locally compact group. Fix a compact open subgroup U and a connected locally finite Cayley–Abels graph X with vertex set L/U; let v=U. The action is continuous, transitive and by graph isometries, with compact vertex stabilizers. We investigate the situation in which X is quasi-isometric to a virtually polycyclic group P. This is a prospective extension of the input, not a claim already proved for L.

The solvable-lattice realization and triangulable-model construction give a connected simply connected real-triangulable unimodular Lie group G quasi-isometric to P. Write pi:G->W for its canonical exponential height. This G need not contain a lattice; the lattice model and the triangulable model serve different purposes. We do not assume a complementary height subgroup: the operative coordinates are a surjection q:N semidirect D ->G, whose kernel records N intersect D.

Fix quasi-inverses f:X->G and r:G->X, with f(v)=1 and r(1)=v. For l in L set F_l=f l r and s(l)=pi f(lv). All F_l have the same quasi-isometry constants. Their multiplication defect is uniformly bounded because rf is uniformly close to the identity on X. The stipulated bounded-height theorem therefore gives a fixed finite matrix group A and one B such that

    ||pi F_l(g)-s(l)-A_l pi(g)|| <= B                         (1)

for every l and g. Equip W with an A-invariant Euclidean norm, obtained by averaging any inner product over A. The multiplication comparison makes A_l A_m=A_lm: its difference times pi(g) is bounded for all g, and pi is onto. In particular A_e=I.

This is not yet a continuous homomorphism by declaration; continuity must be checked from the action on X.

## 2. Finite probes make the label homomorphism continuous

For every A!=I in the finite label set, choose a vector w_A with ||(A-I)w_A||>B+E, where E bounds ||pi f r(g)-pi(g)||. Choose g_A with pi(g_A)=w_A. The subgroup V of L fixing v and all finitely many vertices r(g_A) is open. If l belongs to V, then s(l)=0 and F_l(g_A)=fr(g_A). Thus (1) gives

    ||(A_l-I)w_A|| <= B+E.

If A_l!=I, taking A=A_l contradicts the chosen probe. Hence V lies in L0=ker A, which is open, normal and finite index. This proves continuity of the finite label map without assuming a topology on the entire quasi-isometry group.

L0 is compactly generated. Its orbit is coarsely dense in X: choose a finite right-coset transversal L=L0 R. Every l=h a has d_X(lv,hv)=d_X(av,v), bounded independently of h. Put U0=U intersect L0; this is compact open in L0. The function s on L0 is right U0-invariant and locally bounded.

## 3. Correct the translations without an invalid continuity argument

Comparing F_h F_k and F_hk at 1 gives one defect constant D1 such that

    ||s(hk)-s(h)-s(k)|| <= D1       (h,k in L0).              (2)

Metric amenability of X follows from its quasi-isometry to P by bounded-multiplicity thickening of Følner sets. In the locally compact setting this yields amenability AND unimodularity of L, not merely its amenability as a topological group. One may either use the primary large-scale amenability theorem, or perform the same thickening argument in a proper adapted metric on L: right translates move points a bounded distance and hence a nontrivial modular multiplier contradicts metric Følner sets. Compact fibers require Haar volume in that version. L0 inherits amenability.

For fixed h, the bounded function x -> s(hx)-s(x) is right U0-invariant, hence belongs to the bounded uniformly continuous function space on which a left-invariant mean exists. Equivalently, it is a bounded function on the discrete homogeneous space L0/U0. Define, coordinatewise,

    tau(h)=m_x(s(hx)-s(x)).

The invariant-mean addition calculation gives tau(hk)=tau(h)+tau(k), and positivity gives ||tau(h)-s(h)||<=D1. For the vector norm bound, apply every unit dual functional and use the scalar positivity inequality. No assertion that an invariant mean preserves pointwise parameter continuity is used; an actual earlier original records a counterexample to that assertion.

Continuity is paid directly. For u in U0 and every integer n, s(u^n)=0. Therefore

    n ||tau(u)||=||tau(u^n)||<=D1,

so tau(U0)=0. The kernel K=ker tau contains an open subgroup. Thus tau is continuous, indeed locally constant, and K is open and closed in L0. A second homomorphism uniformly close to s agrees with tau by applying the bounded difference to powers; the correction is unique and independent of the mean.

For l in L and h in L0, the affine defect comparison gives

    s(l h^n l^-1)=A_l s(h^n)+O_l(1).

Using the bounded correction on L0, dividing by n and passing to the limit gives

    tau(l h l^-1)=A_l tau(h).                               (3)

Thus K is normal in all of L. This does not require constructing an arbitrary, possibly discontinuous, correction on the whole finite extension.

## 4. The quotient is finitely generated, but its Euclidean image may be dense

Because K is open, L0/K is discrete. A compact generating set for L0 has finite image in L0/K; hence this quotient is finitely generated. The injective map induced by tau identifies it abstractly with Z^r for some finite r, since it is a finitely generated torsion-free abelian group.

The image tau(L0) is coarsely dense in W: the L0-orbit is coarsely dense in X, f is a quasi-isometry, pi is Lipschitz and onto, and tau differs from pi f(hv) by a fixed amount. Its real linear span is all of W, so r>=dim W. This does NOT show r=dim W or that the image is a lattice. A finitely generated abstract subgroup of R can be dense (Z+sqrt(2)Z); the quotient topology of L0/K and the induced Euclidean topology on tau(L0) are different. We retain that distinction.

The group obtained so far has an exact extension

    1 -> K -> L0 -> Z^r -> 1,                              (4)

with an open height kernel. A choice of lifts of the generators of Z^r need not commute. Equation (4) is not replaced by a semidirect product: their commutators and all conjugation relations remain part of the extension data.

## 5. Haar-volume polynomial growth for every compactly generated piece of K

Let J be generated by a compact symmetric set T contained in K, with U0 included in T. Then J is open in L (hence closed), and Haar measure on L restricts to Haar measure on J. No undistortion of J in L is assumed.

For j=t1...tm in T^m, all prefix products j_i lie in K. Hence pi f(j_i v) has norm at most D1. The graph displacement of T is bounded, so successive f(j_i v) have distance at most C_T in G. Joining them by minimizing geodesics gives paths of length at most C_T m and heights of norm at most

    M_T=D1+Lip(pi) C_T.

The operative bounded-height packing proof puts their endpoints in a region with polynomially many fixed-scale separated points. The quasi-isometry lower inequality and the bounded valence of X bound the number of vertices mapping to each fixed-radius G-ball. Consequently

    |{jU0 : j in T^m}| <= C'_T (1+m)^b_G,
    mu_L(T^m) <= mu_L(U0) C'_T (1+m)^b_G.                   (5)

For the first inequality it is enough to count jv rather than jU0: j in L0 has jU=jU0 within L0. The second follows by covering T^m by precisely those left U0 cosets. Finite stabilizer counting has been replaced by compact-fiber Haar measure, so the original discrete proof really applies in this setting.

One can choose the exponent independent of T. Here is a deliberately coarse explicit choice, retaining the overlap q. Let n=dim N, c be the nilpotency class of N, s the nilpotency class of D, and Q_D its homogeneous dimension. When N=1 take b_G=Q_D. Otherwise take

    b_G = n c [s(n-1)+1] + Q_D.                           (6)

On a D-ball of radius O_T(m), logarithmic coordinates grow at most m^s. On each weight space the nilpotent residual exponential has degree at most n-1. Since all prefix heights are bounded by M_T, its exponential character factor is a T-dependent constant. Each conjugated N-increment therefore has log norm <=C_T(1+m)^[s(n-1)]. The logarithm of a product of O_T(m) increments is a BCH polynomial of degree <=c with coefficient sum bounded by C(1+m)^c. Its norm is at most C_T(1+m)^[c(s(n-1)+1)]. Taking n-dimensional volume and multiplying by the D-ball volume gives (6). Fixed right thickening obeys the same bounds. Since q is Lipschitz, chosen lifts of separated G-endpoints remain separated; no injectivity or lattice in N semidirect D is needed.

The exponent is only an upper bound. It is not an effective bound on C'_T, a sharp dimension formula, or a universal bound on the compact subgroups introduced next.

The primary polynomial-growth structure theorem now supplies a compact open normal subgroup C_J of J with J/C_J discrete and virtually nilpotent. Its proof uses the Lie/no-small-subgroups structure of a polynomial-growth asymptotic cone and a conjugation-escape argument. This is stronger than citing polynomial growth as a label. K is a directed union of such open J (include U0 together with each additional compact subset). The output is local compact-by-virtually-nilpotent structure. Normality of C_J in J does not make C_J normal in K or L.

## 6. Try the strongest available normal-subgroup construction

If L already contains a cobounded polycyclic subgroup Gamma, the primary envelope theorem supplies the missing global compact open normal subgroup. Its mechanism is not just a finite-index transfer: take the finitely generated nilpotent Fitting subgroup of Gamma; use simultaneous tidy subgroups and the cobounded normalizer to obtain one compact open subgroup normalized by it; construct a closed normal enlargement in a finite-index ambient group; quotient by its characteristic maximal compact normal subgroup; then use the open centralizer of the remaining discrete finitely generated nilpotent subgroup. Almost self-centralizing of the Fitting subgroup makes that centralizer compact-by-virtually-abelian. The resulting characteristic compact subgroup is open and normal in the ambient group.

This operation must be included in the reduction. In our prospective setting, however, a finitely generated subgroup chosen cobounded in L need not be discrete or quasi-isometrically embedded in its intrinsic word metric. Source recognition therefore does not make it polycyclic. Picking finitely many representatives of a compact generating neighborhood is not a way around this: the remaining compact subgroup can contain arbitrarily complicated finitely generated abstract subgroups, and errors may accumulate inside it.

Nor do the local subgroups J from section5 supply the primary theorem's required finitely generated nilpotent NORMAL subgroup of a cobounded group. Their compact radicals and finite-index nilpotent quotients are not compatible under all height conjugations. We next calculate this failure explicitly, including exact intersections, unions and modular balance.

## 7. An exact balanced local-field diagnostic

Fix a prime p, F=F_p((u)), and O=F_p[[u]]. Consider

    L_test = (F x F) semidirect_alpha Z,
    alpha(x,y)=(u x,u^-1 y),     U_test=O x O.

This is a diagnostic for the output of sections3–5, NOT a proposed example quasi-isometric to P. It is locally compact, totally disconnected and compactly generated by U_test and the stable letter t: conjugating U_test and taking sums reaches every pair of Laurent series. Both factors are abelian and the quotient is cyclic, so it is amenable. With mu(O)=1, multiplication by u scales Haar by p^-1 and multiplication by u^-1 by p. Their product is1, so L_test is unimodular. Height is the exact continuous homomorphism (x,y,n)->n, with no defect, dense-span issue or finite label action.

Every compact subset of F x F lies in u^-m O x u^-m O for some m. This is a compact subgroup; thus every compactly generated subgroup of the height kernel is compact. Their growth exponent is0. A word in U_test and t±1 whose prefix heights stay between -M and M has horizontal endpoint in u^-M O x u^-M O. The Haar volume of that region is p^(2M), independent of the word length. Thus even a stronger bounded-height packing conclusion does not force a global compact normal subgroup.

Indeed,

    t^n U_test t^-n = u^n O x u^-n O,
    intersection_{n in Z} t^n U_test t^-n = {(0,0)},
    subgroup generated by all these conjugates = F x F.

The intersection has lost openness; the generated union has lost compactness. More generally, any compact normal C in L_test maps trivially to Z. If (x,y) in C and x!=0, conjugating by t^-n gives first coordinate u^-n x, escaping every compact subset. If y!=0, conjugating by t^n does the same in the second coordinate. Thus C=1. There is no compact open normal subgroup.

This example even carries the familiar discrete uniform lattice. Embed F_p[u,u^-1] by

    f -> (f(u), f(u^-1)).

No nonzero Laurent polynomial has both coordinates in uO: its least exponent would have to be >=1 and its largest exponent <=-1. The image is therefore discrete. Given (x,y), remove the negative-power part of x using negative monomials of f; remove the negative-power part of y using positive monomials of f. The remainder lies in O x O, so the quotient is compact. Multiplication by u in the polynomial ring is compatible with alpha. Consequently the semidirect product of this lattice with Z is a discrete cocompact subgroup, isomorphic to the finite-lamp wreath product.

This is the known local-field/horocyclic construction actually read in the primary, now with the exact normal-core calculation. It is not a discovery or a counterexample to the desired quasi-isometric extension. Its role is precise: amenability, unimodularity, an exact finitely generated height quotient and even exponent-zero local kernels are insufficient on their own. Any successful continuation must use the geometry of the polycyclic comparison beyond those properties.

## 8. The nilpotent-boundary approach, with the mixed bracket retained

The strongest alternative examined is to use the input's contracting ray boundaries, conjugate the resulting uniform boundary actions to similarities, and reconstruct an isometric action. In the primary SOL-like setting the two boundary dilation characters must cancel: their sum is uniformly bounded and also additive under powers, hence zero. Product boundary conjugacies then extend to a quasi-isometry and a proper isometric action. This is already an integrated primary operation. It requires the specified Carnot/Carnot-by-Carnot boundary hypotheses, the radial-limit condition, and in the one-dimensional distinguished-fiber case the stated amenability hypothesis. A general quotient boundary in the input is not automatically covered by this conjugation theorem.

There is a second obstruction before invoking any general conjugation theorem: the collection of ray quotients may not retain all of G. Work explicitly with the four-dimensional group having Lie algebra

    [X,Y]=Z, [T,X]=X, [T,Y]=-Y, [T,Z]=0.

This is the same diagnostic model that appears in the stipulated source's weighted-box construction; its occurrence was read later than sections1–6 above and is recorded as a late read. Nothing about its bracket-generated volume is claimed as a new operation. In exponential coordinates for the Heisenberg factor its group law is

    (x,y,z,t)(a,b,c,s)
      = (x+e^t a, y+e^-t b,
         z+c+(x e^-t b-y e^t a)/2, t+s).                   (7)

Here N is the Heisenberg group, D=exp(span(T,Z)) is abelian, N intersect D=exp(RZ), and canonical height is t. The positive ray quotient kills Y and Z and records x; the negative ray quotient kills X and Z and records y. Thus the central subgroup exp(RZ) acts trivially on BOTH ray quotients. It also has zero height. The entire vector of boundary maps and height translations fails to detect it.

The failure is visible on actual lattice models, not only abstract Lie algebras. In symmetric Heisenberg coordinates, take the lattice with (x,y) in Z² and z in (1/2)Z. Any A in SL(2,Z) preserves this lattice under (v,z)->(Av,z), since it preserves the alternating area form. For A=[[2,1],[1,1]], eigenvalues are positive reciprocal numbers lambda,lambda^-1, with lambda>1. Its real logarithm has eigenvalues ±log(lambda), and after changing the horizontal basis and height scale the resulting semidirect Lie group is (7). The semidirect product of the Heisenberg lattice with Z is discrete and cocompact in it. The center supplies an infinite cyclic subgroup in the kernel of the induced map to quasi-isometry classes.

For z0 central, left translation by exp(z0 Z) is an isometry and

    d(g,exp(z0 Z)g)=d(1,exp(z0 Z))

for every g. Each translation is a bounded distance from the identity, but these distances are unbounded as |z0| increases, by properness of the metric. All the translations have the same (1,0) quasi-isometry constants. Thus this model is not QI-tame. A general claim that a geometric action maps to the quasi-isometry group with compact kernel would be false here. The primary envelope embedding theorem actually assumes QI-tameness; that assumption cannot be silently deleted. The example does not obstruct a compact-by-Lie conclusion, since this L is itself a Lie group; it obstructs this particular reconstruction route.

The missing central variable is paid geometrically by commutator area. At height0,

    exp(aX) exp(bY) exp(-aX) exp(-bY)=exp(ab Z).             (8)

At heights rb and ra, respectively, the available X and Y displacements are e^(rb) and e^(-ra). The commutator produces central amplitude e^[r(b-a)]. Together with the X and Y widths this gives the volume exponent 2(b-a), exactly the input's strongest bracket-box operation. Discarding the zero-weight bracket would lose half this exponent.

## 9. Exact bounded-slab degree in the four-dimensional model

The same example allows a sharper check of section5 than the deliberately coarse exponent (6). Let a path start at1, have length <=r and height |t|<=M. In left-trivialized velocities (a,b,c,d), equation (7) gives

    x'=e^t a, y'=e^-t b,
    z'=c+(x e^-t b-y e^t a)/2, t'=d.

Norm equivalence at the identity bounds the integral of |a|+|b|+|c|+|d| by Cr. Hence

    |x|+|y| <= C e^M r,
    |z| <= Cr+C e^(2M) r².                                (9)

Haar measure is dx dy dz dt. Thickening endpoints by a fixed metric ball only changes constants and the fixed height bound, so separated endpoints number at most C_M(1+r)^4. This also covers fixed-height slices without treating the noninjective N semidirect D coordinates as unique.

For the reverse order, at height0 first use X and Y segments of size <=c r, then use a four-segment commutator rectangle with side lengths O(r) to prescribe any remaining central coordinate of size <=c r². The correction for the xy/2 term in (7) is also O(r²), so the same length budget applies after choosing c small. Thus a Heisenberg box with horizontal side lengths comparable to r and central side length comparable to r² is reachable in length Cr entirely at height0. Its N-Haar volume is comparable to r^4. A fixed-radius ambient G-ball intersects N in a set of uniformly bounded N-Haar measure, after translating its center to a point of N if necessary. A maximal separated net therefore has at least c r^4 points. The slab packing degree is exactly4 for this model.

This computation pays the mixed central direction explicitly. It still gives no global normal compact subgroup in the general tdlc setting, and no general conjugacy recovering the missing bracket cocycle from the separate ray actions. Both the group law and the commutator area must survive any proposed reconstruction; assigning independent boundary similarities is insufficient.

## 10. Where the integrated construction ends

The full chain carried out is: geometric action on a locally finite graph -> uniform transferred quasi-action -> finite labels detected continuously by finite probes -> unique exact continuous height correction -> open normal kernel and a discrete abstract Z^r quotient -> compact-fiber Haar packing with a model-dependent uniform polynomial degree -> local compact-by-virtually-nilpotent pieces. The known cobounded-polycyclic/Fitting/tidy operation supplies a global compact open normal subgroup when its genuine lattice/cobounded-polycyclic hypothesis is available. The known SOL-like boundary operation supplies an isometric reconstruction in its genuine boundary classes. Their applicable scopes have been retained.

The unpaid step in the general tdlc extension is to use the full polycyclic comparison geometry to obtain a single compact open normal subgroup of L, or another global structure statement sufficient to replace it, from these local pieces. The local-field diagnostic proves that the extracted height/kernel information alone is inadequate. The mixed-bracket example prevents replacing that obligation by an unsupported faithful/proper boundary representation or by an appeal to QI-tameness. The original discrete finiteness/duality step cannot be applied directly either: its actual statements concern countable discrete groups and finite cohomological dimension over the specified coefficient ring.

If a compact open normal subgroup C of L were obtained, then L/C would be a finitely generated discrete group quasi-isometric to P, and stipulated recognition would make it virtually polycyclic. That final implication is paid. The construction of C is the unpaid operation. No full theorem asserting it has been frozen, and no weaker version of that desired conclusion or renamed source recognition statement is nominated.

## 11. Further reduction: compact generation, and what a discrete height image buys

The preceding endpoint can be sharpened. Suppose first that K is compactly generated. Section5 applies with J=K and provides a compact open normal subgroup C of K with K/C virtually nilpotent. There is in fact a unique maximal compact normal subgroup Cmax of K. To see this from the stated output, the discrete virtually nilpotent quotient K/C has a largest finite normal subgroup: it is virtually polycyclic and hence satisfies the ascending chain condition on subgroups; the subgroup generated by all finite normal subgroups is a directed union of finite normal subgroups, hence is itself finite. Its inverse image is compact, contains every compact normal subgroup of K, and is characteristic. Thus Cmax is normal in L because K is normal in L. It is open in L because it is open in K and K is open. The discrete quotient L/Cmax is quasi-isometric to P, so stipulated recognition makes it virtually polycyclic.

Conversely, in this exact QI setting, suppose that L has a compact open normal subgroup C. The subgroup C0=C intersect L0 maps trivially under tau, by compactness and continuity, so C0 lies in K. The group L0/C0 is discrete virtually polycyclic by the input, and K/C0, being a subgroup, is finitely generated. A compact extension of a finitely generated discrete group is compactly generated: take C0 and finitely many lifts. Thus K is compactly generated. For the particular canonical correction constructed here, the desired compact-open-normal conclusion is equivalent to compact generation of K. This equivalence is a compatible composition, not a nominee.

There is also a completely paid sufficient geometric condition: if tau(L0) is discrete in W, then K is compactly generated. Here are the details, to avoid treating bounded-height containment as coarse surjectivity.

The Lie kernel H_G=ker pi is connected. The exponential map on G is a diffeomorphism, pi(exp X)=pi_*(X), and H_G=exp(ker pi_*); in particular it is path connected. Choose a linear section sigma:W->g. Whenever ||pi(g)||<=D, the point

    g'=g exp[-sigma(pi(g))]

lies in H_G and is at uniformly bounded distance from g; the right factor belongs to the exponential image of a fixed compact vector ball.

For any k in K, pi f(kv) is bounded by D1. Adjust f(kv) as above and join1 to the adjusted endpoint by a path in H_G. No length bound for this path is needed. Subdivide it into metric steps of length <=1. Send the subdivision vertices through r and then choose nearby points h_i v from the coarsely dense L0-orbit. Each f(h_i v) is a fixed distance from the original height-zero path vertex, so ||tau(h_i)|| is bounded by a single constant D2, independently of k and i.

Now use the additional DISCRETENESS: the set

    A2=tau(L0) intersect closed_ball_W(0,D2)

is finite. For each a in A2 choose c_a in L0 with tau(c_a)=a, choosing c_0=e. Put k_i=h_i c_a^-1 when a=tau(h_i). Then k_i lies in K and

    d_X(h_i v,k_i v)=d_X(v,c_a^-1 v)

is bounded by a fixed constant because there are finitely many a. Successive k_i v are therefore at distance <=R for one R independent of the endpoint k. Include e and k at the two ends; the endpoint corrections only enlarge R by a fixed amount. Each increment k_i^-1 k_(i+1) then lies in

    S_R={u in K : d_X(v,uv)<=R}.

This is compact: the graph ball is finite, each vertex fiber is a compact U0 coset, and K is closed. It is an identity neighborhood because U0 is included. The constructed chain expresses every k as a product of elements of S_R. Therefore K is compactly generated.

The step fails if tau(L0) is merely finitely generated as an abstract abelian group: infinitely many distinct image elements may lie in the fixed ball A2, and the word displacements of their chosen lifts need not be uniformly bounded. Choosing a basis of Z^r does not fix this problem, because the integer coefficients of a small Euclidean image can be arbitrarily large. The exact unpaid alternative is now visible: establish discreteness (or uniformly bounded corrections for this finite-height window), or prove compact generation of K by another operation using the full QI geometry.

When W=0, K=L0=L is already compactly generated, so the polynomial-growth theorem closes the locally compact nilpotent case. That case is classical and is not nominated. In the exponential-height case, no proof of the required global compatibility or image discreteness has been obtained here. No conditional statement above is promoted to the remaining substantial full-scope result.
