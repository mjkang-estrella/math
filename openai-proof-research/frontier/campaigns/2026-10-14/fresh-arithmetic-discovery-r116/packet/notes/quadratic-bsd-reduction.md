# Exact quadratic BSD transfer: feasibility and contribution boundary

PREFREEZE / no nominee. These are original working derivations of credited operations, not a theorem freeze, submitted supporting theorem, manuscript, independent grade or new count. The entire investigation is the Source002 elliptic BSD family. The source and its operative proof operations are stipulated true. The identities below test their strongest compatible composition; no truth audit of those operations is undertaken.

## 1. Explored scope and the exact input

Let E/Q be ANY elliptic curve, d a nonzero nonsquare squarefree integer, K=Q(sqrt(d)), and E^d its quadratic twist. Both signs of d, arbitrary ramification, all reduction types, CM, rational torsion, and the prime 2 are retained. The useful source hypothesis is that there exist primes q_+,q_- (possibly different and possibly 2) with

    s_(q_+)(E/Q) <= 1,    s_(q_-)(E^d/Q) <= 1.

Here s_p is the corank of the FULL p-infinity Selmer group, using every local Kummer condition. This implies each rational factor has its full BSD formula, finite whole Sha, and common arithmetic/analytic/Selmer rank r_+,r_- in {0,1}. It permits rank r=r_++r_-=2 over K. A single hypothesis s_p(E/K)<=1 is a sufficient special case, by the corank identity below. It is NOT substituted for the original arbitrary-curve S73 scope.

Pinned exact-BSD paper, October7, thm:main, has precisely this individual low-corank input with no reduction/residual exceptions. Its complete introduction, classical normalization section, unit-divisor-removal section, and central-volume/final-assembly section were read. The final assembly uses the all-prime converse, the entire Sha's finiteness, two-primary positivity/rationality and equality, and the odd-prime inequalities plus pair identity. No operation in that proof gives BSD merely from Mordell-Weil rank<=1.

In particular its Proposition classical:isogeny ALREADY states compatibility of the analytic/arithmetic ratio with products, isogenies and restriction of scalars. Section10 already uses this compatibility for CM descent. The two-primary companion's classical section and conclusion likewise retain full real periods and full point indices. The all-prime companion's actual reduction and extension-extraction endgame were read. Its rationalized Selmer construction does not claim an integral splitting of 2-primary groups.

The strongest external inputs read here are Milne1972 Theorem1 with the preceding §1 proofs, and MilneADT2nd ed. I.7.1–7.3 with the full proof. Portions of the transitive duality proof I.6.13 through its completion and the Euler-characteristic argument I.5.1–5.4 were also read. These are proof inputs with bounded further dependencies, not assertions inferred from abstracts.

## 2. Actual maps pay the full corank and finiteness claims

Choose the usual K-isomorphism i:E^d_K -> E_K, with sigma(i)=-i. Put

    A=E x E^d,        B=Res_(K/Q)(E_K).

Over K, the Q-isogeny phi:A->B and the reverse psi:B->A are

    phi(P,Q)=(P+iQ, P-iQ),
    psi(R,S)=(R+S, i^(-1)(R-S)).

These formulas respect the descent actions, hence descend to Q. Both composites are [2]. The geometric kernel of phi is the diagonal graph of E[2] under i, so deg(phi)=4, and likewise deg(psi)=4. The two principal polarizations identify psi with phi's dual. These are actual abelian-variety maps; no integral idempotent (1+sigma)/2 is being presumed.

For every place v and every finite extension used in the local decomposition, maps of abelian varieties commute with the Kummer connecting map. Thus phi,psi act on full Selmer groups, retaining v|2 and infinity. Local Shapiro for B identifies its full Selmer condition with the product over w|v of the conditions for E/K_w. Globally,

    Sel_(p∞)(B/Q) = Sel_(p∞)(E/K),
    Sel_(p∞)(A/Q) = Sel_(p∞)(E/Q) ⊕ Sel_(p∞)(E^d/Q).

For odd p, [2] is invertible on these p-primary groups, so phi gives an isomorphism. For p=2 the induced maps have kernel and cokernel killed by 2; both are finite because full Selmer groups are cofinitely generated. To see the cokernel finiteness without assuming divisibility, if X->Y has reverse map with composite [2], its cokernel is a quotient of Y/2Y, which is finite for a cofinitely generated 2-primary group. The kernel lies in X[2], also finite. Consequently, for EVERY p,

    s_p(E/K)=s_p(E/Q)+s_p(E^d/Q).                 (1)

The local compatibility is essential; an abstract Galois-module isomorphism without the Kummer images would not imply (1).

The same maps act on Sha. Finiteness transfers in both directions: a kernel is contained in the finite 2-torsion of Sha, bounded by finite 2-Selmer, while the image lies in a finite group when the opposite Sha is finite. MilneADT I.7.1(b) gives the general proof using finite H^1(G_S,ker(phi)). Shapiro identifies Sha(B/Q) with Sha(E/K), and products identify Sha(A/Q) with the two rational groups. Thus the source gives finite WHOLE Sha(E/K), including its 2-primary subgroup. Rationalizing only the group would not prove this; the finite-kernel argument does.

Artin induction on the Tate representations, including ramified local Euler factors, gives

    L(E/K,s)=L(E/Q,s)L(E^d/Q,s).                  (2)

Milne1972 Proposition3 proves restriction compatibility locally by induced inertia/Frobenius modules, treating unramified and totally ramified steps, then composing. Hence the analytic order is r and the first Taylor coefficient is the product of the first coefficients of the two factors. No extra factorial appears when using L^(r)(1)/r! for each first coefficient.

## 3. The point lattice: where the power of two actually occurs

Write T_F for the torsion subgroup of the appropriate point group. Let

    L = E(K)/T_K,
    M = image(E(Q)/T_Q) + image(E^d(Q)/T_d) in L,
    I = [L:M].

The two images have trivial intersection in L: their rational spans are the + and - eigenspaces. For every P in E(K),

    2P=(P+sigma P)+(P-sigma P),

and the terms on the right come from E(Q) and iE^d(Q). Consequently 2L⊂M, I is finite and a power of 2. Let J be the free-lattice index for psi in the other direction. Determinants of psi phi=[2] give

    I J=2^r.                                     (3)

In particular I divides 2^r. This retains the finite integral defect rather than pretending it is absent.

Use the source's Poincare height pairing B_abs, whose diagonal is lim 4^(-n)h_x,abs(2^n P). Its absolute normalization is unchanged by the K-isomorphism i. It is Galois invariant, so for P in the + space and Q in the - space,

    B_abs(P,Q)=B_abs(sigma P,sigma Q)=-B_abs(P,Q)=0.

The relative K-pairing is 2 B_abs. Thus on M its determinant is

    2^r Reg(E/Q) Reg(E^d/Q).

A sublattice of index I has determinant I² times that of L. Therefore the full relative regulator satisfies

    Reg(E/K)= 2^r Reg(E/Q) Reg(E^d/Q) / I².       (4)

Rank zero uses determinant and index 1. This convention agrees with the source's rank-one 2H_abs diagonal and Milne1972 Proposition5. Changing to an absolute regulator removes 2^r from (4) but requires changing the BSD normalization at the same time.

The elementary integral C2-lattice with sigma swapping e1,e2 has eigensublattice generated by e1+e2,e1-e2 of index2. This is a diagnostic algebra example of the lost factor, not a claimed arithmetic counterexample or separate finding. A rational eigenspace decomposition cannot determine I.

## 4. Sha and the local indices close together, including at two

For a homomorphism f with finite kernel/cokernel put

    z(f)=#ker(f)/#coker(f).

Set z_v=z(phi: A(Q_v)->B(Q_v)), z_Q=z(phi:A(Q)->B(Q)), and z_Q^dual=z(psi:B(Q)->A(Q)). Use the natural dual polarizations above. MilneADT I.7.3 proves, before assuming equality of any BSD ratio with 1,

    product_v z_v
      = (#ker Sha(psi) / #ker Sha(phi)) (z_Q / z_Q^dual).   (5)

Only finitely many factors differ from1. The proof is an actual compatibility calculation: dual height functoriality, Cassels–Tate adjointness, local change of Haar volume, a finite global/local cohomology diagram, and the global Euler characteristic with its archimedean corrections. It applies in characteristic zero when 2 divides deg(phi); it is NOT a prime-to-2 statement. Its degree condition is prime to the FIELD CHARACTERISTIC.

Since the finite Cassels–Tate pairings are perfect, the cokernel of Sha(phi) is dual to the kernel of Sha(psi). Let S_A=#Sha(A/Q), S_B=#Sha(B/Q). Then

    S_A/S_B = #ker Sha(phi)/#ker Sha(psi).

Counting torsion and the free-lattice indices gives

    z_Q = (#T_Q #T_d)/(I #T_K),
    z_Q^dual = #T_K/(J #T_Q #T_d).

For example the first identity follows from
#coker(phi_Q)=I #T_K/#phi(T_Q x T_d) and
#phi(T_Q x T_d)=(#T_Q #T_d)/#ker(phi_Q).
Insert these equations and (3) into (5):

    #Sha(E/K) / (#Sha(E/Q)#Sha(E^d/Q))
       = (product_v z_v) (I²/2^r)
           (#T_K² / (#T_Q² #T_d²)).               (6)

This identifies the full dyadic correction by compatible classical operations. Odd-primary Sha groups actually split through phi, so the ratio in (6) is a power of2. No unconditional direct-sum assertion for Sha[2∞] is made.

Every local phi-cokernel is killed by2, and the kernel is contained in A[2]. Local compactness and the invertible differential make both finite. At an odd place where both abelian varieties have good reduction, the formal group map is an isomorphism and the finite-field groups have equal order under isogeny, so z_v=1. Ramified/bad places, and especially2, cannot simply be dropped. Instead (5) includes them without a good-reduction assumption.

At infinity there is a useful direct check. If d>0, B(R)=E(R)² and the sum/difference map has kernel E(R)[2] and cokernel E(R)/2E(R). Since E(R) has c=1 or2 components, their sizes are 2c and c; z_infinity=2. If d<0, B(R)=E(C) is connected. The map from E(R)xE^d(R) has full-dimensional compact image, hence is surjective, and its kernel is E(R)[2]; z_infinity=2c. These real factors illustrate why total real periods matter. They are not additional hypotheses or substitutes for the dyadic local factor.

## 5. The exact leading term is paid, not just the odd part

Let C_F(E) denote the complete period/local-volume factor in the BSD arithmetic volume, in Milne's relative-height normalization; it includes all archimedean components, minimal-differential corrections and the field discriminant normalization. In particular C_Q(E)=Omega_E product_l c_l(E) in the source convention. Define

    V_F(E)=C_F(E) Reg_F(E) #Sha(E/F) / #T_F²,
    D_F(E)=L^*(E/F,1)/V_F(E).

Use one consistent Haar normalization throughout. No simplified imaginary split-prime expression for C_K is applied to general d. Milne1972 §1 Proposition2 proves the full restriction comparison even at ramified places by the Neron restriction model and its smooth special fiber. Proposition5 supplies the matching relative height; the Shapiro Sha comparison completes Theorem1. Thus D_Q(B)=D_K(E).

For phi, the local-volume change with pulled-back differential is exactly product_v z_v. Changes of a global differential cancel by the product formula. Equations(4),(6) therefore give

    C_K(E) Reg_K(E) #Sha(E/K)/#T_K²
      = C_Q(E) Reg_Q(E) #Sha(E/Q)/#T_Q²
          times C_Q(E^d) Reg_Q(E^d) #Sha(E^d/Q)/#T_d².     (7)

Equivalently D_K(E)=D_Q(E)D_Q(E^d). Both right-hand factors are1 by the stipulated source at the stated low-corank hypotheses. This transfers exact BSD, not just its rank or its valuations away from2. The finite point-index and Sha defects have NOT been required to vanish separately; they cancel in the combined volume by the proven duality identity.

This is already the general isogeny/restriction compatibility in Source002 classical:isogeny, now tested against its actual primary proofs. Completing the ramified, rank-two, CM, all-prime or real-place cases here is not evidence of a nonroutine operation. The computation is not submitted as a supporting-result nominee.

## 6. Historical scope and what remains unachieved

Actual i73 §2B (S73) asks for EVERY non-CM elliptic curve over EVERY imaginary quadratic K, every prime p, and full corank0/1, with rank equality and finite whole Sha. Its original scope/prose was read, not inferred from a catalogue. It expressly distinguishes the routine rational-base-change case. i75 §6.2 was also read: restriction/corestriction multiplies the Cassels–Tate pairing by2 and cannot detect the first rational pairing from restricted classes alone. That failed detector does not negate the compatible dual-isogeny calculation (5), which keeps BOTH maps, their local cokernels and the global duality diagram. No old target is changed, renamed or regraded.

For a general E/K, restriction of scalars has dimension2. It need not be isogenous over Q to two rational elliptic curves, so Source002 cannot be applied to two nonexistent rational factors. Even a relation between E and its conjugate is not, by itself, a supplied rational elliptic decomposition or the arithmetic class/nonvanishing implication required in S73. We have neither proved such an implication nor a counterexample or an impossibility statement. We do not select S73 as a new conjectural nominee, and do not offer the rational-base-change subclass as its replacement.

No residual nonroutine operation remains identified in the explored rational quadratic transfer. The unachieved campaign obligation is a substantial new full-scope author-proof nominee beyond these source/classical compatibilities. The old arbitrary-curve S73 obligation remains as originally stated, and all other protected full scopes and dispositions remain unchanged. No theorem was frozen. There is no independent correctness/contribution grade, acceptance, count, priority, current-worldwide-open, exhaustive-search or impossibility claim.
