# Prefreeze calculation: self-dual integral reconstruction

Status: exploratory derivation, no frozen claim and no nominee. One family only, Source027. The prospective direction retains EVERY smooth connected complex curve, every Sp(2n), every collection of quasi-unipotent exact boundary conjugacy classes, and every component of the corresponding reduced character locus, with ambient integrality over the full ring of integers of ONE extension of the eigenvalue field. No strict finite-prime Jordan requirement, single-orbit claim, S-integer substitute, or generic-boundary replacement is being proposed. These are working scope requirements, not a frozen theorem. All old scopes remain intact.

## 1. What the actual source pays

Source027's diagram-density theorem handles oriented GL surfaces joined by flags with specified free graded modules. The operative proof is not just the main SL statement. Two-flag galleries, free splitting, the four-contact negative-scalar disk, affine vertex restrictions, and the unique starting prefix all enter. Scalar twisting and unit-root adjoining only remove determinants; they do not impose a preserved alternating form. Exact boundary classes are selected AFTER taking the reductive quotient. The same order of operations is needed for Sp.

R036 already pays a single integral dense mapping-class orbit on every CLOSED SL_r surface of genus >=2. Its two-band principal-minor certificate, finite-open arithmetic selection, and Baire choice inside the orbit closure must be credited. I204's congruence and strict finite-prime boundary screens are not our target and are not regraded.

## 2. The full integral unipotent radical, without division by 2

Let R be any commutative ring. Set V=U + W + U*, with U=R^k, W=R^(2m), and standard alternating matrix J on W (J^t=-J, J^2=-I). The form on V has matrix

    Omega = [[0,0,I], [0,J,0], [-I,0,0]].

An upper unitriangular block matrix preserving the filtration U subset U-perp subset V and inducing the identity on all three graded modules has shape

    N(A,B) = [[I,A,B], [0,I,J A^t], [0,0,I]],
    B-B^t = A J A^t.                                      (1)

This follows by multiplying N^t Omega N. Conversely (1) makes that product exactly Omega, over every R, including characteristic 2. The middle-right equation gives C=J A^t and the last diagonal block gives precisely the displayed skew equation.

Write Q(A) for the strictly upper triangular matrix whose (i,j) entry for i<j is (A J A^t)_ij. The diagonal entries of A J A^t vanish over every commutative ring by termwise cancellation. Hence Q(A)-Q(A)^t=A J A^t. All solutions are uniquely

    B=Q(A)+Z,    Z=Z^t.

Thus the group scheme N, as a scheme, is affine space of dimension 2km+k(k+1)/2 over Z. This is not a claim that its group law is additive. Its integral points are Zariski dense over any infinite subring R of C, since its coordinates A and the upper triangle of Z vary independently in R. A half-skew expression B=Z+(AJA^t)/2 is unnecessary and would introduce a spurious prime-2 restriction.

The actual product law is

    (A,B)(A',B')=(A+A', B+B'+AJA'^t),                      (2)

and the inverse is (-A,-B+AJA^t). In Z coordinates the correction is
Q(A)+Q(A')+AJA'^t-Q(A+A'), a symmetric integral polynomial matrix. This gives a complete integral parameterization, not merely infinitesimal tangent coordinates.

For k=1,m=1 write A=(a,b), J=[[0,1],[-1,0]], B=z. Then

    (a,b,z)(c,d,w)=(a+c,b+d,z+w+ad-bc),
    [(a,b,z),(c,d,w)]=(0,0,2(ad-bc)).                     (3)

The factor 2 in the commutator does NOT obstruct parameterization or density: z is an independent central parameter. In characteristic 2 this group becomes commutative, while the same scheme remains affine 3-space. A failure of a commutator-only generation argument is therefore not a failure of the full available group.

## 3. Symplectic free splitting over a number ring

Suppose E is a free module with a perfect alternating pairing, U is an isotropic direct summand with a specified free basis, and U-perp/U is supplied with a free symplectic basis. The pairing map E -> U* is surjective: E->E* is an isomorphism and restriction E*->U* splits. Choose dual lifts f_i of the basis of U*. Their skew Gram matrix C_ij=<f_i,f_j> can be killed by adding integral linear combinations of the e_i. If f_i'=f_i+sum_l t_li e_l, then

    <f_i',f_j'>=C_ij+t_ji-t_ij.

Choose one triangle of t to cancel C (for i<j take t_ij=C_ij and t_ji=0). No division by 2 is used. Now H=span(e_i,f_i') is a free perfect hyperbolic summand. Its orthogonal complement identifies isometrically with U-perp/U, so the supplied symplectic basis lifts there. This constructs an integral splitting V=U+W+U* compatible with all supplied graded bases. Different isometries inducing the identity on these gradeds form exactly the group (1).

This proof assumes specified free graded modules with a perfect residual form; it does not assert that arbitrary sublattices/intersections are free or unimodular. These are precisely data which a successful self-dual diagram induction must supply.

## 4. What is genuinely obtained and what is not

The preceding algebra removes two naive barriers: nonabelianness of the lift group and division by 2. For a fixed split self-dual filtration with all graded identifications supplied, the entire lift torsor is explicitly affine with integral coordinates. The source's density-transfer lemma therefore applies to such a family if its projection is open/surjective and integral lower objects admit the stipulated splitting.

This is still not the diagram theorem. At a vertex one needs restriction maps from COARSE self-dual data to the incoming interval data to be surjective over every allowed lower integral solution, with dense integral fibers. One also needs the resulting outgoing data, induced forms, dual identifications and the pairing of repeated seam occurrences to be compatible. These are separate assertions from the affine parameterization of N. Quotients of two stabilizers cannot simply be called free additive modules: (2) has a central correction, and the source's source-side block-forgetting proof used additive Hom(Q,U). Classical root-coordinate/Bruhat reconstruction is a compatible possible solution; nothing here excludes it.

The starting prefix requires U, its annihilator U-perp and the residual W, not just U and V/U. All three are forced by self-duality. A correct induction must mix paired GL facets for U,U* with a lower symplectic facet W, and show closure of the cyclic boundary with the FULL identified graded pairings. A lone isotropic prefix does not justify deleting that compatibility check. No global vertex/gluing coverage theorem has yet been supplied.

## 5. Higher-genus closed central fibers are compatible with the known method

This is a conditional assembly calculation, not a density theorem with its missing nonclosed input suppressed. Let G=Sp(2n), c=+I or -I, g>=2 and V_c={product[A_i,B_i]=c}. Write d=n(2n+1). The existing finite-group argument is sufficient for geometric irreducibility: Liebeck-Shalev Theorem 1.1(i), with its actual proof through Lemma 2.1, gives sum_(chi!=1)chi(1)^-2=o(1) for Sp(2n,q) as q grows through odd prime-power extensions. The source's Frobenius formula therefore gives

    #V_c(F_q)=|Sp(2n,q)|^(2g-1)(1+o(1))
             =q^((2g-1)d)(1+o(1)).                       (4)

Centrality of c is enough: |chi(c)|=chi(1). Every geometric component has dimension >=(2g-1)d, since the smooth target G has dimension d and a fiber is locally cut out by d equations. Choose a finite field defining all components and use Lang-Weil on ALL its extension fields; (4) forces one component of dimension exactly (2g-1)d and no smaller components are possible by the lower bound. The source's spreading argument then gives the characteristic-zero assertion. This uses the actual primary theorem, not an assertion that the statement of LS Theorem 1.8 itself covers central twisted Sp fibers; that theorem's printed statement is for GL and unique top-dimensional components.

For the spectral saturation choose primes p,q>2n and zeta of order pq. Put alpha_i=zeta^i, 1<=i<=n, and

    A1=diag(alpha_1,...,alpha_n,alpha_1^-1,...,alpha_n^-1),
    B1=diag(beta_1,...,beta_n,beta_1^-1,...,beta_n^-1),

where beta_i are distinct rational primes (used only at a complex witness). Every difference among the 2n eigenvalues of A1 is a unit in O_(K(zeta)): the exponent differences are nonzero with absolute value <=2n and coprime to p and q. Thus source spectral projectors are integral. With specified free eigenlines, the symplectic pairing pairs each alpha_i line perfectly with the alpha_i^-1 line; it is zero on every other pair. Choosing one vector in each line and its paired dual gives an integral symplectic basis. The gluing torsor is (G_m)^n and its R-unit points are dense when R contains sqrt(2).

Take w=[[0,I],[-I,0]], which acts by -1 on the diagonal Cartan. For c=I set (A2,B2)=(w,I). For c=-I set (A2,B2)=(w,diag(iI,-iI)), over a field containing i. In the second case w B2 w^-1=B2^-1=-B2, so [A2,B2]=-I. Remaining handles are identity.

At either witness, varying B1 gives (Ad_A1-1) on the Lie algebra and hence every root direction, since A1 is regular. Varying B2 diagonally gives -2 times the Cartan; this is a complex tangent computation, not inversion of 2 in an integral construction. The relation map is submersive. Varying A1 in the torus preserves its commutator with B1 and spans all n spectral directions; T->T/W is etale at the regular A1. Thus the fixed-spectrum fiber is smooth at this point.

ASSUME the self-dual nonclosed diagram assertion gives density for the cut surface with these paired eigenflags, INCLUDING its actual integral gluing. Then the closure D of V_c(R) contains the entire fixed-spectrum fiber. The automorphism A1 -> A1 B1 preserves integral matrices and the relation. Near the witness, eigenvalues of B1 are multiplicatively independent at a Baire-dense set because the beta_i are independent. Its powers therefore fill the n-dimensional centralizer torus. The source's analytic continuation and submersion proof now fills an analytic open in V_c; irreducibility gives D=V_c.

Everything in this paragraph is a compatible use of the source saturation proof and classical Lie theory. It does not identify a new contribution, and it does not establish the missing nonclosed input. The number field can be taken to contain K, sqrt(2), i, zeta_pq for this assembly; no uniform-field claim for an unfinished full diagram theorem is frozen.

## 6. Sharp boundary classes: a real change in the flag formalism, but no obstruction theorem

One cannot simply use every ordinary isotropic parabolic radical as the source's Jordan-column cap. In Sp4, write k=m=1 in (1). For A=(a,b), the strictly upper block H=N(A,z)-I has H^2=0. If (a,b) is nonzero then H has rank 2, whereas at a=b=0 and z nonzero it has rank 1. Thus the full line-parabolic radical generically gives Jordan type (2,2), not the transvection type (2,1,1). Its central one-parameter subgroup gives the latter. A Lagrangian parabolic similarly has a general symmetric 2x2 off-diagonal block, generically rank 2. Replacing the GL flag by an unrestricted symplectic parabolic flag therefore does not enforce the sharp rank-one boundary condition.

This failure is already repaired LOCALLY by a classical compatible operation. For any symplectic vector space and v,t set

    T(v,t)x=x+t<v,x>v.                                    (5)

It is symplectic because the two cross terms in the form cancel, and its inverse is T(v,-t). The nilpotent difference has square zero and rank <=1; it has rank 1 if v,t are nonzero over C. Conversely any rank-one symplectic unipotent matrix has this form: write N=v phi, use symplecticity to force phi to be proportional to <v,->. Therefore (5) covers the entire transvection orbit together with zero and has polynomial integral coordinates. R^(2n+1) is dense, so this individual boundary closure already has dense actual integral matrices. No roots of arbitrary nonunits or inversion of 2 is needed. This is classical transvection algebra, not a nominated advance.

More generally weighted nilpotent filtrations/Jacobson-Morozov collapses are compatible candidates for arbitrary boundary classes. A failure of an UNWEIGHTED parabolic cap does not show that those operations fail. What remains to be proved is that weighted boundary data and self-dual seam restrictions can be reduced together while preserving the product relation, free graded modules and every component. Independent density of each conjugacy class says nothing by itself about density on the product-one fiber. The source's actual rank-reduction is exactly what paid that coupling in type A.

## 7. Stronger compatible local operations and the remaining global interface

There is more available than the failed unrestricted-cap substitution. For any TWO isotropic partial flags of fixed types, their relative positions have finitely many Bruhat types. In the standard split model each type has an integral signed-permutation representative w, and its complex orbit is the image of Sp(2n) acting on the standard pair (F,wH). Integral symplectic matrices are Zariski dense: the elementary integral root subgroups contain infinitely many parameters and generate Sp(2n,C). Consequently every such pair orbit has a dense set of integral split representatives. This alone pays absolute two-flag position density, including nongeneric relative positions. It is not necessary to discard all lower Bruhat cells.

If the actual common double-graded modules are supplied free, with their perfect dual pairings, a common symplectic splitting is the natural relative version. The stabilizer of the pair is P intersect wQw^-1. In that split model its unipotent factors have Chevalley root coordinates with integral polynomial multiplication, and its Levi factors are products of GL and smaller Sp groups. Those are precisely compatible operations for replacing the additive common-splitting argument of the source. Our matrix formula (1) gives an entire maximal-parabolic instance, including the central correction at 2. No impossibility is inferred from the nonabelian factor.

The stronger required statement is RELATIVE to the prescribed maps and all weighted boundary data, not just existence of integral points in a flag orbit. For each finite rank/relative-position pattern arising from an original mixed self-dual surface solution, construct a lower-rank mixed diagram and an open surjective reconstruction tower with the following properties: every original complex solution is covered; every lower integral solution has integral lifts, dense in each complex fiber; paired/central blocks preserve the supplied perfect forms and all quotient identifications; both directions of each split/merge and paired interchange are allowed; every boundary cycle closes at its specified starting self-dual prefix; repeated occurrences of the same facet remain compatible; weighted boundary restrictions survive every step. Such a tower, together with genus-one central factors, would feed the ordinary source induction and the calculation in section 5. It has not been constructed here. Listing the split groups in its prospective fibers is not a proof of these properties.

Taking involution-fixed points of the existing GL theorem does not supply the missing tower. Density of a set in a variety need not imply density in its fixed locus, and even an affine involution can have no integral fixed points: x -> 1-x on A1_Z has the fixed point 1/2 over C but no fixed point over O_L for ANY number field L. The latter follows because 2 is a nonunit in O_L. This is only a counterexample to that general inference; it is not an obstruction example inside our symplectic surface problem. The explicit integral splitting in section 3 avoids this issue for its stipulated local data. A coordinated self-dual construction may avoid it throughout, but that must be shown.

Genus-one central fibers also need their representation-level treatment. At c=I, semisimple commuting Sp pairs lie in a common torus, so character-level density follows from unit parameters. At c=-I, the relation is AB=-BA, and A^2,B^2 commute with both matrices. The GL source pays the ordinary cyclic eigenblock decomposition; imposing a perfect alternating form pairs inverse central eigenspaces and introduces self-dual special blocks. This is a compatible classical classification route. Neither character-level density alone nor the GL representation theorem establishes the full symplectic representation-level density needed by every intermediate diagram. No full classification/deformation proof or actual primary almost-commuting-pair proof was read and assembled in this round, so this interface stays unpaid.

## 8. Research conclusion at the actual reduction reached

No theorem is frozen. The strongest developed reduction now pays full integral parabolic lifts, symplectic free splitting, absolute two-flag density, transvection boundary closures, and the higher-genus closed saturation CONDITIONAL on the remaining nonclosed input. These are classical/source-compatible calculations. The actual unpublished work still required is a coherent mixed self-dual, weighted-boundary rank-reduction and its genus-one representation-level input, followed by full quotient/component assembly. This is appreciably more precise than declaring that SL-density does not pass to Sp, but it is not a full proof or a new supporting nominee.

No identifiable nonroutine operation beyond the strongest compatible classical/source composition has been established. The possible type-C extension may be routine once the correct diagram language is supplied; the local calculations do not decide contribution. Difficulty, amount of bookkeeping, a new structure-group label, or exact-boundary completion alone supplies no substantial-contribution evidence. Decision: PREFREEZE / no nominee. No correctness/contribution grade, independent review, acceptance or count is assigned. No restricted replacement, current-open claim, worldwide-priority claim, exhaustion certificate or impossibility claim is made.
