# T027O: one integral mapping-class orbit in every rank

Myeongjin Kang, no affiliation. Original exposition CC BY 4.0. Author candidate for independent full-proof and contribution review; no acceptance or count is asserted. The exact scope was frozen in scope027o.md before the tangent argument was completed. Source truth is stipulated at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

## 1. Statement and input contracts

**Theorem T027O.** For every g>=2 and r>=2 there are a number field L contained in C and a homomorphism rho:pi_1(Sigma_g)->SL_r(O_L) such that the orbit of [rho] under the orientation-preserving mapping class group is Zariski dense in the entire complex SL_r character variety X_g,r.

The field is allowed to depend on g,r. This is one orbit of an actual integral representation. There is no generic-input hypothesis, restriction to a marked locus, or replacement by the union of arithmetic orbits. There is no punctured-surface assertion.

We use the pinned source027, `Integral points on character varieties of curves`, for the integral model and the irreducibility of the determinant-one closed surface relation variety (surfaces.tex, the SL_r intermediate assertion established inside the proof of Proposition `prop:surface-irreducibility`, lines197–248, with scalar c=1). The proposition statement itself concerns the GL_r fiber; the following scalar-extension paragraph passes from the SL_r intermediate fiber to GL_r. Its quotient X_g,r is therefore irreducible. On the locus of irreducible representations the tangent space is the kernel of the derivative of the relation modulo infinitesimal conjugation; the complex trace cup-product form is symplectic. This is the classical Goldman surface-character geometry, not a new assertion here. Goldman's 1986 §§4.3–4.7 identify the Hamiltonian flow of an invariant function of a simple curve with the corresponding centralizer twist. We will also justify the specific smoothness test and the use of a possibly singular orbit closure below.

For r=2 the entire statement is already supplied by Coccia–Litt, Proposition 5.0.1 and Theorem 5.0.2, together with Proposition 3.1.10: their construction is an actual SL_2(O_L) representation and has dense mapping-class orbit. These results are explicitly credited, not claimed anew. For the unit hypothesis of their Proposition 5.0.1 one may take K=Q(sqrt(5)) and v=(1+sqrt(5))/2, for which v−v^-1=1. Density over the algebraic closure of Q gives density after extension to C. The rest of this proof treats every r>=3.

Write d=r²−1 and T for the determinant-one diagonal torus. Use surface generators a,b,c,d0,a_3,b_3,...,a_g,b_g, with relation [a,b][c,d0] product_(i>=3)[a_i,b_i]=1. The symbol D is the matrix of d0; the integer d denotes the Lie-algebra dimension only when needed. All tangent matrices below are complex and traceless when used in sl_r.

## 2. A fixed arithmetic torus with a dense cyclic generator

Fix an integer c0>=3 and let f(X)=X^r−c0 X^(r−1)−1. On |X|=1 the middle term strictly dominates the sum of the other two, so Rouche's theorem gives r−1 roots inside the unit circle and one outside. There is a real root greater than c0, so it is the unique outside root. The polynomial is irreducible over Q: a proper monic integral factor not containing the outside root would have a nonzero integral constant term of absolute value less than one. Characteristic zero gives distinct roots alpha_1,...,alpha_r, and each is an algebraic unit.

If product alpha_i^m_i is a root of unity, put M=max_i m_i and apply a Galois automorphism sending a root carrying exponent M to the outside root. The sum of all logarithmic absolute values is zero. Each other log modulus is negative, so

 sum_i m_i log|alpha_i| = sum_i (m_i−M)log|alpha_i|

in the new ordering is positive unless all m_i=M. Thus the exponents of any such relation are all equal.

Choose a root of unity eta satisfying eta^r=(-1)^(r−1), and set mu_i=eta alpha_i. Then product mu_i=1, and the only character relations product mu_i^m_i=1 are the multiples of (1,...,1). In particular C_mu=diag(mu_i) generates T densely. Let L be the splitting field with eta adjoined.

The following set of diagonal integral matrices is Zariski dense in T:

 B(m)=diag(mu_1^m1,...,mu_(r−1)^m(r−1), product_(i<r)mu_i^(−mi)),  mi>=1.

Indeed the first r−1 coordinates range independently over infinite subsets of C*, so repeated Laurent-polynomial interpolation proves density. Every B(m) itself generates T densely: a character relation gives product_(i<r)mu_i^(mi(e_i−e_r))=1, hence mi(e_i−e_r)=0 for each i. Thus all e_i=e_r.

The group SL_r(Z) is Zariski dense in SL_r(C): its closure contains every elementary one-parameter root group because it contains all their integral points, and those root groups generate SL_r. Consequently pairs (B,Q), with B as above and Q in SL_r(Z), are Zariski dense in T×SL_r. For any such pair,

 C=Q C_mu Q^-1

belongs to SL_r(O_L), since Q^-1 is integral. Its centralizer is the torus T_C=Q T Q^-1, generated densely by C. We will select B,Q only after specifying finitely many nonempty open conditions.

## 3. Actual simple curves and their words

We first work in a genus-two subsurface with one boundary. Its standard rose has cyclic half-edge order

 a, b^-1, a^-1, b, c, d0^-1, c^-1, d0.

The based words bd0 and abcd0 represent simple nonseparating curves. To verify this directly, thicken the rose. The turns for bd0 pair (b^-1,d0) and (d0^-1,b); those chords in the vertex disk are nested. The turns for abcd0 pair (a^-1,b), (b^-1,c), (c^-1,d0), (d0^-1,a); those chords are noncrossing as well. Each edge is used at most once, so disjoint smoothing in the disk yields a single embedded closed curve. Their homology classes are primitive and nonzero.

Boundary-fixing Dehn twists about a and c can be chosen with based actions b->ba^m and d0->d0 c^n. They preserve [a,b] and [c,d0] exactly and fix the other handles. Hence, for every k,l>=1, both curves

 u0(k,l)=b a^k d0 c^l,
 u1(k,l)=a b a^(k−1) c d0 c^(l−1)                         (3.1)

are simple and nonseparating: they are images of bd0 and abcd0 under these twists, respectively.

For an extra handle i>=3 the base words abcd0 a_i and abcd0 b_i^-1 are also simple. In the full rose order, replacing the turn (d0^-1,a) by (d0^-1,a_i),(a_i^-1,a), or by (d0^-1,b_i^-1),(b_i,a), gives nested chords around the unchanged turns. Again each edge is used once. Applying the same twists therefore gives simple curves u1(k,l)a_i and u1(k,l)b_i^-1.

This based-word verification is necessary. The earlier work file's proposed family a^k b c^l d0 was not justified by free slope simplicity and is not used anywhere in this proof.

## 4. Generic Cartans and principal minors

Let h be the diagonal traceless algebra and h_C=Q h Q^-1. For r>=3 the following conditions hold on a nonempty Zariski open set of Q:

(P1) For every i!=j the linear map K->(K_ij,K_ji) from h_C to C² has rank two.

(P2) The torus T_C contains a regular matrix N with all off-diagonal entries nonzero and, for every triple of distinct indices,

 N_ij N_jk N_ki != N_ik N_kj N_ji.                       (4.1)

For P1 at a fixed pair, it suffices to find a regular matrix H for which H and H² minus its scalar part have independent (i,j),(j,i) projections. For the pair 1,2 use off-diagonal entries H12=H21=H23=H31=1 and H13=H32=0. The relevant 2×2 determinant is one, independently of the diagonal entries. Choose the diagonal generically so that H is regular, then subtract its trace. Its eigen-Cartan witnesses the required nonvanishing. Relabel and intersect the finitely many nonempty open conditions.

For P2, a generic invertible regular matrix has all the indicated entries and triangle differences nonzero. Scale it to determinant one. Its eigen-Cartan is a witness. Existence of such an element in Q T Q^-1 is open in Q: expand the finite product of the required nonzero expressions as a Laurent polynomial in the torus coordinates and require that not all its coefficients vanish. The fixed eigenvalues mu_i impose no restriction on the possible eigen-Cartans. Thus P1 and P2 are compatible nonempty opens on the irreducible parameter space SL_r.

**Principal-minor differential lemma.** Suppose M has all off-diagonal entries nonzero and satisfies (4.1). If every principal minor of M is stationary under a variation E, then E=[h0,M] for a diagonal h0.

The 1×1 minors give Eii=0. Set xij=Eij/Mij for i!=j. The 2×2 minors give xij+xji=0. In the derivative of the 3×3 minor, the diagonal and transposition terms vanish by these relations. What remains is

 (Mij Mjk Mki−Mik Mkj Mji)(xij+xjk+xki)=0.

Thus xij+xjk+xki=0. Fix a reference index and set h_i=x_i1, with h_1=0. Then xij=h_i−h_j, proving the lemma. For r=3 the full determinant supplies the 3×3 identity. We will always have its derivative zero, even though characteristic coefficients with index r are not varied.

This is an infinitesimal instance of classical principal-minor/diagonal-similarity rigidity. Loewy's global theorem and the cycle identities in Mantelos are antecedents; this lemma alone is not proposed as a new contribution.

## 5. A generic injective linear system

There is a nonempty Zariski open set of pairs (A,Q), A in T, for which the only S in sl_r satisfying

 (Ad_A−Ad_C)S=0,
 (I−Ad_C)S in h+h_C                                      (5.1)

is S=0. Here C=Q C_mu Q^-1 has the fixed eigenvalues chosen above.

To prove nonemptiness, choose a real orthogonal Q of determinant one with every entry nonzero. Then every element of h_C is complex symmetric and h cap h_C=0 in sl_r. In fact diag(k)Q=Q diag(lambda) implies k_i=lambda_j for all i,j, hence scalarity. Choose a real traceless diagonal H with distinct entries and set A(t)=exp(tH).

Suppose nonzero solutions S_t existed for a sequence of nonzero t tending to zero. Normalize their Hermitian norm to one and pass to a convergent subsequence S_t->K. The first equation gives K in h_C. Using that equation again,

 (I−Ad_C)S_t/t=(I−Ad_A(t))S_t/t -> −[H,K].

Since the left side lies in the fixed closed subspace h+h_C, so does [H,K]. But H and K are complex symmetric, hence [H,K] is skew-symmetric, whereas every element of h+h_C is symmetric. Therefore [H,K]=0. Distinct entries of H make K diagonal; the zero intersection h cap h_C then implies K=0, contradicting its norm. This proves injectivity for all sufficiently small nonzero t.

On the open locus h cap h_C=0, condition (5.1) is injectivity of a finite matrix of regular linear maps, after choosing a local basis for h+h_C; maximal-rank minors make it Zariski open. The witness just proved its nonemptiness. It need not itself satisfy P1. All the separate nonempty opens intersect because T×SL_r is irreducible.

We also require A to have distinct products a_I=product_(i in I)a_i on distinct subsets of the same size 1<=|I|<=r−1. These are finitely many nonzero Laurent-polynomial conditions on T and form a nonempty open. We may impose that Q has no zero entries, that C has no zero entries, and that B has distinct diagonal entries. Each is a nonempty open condition in the relevant parameters. For C the off-diagonal coordinate is not identically zero on the regular conjugacy class; the same is true of diagonal coordinates. Their finite intersection is nonempty.

## 6. The two-band tangent certificate in genus two

At the representation (A,B,C,I), with A,B diagonal, consider the characteristic-coefficient functions of A, of C, and of every word u0(k,l),u1(k,l) in (3.1). We prove that their common tangent kernel on the relation variety consists exactly of infinitesimal conjugations, provided the open conditions of §§4–5 hold.

The spectral functions of regular A,C imply delta A=[H_A,A] and delta C=[Z,C]. Subtract simultaneous conjugation by H_A and write

 delta A=0,  delta B=B U,  delta C=[Z,C],  delta D=V.

Cyclic rotation does not change characteristic coefficients. Thus for u0 use the matrix A^k D C^l B. Its variation, with delta A=0, is A^k times

 E_l=(V+Z)C^l B+C^l(Ad_B U−Z)B.                          (6.1)

For each j<r, the j-th characteristic coefficient of A^k M is, up to its fixed sign,

 sum_(|I|=j) a_I^k det M[I,I].                           (6.2)

The a_I are distinct and nonzero. If the coefficient's derivative vanishes for every k>=1, Vandermonde interpolation forces every derivative of each j×j principal minor of M to vanish. The determinant derivative is zero automatically: all original factors lie in SL_r, and the same is true of their infinitesimal variations. Apply this to M=C^l B and (6.1).

Since the powers C^l, l>=1, are dense in T_C, the resulting regular identities hold with C^l replaced by any N in T_C. Put X=V+Z, Y=Ad_B U−Z, W=X+Y=V+Ad_B U. At N=I, first principal minors of (XN+NY)B give Wii=0. Differentiate the vanishing second-principal-minor variation in a direction K in h_C at N=I. The first-minor variations already vanish identically, and the remaining equation is

 Kij Wji+Kji Wij=0.

P1 implies Wij=Wji=0 for every pair. Thus W=0 and V=−Ad_B U. The variation is now [X,N]B. At a good N from P2 apply the principal-minor lemma to M=NB. Its nonzero triangle differences differ from those of N only by the nonzero product of three diagonal entries of B. Hence [X,N]B=[h0,NB]=[h0,N]B. Regularity gives X−h0 in h_C. Diagonal conjugators may be made traceless by subtracting their scalar part; the residual centralizer element is then traceless as well. Subtract the diagonal conjugation h0. Setting S=Ad_B U leaves exactly

 delta A=0,  delta B=S B,  delta C=[S,C],  delta D=−S.     (6.3)

The derivative of [A,B][C,D] in (6.3) is (Ad_A−Ad_C)S. Thus a tangent to the relation satisfies T0:=Ad_A S=Ad_C S.

Now evaluate u1. At the point its matrix is M=A^k B C^l. Direct differentiation of a b a^(k−1) c d0 c^(l−1), using (6.3), gives

 delta M=T0 M+A^k B(S−T0)C^l−M S
        =[T0,M]+A^k B[R,C^l],  R=S−Ad_C S.              (6.4)

The conjugation term contributes zero to every characteristic derivative. Interpolation (6.2), followed by density of C^l, says that all principal minors of BN are stationary in the variation B[R,N] for every N in T_C. Apply P2 and the principal-minor lemma again. Since B is diagonal, it gives R−h1 in h_C for a diagonal h1. Therefore R belongs to h+h_C.

We have obtained precisely system (5.1), so S=0. Retracing the gauges shows that the original tangent was an infinitesimal conjugation. Conversely every conjugation annihilates all invariant functions, proving the assertion.

The representation is irreducible when B has distinct entries and every entry of C is nonzero: a B-stable subspace is a sum of coordinate lines, and no proper nonzero such sum is C-stable. The relation map is submersive when h cap h_C=0 and A is regular. Its derivative includes the sum of the images of Ad_A−I and Ad_C−I, by varying B on the left and D. With respect to the nondegenerate trace pairing, the annihilator of this sum is their common centralizer h cap h_C=0. Thus the relation variety is smooth here. The irreducible quotient has only the scalar stabilizer, which acts trivially, so it is a smooth character point of dimension 2(r²−1). The preceding kernel result therefore says that our invariant differentials span its cotangent space.

## 7. All genera and a finite spectral list

Keep the first two handles as above and put identity matrices on all extra handles. The first derivative of their commutators is zero, so these handles give independent tangent variables delta A_i,delta B_i in sl_r. Infinitesimal conjugation acts trivially on these identity entries. The core tangent argument still applies.

For k,l>=1 use the simple curves u1(k,l)a_i and u1(k,l)b_i^-1 from §3. At the point their matrices equal U_kl=A^k B C^l. Subtracting the trace differential of the core curve leaves respectively

 Tr(U_kl delta A_i),  −Tr(U_kl delta B_i).                (7.1)

These functionals detect all extra variables. Indeed the matrices U_kl, 1<=k,l<=r, span M_r if A has distinct entries and every entry of Q is nonzero. Vandermonde interpolation in k expresses every row projector Eii as a linear combination of A,...,A^r. The row i of C^l is

 sum_j mu_j^l Qij row_j(Q^-1).

The mu_j are distinct and Qij nonzero, so interpolation in l=1,...,r spans every row vector. Multiplication by the nonzero diagonal B does not alter this conclusion. The trace pairing with all M_r is nondegenerate, proving the claim.

The infinite family of invariant differentials consequently spans the full cotangent space of dimension (2g−2)(r²−1). Select finitely many of them that already span, and add all core words needed for (7.1) and the associated extra-handle curves. This is a finite set F of simple curves, with finitely many characteristic-coefficient indices. Existence of this finite set is enough; no effective bound is claimed.

More precisely, choose one point in the nonempty parameter open established above and choose F there. The nonzero maximal-rank minor of the relation derivatives together with these invariant derivatives is a regular or locally rational function of (A,B,Q). After clearing its nonzero denominator, it remains a nonzero regular function. Therefore there is a nonempty open in (B,Q) on which that function is not identically zero as a function of A. The smoothness and irreducibility conditions can be included in the same finite list of open conditions.

## 8. Arithmetic selection and nonresonant complex points

For each core band in the finite list F, its matrix along the family (A,B,C,I,...) is A^k B C^l with k,l>=1. The spectral map

 A in T -> characteristic coefficients of A^k B C^l

is dominant for (B,Q) in a nonempty open. To prove this, take Q=I, so C is diagonal with the fixed eigenvalues mu_i. Multiplication by B C^l is an automorphism of T; A->A^k is finite and surjective; and T->T/W is the finite dominant Weyl quotient. The Jacobian has full rank at some A. A corresponding minor, considered as a Laurent polynomial in A, remains not identically zero on a nonempty open in (B,Q). This is a witness in the same fixed eigenvalue conjugacy class, not a variation of C's eigenvalues. For extra-handle curves the spectral map is the same as for the associated core word.

Intersect these finitely many spectral-dominance opens with the open from §7. The parameter space T×SL_r is irreducible, so the intersection is nonempty. By §2 select B=B(m) and Q in SL_r(Z) in it. Now fix these arithmetic matrices and the number field L. The representation

 rho_0=(I,B,C,I,I,...,I)                                 (8.1)

takes values in SL_r(O_L).

Let Z be the Zariski closure of its mapping-class orbit. The twist a->ab fixes the other matrices. Its powers applied to (8.1) give (B^n,B,C,I,...), and powers of B are dense in T. Hence Z contains the entire irreducible family

 rho_A=(A,B,C,I,I,...,I),  A in T.                        (8.2)

Select a complex A in this family satisfying the tangent-spanning open and such that every monodromy of a curve in F generates its full centralizer torus. This is possible as follows. On the regular semisimple spectral locus, failure of cyclic torus generation means that some nontrivial character of T, modulo the determinant character, is one on an ordering of the eigenvalues. For a fixed character this is a proper hypersurface in T. Its finite Weyl image is a proper closed subset of the adjoint quotient. Dominance of each band spectral map implies that its inverse image is proper in the A-torus. Avoiding their countable union, together with the finitely many open-condition complements, is possible by the Baire theorem. The A-curve itself uses the dominant spectral map of A; the C-curve is already nonresonant by construction. Denote the resulting smooth irreducible character by x.

The selected A need not be arithmetic. This is legitimate because x already lies in the closure of the orbit of the single arithmetic representation (8.1). No Hilbert-irreducibility or simultaneous arithmetic nonresonance assertion is used.

## 9. From twist powers to an open orbit closure

We give the closure argument explicitly to handle potential singularities of Z. Let Z0 be an irreducible component of Z containing the closure of the family (8.2); such a component exists because the family is irreducible. Each mapping class permutes the finitely many components of Z. For each gamma in F choose a positive power of its Dehn twist preserving Z0.

Work on the ambient smooth irreducible-character locus and restrict to the open where the gamma-monodromy is regular semisimple. The finite cover that orders its eigenvalues is finite etale. Every irreducible component of this cover of the irreducible Z0-open surjects onto that open: flatness implies that every irreducible component dominates the integral base, and finiteness makes its image closed, hence surjective. At the point x, every ordering of the eigenvalues is multiplicatively independent modulo determinant. Thus no nontrivial character relation can hold identically on any of these covering components. For each such relation its zero set has proper finite image in Z0. The complement of the countable union is dense in the analytic topology on Z0 (apply Baire on its smooth dense locus, and then closure).

At any point y in this dense set, the chosen positive Dehn-twist power has the same cyclic torus closure as the full twist: a power of a dense cyclic subgroup of a connected torus is still dense. In the cut-surface description, twisting multiplies the transverse gluing matrix by the monodromy, or conjugates one side if the curve separates. Therefore the entire centralizer-torus orbit of y lies in Z0 by Zariski closedness. Goldman's theorem says the Hamiltonian field of each chosen invariant function on gamma is tangent to this torus orbit.

It follows that these holomorphic Hamiltonian vector fields preserve the defining ideal of Z0, not just a tangent space at x. For a local defining function f of Z0, its derivative along the field vanishes on the dense set just described, so vanishes on Z0. In a local finite generating set of the radical ideal this says Xf_j=sum_k a_jk f_k for holomorphic coefficients a_jk. The uniqueness theorem for the resulting linear differential system along integral curves implies that the local flow preserves Z0, including at its singular points. Equivalently one may use the local centralizer family and analytic closedness; the ideal argument states precisely why smoothness of Z0 is unnecessary.

At x, the differentials from F span the ambient cotangent space by §§6–7. Nondegeneracy of Goldman's symplectic form makes their Hamiltonian vectors span the ambient tangent space. Choose a basis from these vectors and compose their local complex-time flows starting at x. Every intermediate point stays in Z0, while the derivative of the composition map at zero is surjective. The holomorphic submersion theorem gives an ambient analytic open set contained in Z0. Since X_g,r is irreducible, that open set is Zariski dense. Thus Z0=X_g,r and Z=X_g,r. This proves T027O for all r>=3, and the credited rank-two theorem completes the frozen scope.

## 10. What is and is not being claimed

The source already proves potential density of the full integral-point set in every rank, and uses Dehn-twist torus saturation plus Baire extension. Goldman supplies the symplectic and twist machinery. Coccia–Litt supply single-orbit density in rank two and the pants-fiber torus method. Principal-minor rigidity has classical antecedents. Pickrell–Xia I, Proposition2.1.24/Lemma2.1.34 and §3, additionally provide centralizer-power infinitesimal spanning and transverse sewing antecedents; these materially constrain contribution credit. None of those ingredients is claimed as new here.

The candidate bridge is the explicit pair of simple-band families, their complementary tangent reductions, the generic injectivity of (5.1), and the finite-open arithmetic selection followed by generic complex saturation inside one arithmetic orbit closure. Its contribution classification remains for independent review. No global novelty claim follows from bounded searches.

The earlier proposed left-ordered word family is superseded, not silently certified. The corrected finite diagnostics in simple-band-diagnostic.json agree with the two-family reductions at r=2,3,4 over F1009. They are not an all-rank proof, not a characteristic-zero specialization theorem, and not an arithmetic-orbit computation. The proof above is independent of those numerical checks.

No author-side mathematical obligation is intentionally left unresolved in this candidate. Independent reviewers should especially check the ribbon/based-word conventions, the residual tangent system, finite-open arithmetic selection, and the component/flow argument. Formal verification has not been implemented; feasible scoped interfaces are recorded separately.
