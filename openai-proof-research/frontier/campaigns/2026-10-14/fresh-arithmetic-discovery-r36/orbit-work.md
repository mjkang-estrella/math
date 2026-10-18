# T027O: substantive orbit construction work

Myeongjin Kang, no affiliation; original prose CC BY4. Author work, not a review. Frozen target scope027o.md is unchanged. This file records proofs and the evolving candidate argument; statements explicitly labeled obligations are not established by finite checks.

## 1. Why the source's test point cannot itself work

The source dynamics.tex chooses diagonal A1,B1,B2 and a cyclic permutation A2=P, with other handles identity. Every image lies in N(T), the monomial normalizer. Replacing the prime beta_i by independent units makes it integral but leaves it monomial. Precomposition by any surface automorphism preserves the image subgroup, hence every character in its mapping-class orbit comes from a tuple in N(T).

For SL_r, N(T) has dimension r−1 and finitely many components. The image in the character quotient of Hom(pi1(Sigma_g),N(T)) consequently has dimension at most 2g(r−1), as does its closure. The whole character variety has dimension (2g−2)(r²−1) on its irreducible smooth locus. The inequality 2g<(2g−2)(r+1) holds for every g,r≥2. Thus this orbit closure is proper. This is a route exclusion, not a counterexample to T027O.

The source D is instead the closure of ALL integral points. Its fixed-spectrum fiber V_alpha is already contained in D before the test point is used. That fiber supplies the kernel of the spectral differential. Those directions cannot be silently transferred to the closure of a single orbit.

## 2. Integral Pisot-unit seed and dense image

Let f_r(X)=X^r−c X^(r−1)−1, c an integer at least3. On the unit circle the middle term dominates the other two, so Rouche gives r−1 roots strictly inside and one root strictly outside. The outside root is real and greater than c. The polynomial is irreducible over Q: any proper monic integer factor excluding the outside root has nonzero integer constant term of modulus less than1. Characteristic zero then gives distinct roots alpha_i, all algebraic units.

Any multiplicative relation product alpha_i^m_i equal to a root of unity has all m_i equal. Apply a Galois automorphism sending a root with maximal exponent M to the unique outside root. All other logarithmic absolute values are strictly negative, and the sum of all logarithmic absolute values is0. Hence the logarithm of the proposed product is strictly positive unless every exponent equals M. This proves the assertion. Parent independently supplied this same check; it is author assistance, not a gate.

Choose a root of unity eta with eta^r=(-1)^(r−1), and put mu_i=eta alpha_i. Their product is1 and their only multiplicative relations are integer multiples of the all-ones vector. Thus diag(mu_i) generates a Zariski-dense cyclic subgroup of the determinant-one diagonal torus.

The cyclic permutation P e_i=e_(i+1) gives characteristic polynomial f_r for P(I+cE12). Consequently C=eta P(I+cE12) is an integral SL_r matrix with those eigenvalues. Let B=diag(mu_i), and let A be diagonal with distinct roots of unity and determinant1. Then (A,B,C,I,I,...,I) satisfies the surface relation.

The image is Zariski dense in SL_r. Its closure contains the diagonal torus T because it contains B. Its Lie algebra is T-stable. Conjugating the diagonal Cartan by C or C inverse extracts the E12 root space, followed by its cyclic shifts. More explicitly Ad_C on a cyclic nearest-neighbor root has the next such root with coefficient1, plus distinct root weights; T-weight projection isolates that next root. Starting with E12 yields E23,...,Er1. Brackets of these directed-cycle roots give every Eij and the traceless diagonal algebra. Hence the Lie algebra is sl_r. The root-of-unity scalar eta does not affect conjugation. Parent independently suggested this root-weight check; it is credited as author assistance.

Smoothness of the source relation map survives this nonmonomial repair: varying B at fixed distinct diagonal A spans the off-diagonal matrices. On diagonal variations H of the fourth matrix, the diagonal part of (Ad_C−1)H is (Ad_P−1)H, spanning the traceless diagonals. Varying A diagonally changes its spectrum freely while preserving the commuting first handle. This proves the same local relation/spectrum submersions as the source. It does NOT yet prove dense mapping-class orbit.

The final candidate may use instead C=Q diag(mu_i) Q inverse with integral unimodular Q chosen from a nonempty Zariski open, and B chosen independently from the dense set

 B=diag(mu_1^m1,...,mu_(r−1)^m(r−1), product_(i<r)mu_i^(−mi)),  mi>=1.

Every such B generates T: a character relation forces mi(ai−ar)=0 for all i<r. This set is Zariski dense in T by repeated one-variable Laurent-polynomial interpolation. Integral unimodular Q are Zariski dense in SL_r, since their closure contains each elementary root subgroup. All these matrices are integral over one fixed splitting field with eta adjoined.

## 3. Orbit-closure torus before arithmetic genericity

Start from rho=(I,B,C,I) in genus2 (extra identity pairs for larger genus). The Dehn twist about b changes a to ab and fixes the other relevant matrices. Since powers of B are dense in T, the orbit closure contains the entire family rho_A=(A,B,C,I) for A in T. The initial point is arithmetic. A subsequently selected complex point in this family need not be arithmetic: it already belongs to the closure of the arithmetic orbit. This is the proposed way to avoid simultaneously imposing infinitely many multiplicative-independence conditions on arithmetic points.

For a simple band curve gamma_(k,l)=a^k b c^l d, k,l>=1, its matrix at rho_A is A^k B C^l. The curves a^k b and c^l d are primitive simple slopes on disjoint one-holed tori; a band sum across the separating neck gives a simple curve with this word after fixing compatible base paths. This topological convention must be included in the final proof rather than inferred from word length.

For any fixed finite list of k,l with k>=1, there is a nonempty Zariski open in the C-conjugacy family such that the characteristic-coefficient map A -> spectrum(A^k B C^l) is dominant. At diagonal C this is the ordinary elementary-symmetric map after invertible diagonal multiplication and the finite surjective power map A->A^k. A nonzero Jacobian minor persists as a polynomial condition in C and B. The same fixed eigenvalue conjugacy class contains that diagonal witness. Finite intersections of these nonempty opens remain nonempty.

Dominance ensures that full cyclic-torus generation for each selected band monodromy holds on a Baire-dense subset of the A-family: each nontrivial eigenvalue character relation, modulo determinant, is a proper algebraic condition on the finite eigenvalue cover. This is a complex genericity argument inside the orbit closure, not an arithmetic specialization claim.

## 4. Proposed all-rank tangent-spanning lemma, r>=3

Fix C regular semisimple with multiplicatively independent eigenvalues modulo product, and B diagonal. Let its Cartan be h_C. Require the following generic Cartan properties:

(P1) For every i!=j, the map H -> (H_ij,H_ji) from h_C onto C² has rank2.
(P2) Some regular C(t)=Q diag(t_i)Q inverse in its centralizer torus has all off-diagonal entries nonzero and C(t)_ij C(t)_jk C(t)_ki != C(t)_ik C(t)_kj C(t)_ji for every triple of distinct indices.

Both are nonempty Zariski-open conditions on a Cartan. For P1, use H and its traceless square: the determinant for a fixed pair i,j is a nonzero polynomial, witnessed on a three-index block having H12=H21=H23=H31=1 and H13=H32=0, then perturb the diagonal to make H regular. Relabel indices and intersect finitely many opens. For P2, a generic regular matrix has the listed inequalities; its eigen-Cartan supplies a witness. Fixed Pisot eigenvalues affect C but not the range of C(t) in that Cartan.

Let A be diagonal with distinct eigenvalues and distinct products on distinct subsets of equal cardinality. Define

 L_(A,B,C)=Ad_(AB)−Ad_B−Ad_C+I on sl_r.

Suppose L is invertible. Consider the differentials of the characteristic coefficients of A, of C, and of A^k B C^l D for all k,l>=1, at (A,B,C,D=I) on the surface relation variety. Their common kernel should be exactly infinitesimal conjugation; the following argument establishes the reduction.

The basic A,C coefficients make delta A=[H_A,A] and delta C=[Z,C]. Subtract conjugation by H_A to set delta A=0. Write delta B=B U and delta D=V. Then

 delta(B C^l D)=B[(U+Z) C^l+C^l(V−Z)].

Since delta A=0, interpolation in k of the characteristic coefficients of A^k M isolates the differentials of every proper principal minor of M=B C^l. Distinct subset products of A are exactly the needed distinct exponential bases. Since C^l is dense in its determinant-one centralizer torus, these polynomial identities persist with C^l replaced by every C(t).

Put X=U+Z,Y=V−Z,W=X+Y=U+V. At C(t)=I, first principal minors give W_ii=0. Differentiate the vanishing second-principal-minor identities in a Cartan direction H at I. The first-minor variations vanish identically, leaving

 H_ij W_ji+H_ji W_ij=0.

P1 forces every W_ij=0. Thus V=−U and the variation becomes B[X,C(t)].

An elementary principal-minor lemma: at a matrix M satisfying P2, a variation with every principal minor stationary is [h,M] for some diagonal h. First minors give delta Mii=0. Second minors imply xij:=delta Mij/Mij is antisymmetric. Third minors then give (forward triangle product−reverse triangle product)(xij+xjk+xki)=0. Hence xij=h_i−h_j. This proves the lemma without a global principal-minor reconstruction theorem.

Apply it at a good C(t) from P2 to M=B C(t); diagonal B cancels from the triangle inequalities. It gives [X,C(t)]=[h,C(t)], so X−h belongs to h_C. Thus delta C=[h−U,C]. Subtract diagonal conjugation by h. The remaining variation is

 delta A=0, delta B=B U, delta C=−[U,C], delta D=−U.

Its derivative in the surface relation [A,B][C,D]=I is L_(A,B,C) U. Invertibility forces U=0. This yields the asserted tangent kernel. Rank2 need not be rescued by P1: the full rank2 target is already a primary theorem of Coccia–Litt.

## 5. Why invertibility of L is a nonempty open condition

This is the current analytic witness to check carefully. Choose H real diagonal with distinct entries, B=exp(sH), s>0, and C=Q diag(mu_i)Q transpose with Q real orthogonal, all of whose entries are nonzero. Then h_C intersects the diagonal Cartan only in scalars: diag(k)Q=Q diag(lambda) forces every k_i=lambda_j. Let A(t)=exp(tH), with H traceless. At t=0, L=I−Ad_C has kernel h_C and image its trace-orthogonal complement. Its first derivative is Ad_B ad_H.

For a nonzero traceless real symmetric K in h_C,

 Tr(K Ad_B[H,K]) = sum_(i<j) |Kij|² (hi−hj)(exp(s(hi−hj))−exp(−s(hi−hj))) >0.

Strictness uses that a diagonal K in h_C is scalar. In a real symmetric basis of this Cartan the induced bilinear matrix is real symmetric positive definite, as follows by polarizing the displayed sum. Its complexification is therefore invertible. An arbitrary unitary Q would not justify this inference from positivity on real vectors; the real-orthogonal choice is essential to this witness. This witness need not satisfy P1: nonemptiness of the separate Zariski opens suffices for their later intersection. The Schur complement makes L_(A(t),B,C) invertible for small nonzero t. Consequently the determinant is not the zero regular function on T_A × T_B × the fixed C-conjugacy class. This witness is complex/analytic only; the eventual arithmetic B,Q are selected by Zariski density against the resulting finite polynomial conditions.

## 6. From infinite differential family to a finite certificate

Once §4 and §5 are complete, choose one parameter point satisfying their open conditions. The cotangent space is finite-dimensional, so finitely many k,l and coefficient indices already span. Their determinant is a nonzero rational function on the parameter family. After projection to B,Q, a nonempty open ensures that this determinant is not identically zero as a function of A. Intersect with the finitely many spectral-dominance opens from §3 and the irreducibility open (e.g. C has all entries nonzero, B distinct). Choose arithmetic B,Q from the dense sets in §2. Then choose complex A inside the closure family satisfying the determinant open and all required nonresonance conditions. There is no requirement that this A be arithmetic.

For genus g>2, add identity handle pairs initially. On the tangent space these extra pairs contribute freely because the first derivative of a commutator at (I,I) is zero. For each new handle, band a selected core curve u with its a_i and b_i. At the seed their monodromy is U=rho(u); subtracting the core trace differential leaves Tr(U delta A_i) or Tr(U delta B_i). Matrices A^k B C^l span M_r for finitely many k,l if all entries of the eigenvector matrix of C are nonzero: interpolation in k isolates rows, and powers of C span its Cartan, whose eigenprojector rows span each entire row space. Add those finitely many bands to the list. They therefore detect every extra tangent coordinate, and have the same torus-generating monodromy as the associated core curve. This is the proposed full-genus extension, not a separately nominated restriction.

## 7. Remaining geometric closure obligations

The parent/source generalized-twist and primary Goldman contracts must be read exactly. At a regular semisimple monodromy the closure of Dehn-twist powers contains the centralizer torus motion, and invariant characteristic functions have Hamiltonian vector fields among its directions. A finite set of Hamiltonian differentials spanning the cotangent should therefore force an open orbit-closure neighborhood by composing their local flows.

Do not infer this merely from full Zariski tangent space of a potentially singular closure. Instead take an irreducible component Z0 containing the A-torus family; a finite power of each twist preserves Z0. Nonresonance at the chosen A witnesses that each bad eigenvalue-character equation is not identically zero on the relevant finite spectral cover of Z0. Baire density and closedness then extend torus saturation to nearby points of Z0. This supplies local flow invariance, so composition and the submersion theorem produce an ambient open set. These extension details still need complete verification before calling T027O proved.

Finite diagnostic: ranks2,3,4 over F1009 give relation ranks3,8,15 and full cotangent ranks6,16,30 from the band families. This checks formulas, not all-rank truth, actual arithmetic genericity or orbit density. First diagnostic attempt required unavailable numpy and failed; it was replaced by pure-Python modular linear algebra. No failed output is labeled a passing check.

No full target conclusion, independent gate or nomination is made in this work file. The source-relative novelty question must also be revisited: the evolving argument uses source twist saturation as inspiration and source geometry as a contract, but several structural inputs are classical. A complete proof would still require operation-level contribution review, not a novelty inference from an absent theorem statement.

## 8. Topology correction before candidate completion

The claim in §3 that all based words a^k b c^l d are simple was not established by free slope simplicity. It must not be used. Boundary-fixing twists send b to ba^k and d to dc^l; left multiplication conjugates the boundary commutator instead. The tangent argument of §4 is valid for its word functions but is not, as stated, a simple-curve certificate. The determinant witness §5 remains an auxiliary calculation, not the final construction.

A repair uses TWO genuinely simple base bands and a different final linear system. In the standard oriented rose for the genus-two surface with boundary, the cyclic order of half-edges is

 a, b^-1, a^-1, b, c, d^-1, c^-1, d.

The word bd has turn pairs (b^-1,d),(d^-1,b), which are nested and disjoint in the vertex disk. The word abcd has pairs (a^-1,b),(b^-1,c),(c^-1,d),(d^-1,a), likewise noncrossing. Each edge occurs at most once, so smoothing these turns in a thickened rose produces an embedded closed curve. Both are nonseparating by their nonzero primitive homology. The boundary-fixing orientation-preserving twists b->ba^m and d->dc^n give the simple families

 u0(k,l)=b a^k d c^l,
 u1(k,l)=a b a^(k-1) c d c^(l-1),  k,l>=1.

At (A,B,C,I) with A,B diagonal both have monodromy A^k B C^l. Their infinitesimal formulas differ, and that difference is essential.

Retain P1 and P2 of §4. After the basic A,C spectral functions and gauge delta A=0, put delta B=B U, delta C=[Z,C], delta D=V. Cyclically rotating u0 gives A^k D C^l B. Its variation is A^k times

 (V+Z)C^l B + C^l(Ad_B U−Z)B.

Interpolation in k, extension in l, and the same first/second-principal-minor argument force V+Ad_B U=0. The principal-minor lemma at a good C(t) then gives V+Z=h+K with h diagonal and K in h_C. Subtract diagonal conjugation by h. With S=Ad_B U the residual variation is exactly

 delta A=0, delta B=S B, delta C=[S,C], delta D=−S.

The derivative of the surface relation is (Ad_A−Ad_C)S. Thus it vanishes precisely when T:=Ad_A S=Ad_C S.

For u1 write M=A^k B C^l. Direct differentiation in this residual variation gives

 delta M = T M + A^k B(S−T)C^l − M S
         = [T,M] + A^k B[R,C^l],    R=S−Ad_C S.

Conjugation does not change characteristic coefficients. Interpolation in k and density in l therefore imply that all principal minors of B C(t) have zero derivative along B[R,C(t)]. P2 and the elementary principal-minor lemma imply R in h_diag+h_C. Consequently the common kernel of BOTH simple families, modulo conjugation, is contained in

 (Ad_A−Ad_C)S=0,    (I−Ad_C)S in h_diag+h_C.                 (J)

The system (J) is generically injective on sl_r. Here is a separate nonempty-open witness, replacing §5 in the final route. Choose C=Q diag(mu)Q^transpose with Q real orthogonal and every entry nonzero, and H traceless diagonal with distinct entries. Set A(t)=exp(tH). If arbitrarily small nonzero t admitted nonzero S_t satisfying (J), normalize ||S_t||=1 and pass to a convergent subsequence S_t->K. The first equation gives K in h_C. Also

 (I−Ad_C)S_t/t=(I−Ad_A(t))S_t/t -> −[H,K].

The left side lies in the fixed subspace h_diag+h_C, so [H,K] belongs to that subspace. Every matrix there is complex symmetric, while K and H are symmetric and [H,K] is skew-symmetric. Hence [H,K]=0. Distinct diagonal H forces K diagonal. But h_C intersects h_diag only in scalars: diag(k)Q=Q diag(lambda), and all entries Qij nonzero, force every k_i=lambda_j. Since K is traceless, K=0, contradicting its unit norm. Thus (J) is injective for all sufficiently small nonzero t. This argument applies to complex S_t; it does not infer complex nonsingularity from positivity on real vectors.

Injectivity is a Zariski-open matrix-rank condition in (A,Q) on the open where h_diag cap h_C=0. The witness need not satisfy P1; the separate nonempty opens intersect on the irreducible parameter space. Choose H additionally outside the finite subset-sum hyperplanes to obtain the subset-product condition on A for small t. B remains an independent diagonal parameter. This proves the all-rank r>=3 tangent certificate with actual simple curves.

The corrected finite-field diagnostic uses only basic A,C spectra and these two families. For ranks2,3,4, u0 yields cotangent ranks5,14,27, and adding u1 yields6,16,30 respectively. These checks corroborate the predicted residual Cartan dimensions, but the argument above is the all-rank proof.

For extra handles, do not assert without proof that arbitrary based core words can simply be appended. Use the explicit base words abcd a_i and abcd b_i^-1, i>=3. In the rose cyclic order, the turns replacing (d^-1,a) are (d^-1,a_i),(a_i^-1,a), or (d^-1,b_i^-1),(b_i,a). They are nested around the unchanged turns, so both curves are embedded. Apply the same first/second-handle twists to obtain u1(k,l)a_i and u1(k,l)b_i^-1. At identity extra handles their trace differences from u1 detect respectively Tr(A^k B C^l delta A_i) and −Tr(A^k B C^l delta B_i). The matrix-span argument of §6 applies. Thus the corrected topology covers every g>=2, with no genus restriction.

Chronology: this correction was made before a candidate was completed or sealed. The full frozen scope027o.md is unchanged. Parent independently identified the same boundary-fixing distinction; its author-side warning is credited. The two-family repair and system (J) are author derivations, not an independent verdict.
