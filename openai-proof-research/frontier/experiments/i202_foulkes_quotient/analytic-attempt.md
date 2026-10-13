# I202: the actual Foulkes deficiency module

2026-10-12. **UNRESOLVED TARGET; NO SUBSTANTIAL NOMINATION.** All corpus theorems and lower operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted. No acceptance gate has been run. The new paid result below kills the explicit determinant class after **one** multiplication and supplies a corresponding family for odd primes. It does not kill the entire deficiency module.

## 1. Target, conventions, and dependencies

Over C, for a fixed number a of tensor rows, set

    R_j = ((Sym^j V)^{tensor a})^{S_a} = Sym^a(Sym^j V),
    A = C[R_1] inside R = direct_sum R_j,    C = R/A.

Products in C mean its A-module action. There is no multiplication of two arbitrary classes of C. Averaging and multiplication identify A_j with the image of the specified canonical map mu_(a,j): Sym^j(Sym^a V) -> R_j. These are the conventions in the quadratic source, Section 2, and the sixth-power reduction, equation (multmap), read in place.

For a=7 the exact target is C_8=0. The accepted module-generation operation gives C_j=A_1 C_(j-1) for j>=7, hence

    C_8 = A_1^2 C_6.                                      (1)

We retain this exact target. If it holds, the same operation gives C_j=0 for every j>=8; complete reducibility then supplies the ordinary seventh comparison for these j, while j=7 is the identity comparison. This does not identify an arbitrary equivariant embedding with the canonical map. The dimension-seven reduction follows because the target R_j has Schur length at most seven and the map is a natural transformation of homogeneous polynomial functors: evaluation in dimension seven detects every possible cokernel multiplicity space. No numerical dimension bound is assumed.

The I199 report, complete analytic record and parent response are read inputs, including their failed ambient-injectivity and regularity routes. We do not rerun those arguments as solutions. Primary new inputs are Domokos, *Vector invariants of a class of pseudo-reflection groups and multisymmetric syzygies*, arXiv:0706.2154v2, and Kotlar, *On extensions of the Alon–Tarsi Latin square conjecture*, arXiv:1204.5276v2. Both full papers have been read. Kumar–Landsberg, *Connections between conjectures of Alon–Tarsi, Hadamard–Howe, and integrals over the special unitary group*, has also been read in full to check the existing determinant-contraction connection. RSW Section 2 is read in place for the normalization and multisymmetric interpretation. Exact source scopes and hashes are in the authentication record.

## 2. Route I: actual multiplication, starting with the determinant

### 2.1 A proved family of socle submodules

Here is an auxiliary theorem about the actual quotient, not an ambient differential kernel.

**Proposition.** Let p be an odd prime. Use a=p in the algebra above. For every finite-dimensional complex V with dim V>=p, the multiplicity-one rectangular submodule

    W_p = S_((p-1)^p) V  inside R_(p-1)

injects into C_(p-1), is nonzero there, and is annihilated by A_1. Thus it is a submodule of the graded socle Ann_C(A_+). If dim V<p, W_p=0 and the annihilation assertion is vacuous. More generally the same proof works for any odd n>=3 for which the extended Alon–Tarsi constant AT(n) is nonzero.

For p=7 and dim V=7 this says

    A_1 [(det V)^6] = 0 in C_7.                          (2)

In particular its second products vanish in C_8. This pays the explicit class left open in I199; it does not prove (1) vanishes.

**Proof of survival and multiplicity.** First take dim V=p. In the polynomial ring of p rows, D=det(X) has degree one in each row and changes sign under a transposition of rows. Therefore D^(p-1) belongs to R_(p-1), is nonzero, and spans the representation (det V)^(p-1). The exponent is even, an essential point. In the Cauchy decomposition of Sym(V tensor C^p), the label factor S_((p-1)^p) C^p is one-dimensional, has the required equal row degree, and its permutation action is sign^(p-1)=1. Thus this rectangular constituent has multiplicity one, stably in V. The source of mu_(p,p-1) has outer degree p-1 and therefore Schur length at most p-1. It cannot contain this p-row constituent, so W_p survives in C_(p-1).

**Construction of its multiplication identity in dimension p.** Regard the row entries L_(i,k) as the coefficients of p linear forms and put

    F_L(y) = product_(i=1)^p (sum_(k=1)^p L_(i,k) y_k).

The coefficients of F_L are precisely generators of A_1, up to the harmless nonzero multinomial normalizations. For any degree-p form F, introduce p independent vector variables x_1,...,x_p and the differential operator

    Omega = det( partial / partial x_(j,k) )_(j,k=1)^p.

Define the covariant

    K(F;y) = [ Omega^(p-1) product_(j=1)^p F(x_j) ]_(x_1=...=x_p=y).       (3)

Every coefficient in y of K is a degree-p polynomial in the coefficients of F. Indeed the product has p such coefficients in each term, and differentiation/evaluation changes only the x variables. Every x_j has p-1 derivatives applied, so degree one remains in each block and K has degree p in y.

Write F_0(y)=y_1...y_p. For F=F_0, expand Omega^(p-1). A term survives on product_(j,k) x_(j,k) exactly when the p-1 permutation matrices selected by the determinant factors have disjoint supports. There is then one remaining cell in every row and column; these cells form a permutation matrix. Upon setting x_j=y the remaining monomial is always product_k y_k. Differentiating a squarefree monomial gives coefficient one, so

    K(F_0;y) = kappa_p F_0(y),
    kappa_p = [product_(j,k) X_(j,k)] per(X) det(X)^(p-1).               (4)

There is neither an unsigned count nor an assumed positive coefficient in (4).

The chain rule under x_j -> L x_j multiplies Omega by det(L). Consequently, for invertible L,

    K(F_L;y) = kappa_p det(L)^(p-1) F_L(y).              (5)

Both sides are polynomial in L, so (5) holds also for singular L. In particular it is an identity in the original row polynomial ring, not only a statement on a localized chart.

**Nonvanishing of the scalar.** Kotlar's Theorem 2.2, with its definition of normalized unipotent squares, proves

    kappa_p = (-1)^(p(p-1)/2) p!(p-1)! AT(p).

Its Corollary 3.6 proves AT(p) congruent to (-1)^((p-1)/2) modulo p. Both statements and the coefficient-count and group-action proofs leading to them were read in the primary paper. Hence AT(p), and thus kappa_p, are nonzero integers. The factorials make kappa_p zero modulo p; it would be erroneous to reduce kappa_p itself modulo p and infer nonvanishing. The modular argument applies to AT(p) before multiplying by the factorials. Over C division by kappa_p is valid.

Comparing coefficients of y in (5), each det(L)^(p-1) times a coefficient of F_L is a degree-p polynomial in the coefficients of F_L. Therefore

    D^(p-1) A_1 is contained in A_p                    (dim V=p).       (6)

This is exactly A_1 W_p=0 in the quotient, not just nonzero occurrence of its representation in the source.

**Extension to all dimensions.** The multiplication image of W_p tensor Sym^p V in R_p is a natural polynomial subfunctor. By Pieri, every constituent of this tensor product other than

    S_(2p-1,(p-1)^(p-1)) V

has p+1 rows: a horizontal p-strip added to the p-row rectangle can extend the top row and can create a new bottom row; if it creates no bottom row, all p new boxes are in the top row. But R_p=Sym^p(Sym^p V) has length at most p, so all the p+1-row constituents map to zero in R_p. The possible multiplication image is therefore a single copy of the displayed p-row Schur functor. It is nonzero, since D^(p-1) z(e_1) is a nonzero polynomial. The composite of this functor with R_p -> C_p vanishes in dimension p by (6), which detects its entire stable multiplicity map. It therefore vanishes in every dimension. As A is generated by A_1, annihilation by A_1 implies annihilation by A_+. This completes the proposition.

### 2.2 What remains after this calculation

For p=7, the killed multiplication image in degree seven has highest weight (13,6,6,6,6,6,6). Its subsequent products vanish in the quotient. The identity does not establish any rank assertion for another C_6 multiplicity space.

There is an explicit other constituent in C_6. In dimension seven, the nonzero highest-weight polynomial

    D^2 z(e_1)^4

has row degree six and weight (30,2,2,2,2,2,2). It is invariant under row permutations and belongs to R_6. As before, A_6 has Schur length at most six, so this seven-row constituent survives in C_6. It differs from W_7=(6^7). Likewise D^4 z(e_1)^2 has weight (18,4,4,4,4,4,4) and survives. These are explicit witnesses that W_7 does not exhaust C_6; they are not asserted counterexamples in C_8. Multiplication in the domain R cannot decide membership in A after multiplication.

Thus, letting W_7 denote its embedded socle copy in C, the exact outstanding question can be written

    A_1^2 (C_6/W_7) = 0.                                (M78)

This is equivalent to (1), since A_1 W_7=0. No decomposition or dimension estimate for the full remainder is assumed.

### 2.3 Attempt to straighten the remainder using all multisymmetric relations

This part uses the affine chart only to give an exact filtered algebra model; localization itself is not used as a vanishing estimate.

Fix coordinates x_(i,0),...,x_(i,6) in the seven rows, z=product_i x_(i,0), and write y_(i,k)=x_(i,k)/x_(i,0). Let

    B = C[y_(i,k): 1<=i<=7, 1<=k<=6]^{S_7}.

Let B_[j] be the invariant polynomials all of whose monomials have degree at most j in each separate row y_i. The map f -> z^j f identifies B_[j] with R_j, by unique separate homogenization; no denominators remain in this identification. Define e_alpha by

    product_i (1 + sum_k t_k y_(i,k)) = sum_alpha e_alpha(y) t^alpha,

where 0<=|alpha|<=7 and e_0=1. Let E_[j] be the span of products of at most j nonconstant e_alpha. Separate homogenization gives exactly

    A_j = z^j E_[j],     C_j = B_[j]/E_[j].               (7)

Each e_alpha is at most linear in every row, so E_[j] is contained in B_[j]. The reverse inclusion is the missing assertion, not a consequence of generation of B. Multiplication by A_1 becomes multiplication by E_[1]. By the paid module-generation lemma,

    B_[8] = E_[1] B_[7] = E_[2] B_[6].

The desired new straightening estimate is therefore

    E_[2] B_[6] is contained in E_[8].                   (S78)

Under (2), the part generated by the dehomogenization of D^6 is already in E_[7] after one multiplication. The rest of (S78) is unresolved.

Domokos, Proposition 2.1 and Theorem 2.5, give a complete characteristic-zero presentation of B in polarized power sums p_w=sum_i w(y_i). Its fundamental relation is

    sum_(pi partition of [8]) (-1)^(8-|pi|)
       product_(blocks H in pi) (|H|-1)! p_(product_(h in H) w_h) = 0.     (8)

The sign agrees with the paper: for eight inputs (-1)^(8-|pi|)=(-1)^|pi|. The relations (8) generate all relations among the unrestricted p_w. They rewrite a product of eight traces as products of at most seven traces. This is an actual all-relations theorem, but its length is trace length, not the E_[j] length.

The failure can be seen without a computation. Restrict to one list coordinate. Newton's expression for p_(y^d) in the algebraically independent elementary polynomials e_1,...,e_7 contains e_1^d with coefficient one. Consequently its minimal elementary factor length is d, although its trace length is one. The apparent bound of seven traces says nothing like an eight-elementary-factor bound.

Row bounds might still rescue (S78), so this observation is not a counterexample to the target. They are lost term by term in the standard straightening. For example

    f = product_(i=1)^7 y_i^6 = e_7(y)^6

belongs to B_[6] and E_[6]. Inclusion-exclusion/ Newton expansion of the distinct-row sum in traces contains a nonzero p_(y^42) term, together with other trace products that cancel its high-row-degree monomials. That individual term needs elementary length 42. Thus a termwise application of (8), followed by termwise Newton conversion, does not preserve either the relevant row bound or a usable elementary length. The cancellation needed to recover length eight for an arbitrary element of E_[2]B_[6] has not been proved. Domokos's finite-presentation degree bound is in total polynomial degree and also does not supply it.

As a check against claiming that a complete presentation automatically supplies diagonal surjectivity, the corresponding uniform assertion B_[a]=E_[a] is false at a=5 by the actual canonical (5,5) kernel in Cheung–Ikenmeyer–Mkrtchyan, Theorem 6(b). At the diagonal the map is an endomorphism, so its nonzero kernel also means a nonzero cokernel. The relations and characteristic-zero generator theorem hold there too. This counterexample concerns the proposed general proof principle; it does not refute S78.

**Route I boundary.** A genuine new result on multiplication is proved for the determinant socle. For the entire module, the missing estimate is (S78), or equivalently (M78). No monotone straightening in elementary length with the row bounds has been obtained.

## 3. Route II: all-slot jet elimination with compatibility retained

This route works directly with T, the symmetric seven-linear form on E=Sym^8 V annihilating A_8 under the canonical pairing. Put F(P)=T(P,...,P). The full condition is

    F(product_(i=1)^8 u_i)=0 for every u_1,...,u_8 in V.   (D)

It is not replaced by an arbitrary equation on a padded subvariety.

### 3.1 The complete coefficient identities, including repetitions

Take eight pairs of vector variables u_i,w_i and set

    P_B = product_(i in B) w_i product_(i not in B) u_i,
    P(s)=sum_(B subset [8]) s_B P_B=product_i(u_i+s_i w_i).

For alpha in {0,...,7}^8, condition (D) implies the simultaneous identity

    sum_n 7!/(product_B n_B!) T((P_B)^(n_B): B subset [8]) = 0,           (9)

where the sum is over nonnegative integer n_B satisfying

    sum_B n_B=7,     sum_(B containing i) n_B=alpha_i for each i.

**Proof.** Expand T(P(s),...,P(s)); group ordered choices of its seven subsets B by their multiplicities. The multinomial coefficient counts those choices, while the exponent of s_i counts how many selected subsets contain i. This proves (9), with no division by a possibly zero coefficient. Conversely, if the full family holds as polynomial identities in u,w, all coefficients of F(P(s)) vanish and the original condition follows. In particular the term alpha=(7,...,7) is the original diagonal condition on the w_i; retaining only low alpha is a strictly different system. No completeness claim is made for a truncated family.

For alpha the indicator of a two-element set {i,j}, (9) says

    7 T(P_{ij},P_empty^6) + 42 T(P_i,P_j,P_empty^5)=0.    (10)

Both terms have the same aggregate perturbation degree. Slot symmetry identifies exchanges of arguments but does not turn (10) into two separate vanishings. A proposed induction ordered only by perturbation degree therefore has no triangular pivot at this first nontrivial stage. Choosing their values in ratio -6 gives a consistent nonzero solution of this one local relation; this is not asserted to extend to a global T. It precisely explains why this local relation cannot be eliminated in isolation.

### 3.2 A further compatible Hessian restriction

The paid I199 contraction, using weights (8,6) and (7,6) in the quadratic source's one-step operation, gives

    T((x^6 yz)^6,R)=0 for every R in E and x,y,z in V.    (11)

The arbitrary R follows by spanning with pure powers. Differentiating the polynomial identity (11) in x,y,z, rather than discarding the dependence of its other slots, gives the new recorded consequences

    T((x^6 yz)^5, x^5 yz a, R)=0,
    T((x^6 yz)^5, x^6 z a, R)=0,
    T((x^6 yz)^5, x^6 y a, R)=0                        (12)

for every a,R. The scalar factors are respectively 36, 6, 6 and are nonzero. In differential language the Hessian of F at P=x^6 yz annihilates the image of the differential of (x,y,z)->x^6 yz in one argument, with its other argument arbitrary. This is stronger information than the value F(P)=0 alone and retains all seven-slot compatibility.

An attempted continuation would need to free the second slot in (12), or combine different basepoints to make (9) triangular. Neither follows: varying a basepoint differentiates every repeated slot, creating exactly the terms whose separation is in question. The image of that differential is only a tangent subspace, not all E.

There is an explicit counterexample to replacing (D) by this singularity/Hessian restriction. In a two-dimensional subspace with coordinates X,Y, write

    P=sum_(k=0)^8 binom(8,k) a_k X^(8-k)Y^k,
    q(P)=sum_(k=0)^8 (-1)^k binom(8,k) a_k a_(8-k).

The bilinear contraction defining q uses eight copies of the alternating two-dimensional form, so q is GL_2-relative invariant. For P=X^6 Q only a_0,a_1,a_2 may be nonzero and q(P)=0. Relative invariance gives q(x^6 Q)=0 for every x,Q. Therefore

    G(P)=q(P)^2 a_0(P)^3

is a homogeneous degree-seven polynomial whose full gradient vanishes on every x^6 Q. Differentiating that vanishing gives all the tangent-Hessian vanishings (12). But G(X^8+Y^8)=4, since q(X^8+Y^8)=2 and a_0=1. The binary form X^8+Y^8 is a product of eight linear forms over C. Hence G fails (D). To obtain the same counterexample in dimension seven, choose a linear projection V -> span(X,Y) that is the identity on this binary subspace, and pull G back along Sym^8 of that projection. It still has zero full gradient on every x^6 yz, since its binary argument has that form, and still takes value 4 at X^8+Y^8. Thus the failure is present in the dimension of the target as well. This is a counterexample to the proposed weakening, not a counterexample to mu_(7,8); indeed all binary forms split.

### 3.3 Exact full-system operator and the remaining estimate

For clarity, the full identities have a concise tensor expression. Put the 56 positions in a 7-by-8 array, with one row for each argument of T. On (V*)^{tensor 56}, let P_H average over within-row permutations and permutations of rows, and let P_K average over within-column permutations and permutations of columns. Thus

    H = S_8 wreath S_7,     K = S_7 wreath S_8.

T is represented by t with P_H t=t. Evaluating at product inputs and polarizing every factor says exactly P_K t=0. This follows by averaging within the seven occurrences of each factor u_i and then permuting the eight factors. It retains all the coefficient identities (9), not just their squarefree members.

Choose a Hermitian inner product so the two permutation averages are orthogonal projections. On im(P_H) set

    G = P_H P_K P_H.

Then <Gt,t>=||P_K t||^2. The new elimination estimate one would have to prove is

    ker(G | im(P_H))=0 on the Schur components of length <=7.            (J78)

Equivalently, on this finite space there must exist some epsilon>0 with <Gt,t> >= epsilon ||t||^2. Positivity of the projection averages proves only nonnegativity; it does not prove this strict inequality. No positive coefficient or spectral gap is assumed. The diagonal (5,5) counterexample shows that the corresponding general assertion about two symmetrizers is false. A proof here must exploit the particular (7,8) configuration, not just self-adjointness or permutation symmetry.

The result of Route I removes the multiplication coming from W_7 but supplies no lower bound for G on every remaining multiplicity space. No compatible nonzero vector in ker(P_K) intersect im(P_H) has been constructed, either. The explicit polynomial G(P) in the previous subsection (a different use of the letter G) fails the full system at a displayed product, so it cannot be used as such a vector.

**Route II boundary.** The newly attempted estimates are simultaneous elimination of the full repeated-index family (9), and strict positivity (J78) after all symmetries. The tangent-Hessian restrictions (12) are paid, but their insufficiency has an explicit product countercheck. The required full-system injectivity remains unresolved.

## 4. Contribution boundary and verdict

The actual determinant class in C_6 is no longer an unchecked candidate: (2) kills it after one multiplication, with a full polynomial identity and a primary-source nonvanishing proof. The odd-prime socle family is a complete auxiliary deduction. It is new in this attempt, not certified new to the literature. Determinant contractions and their Latin-square interpretation are established tools: Kumar–Landsberg Proposition 2.1 and Theorem 1.9 make that prior connection explicit, and the scalar used here is exactly Kotlar's known invariant. Packaging this as a socle statement alone is not sufficient novelty/significance evidence for a substantial nomination.

For the full (7,8) target we have neither proof nor counterexample. The remainder contains explicit other seven-row constituents, and the two estimates S78 and J78 have not been paid. No new canonical range or ordinary seventh Foulkes theorem is claimed. Eight findings remain accepted and two remain; both independent acceptance gates stay with the parent.

All validation was written mathematics and direct source reading. It checked parity of the determinant exponent, the factorial normalization before using the prime congruence, polynomial extension across singular L, Schur lengths in every dimension, separate row degrees in (7), and a product evaluation refuting the weakened jet condition. There was no research code, numerical scan, test run, certificate replay, snapshot, seal, child agent, staging, commit, or publication.
