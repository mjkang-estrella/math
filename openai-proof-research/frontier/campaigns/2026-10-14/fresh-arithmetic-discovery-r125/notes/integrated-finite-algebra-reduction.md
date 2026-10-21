# Integrated finite-algebra root calculation

**PREFREEZE / no nominee.** No statement is frozen as an acceptance candidate. These are completed source/classical reductions and a source-independent diagnostic of singular root equations. They are not independent correctness/contribution grades. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and operative proofs remain stipulated true. The purpose is to identify the strongest compatible composition before calling any operation unpaid.

## 1. Representation and source input

Let p be a prime in binary. A is a nonzero commutative associative unital F_p-algebra of dimension D>=1, supplied by structure constants and the coordinates of its unit. Algebra promises can be checked by polynomially many exact identities if desired; no black-box algebra or unknown characteristic is intended. An element is a D-vector. Dense polynomials are supplied by their full coefficient lists. Polynomial bit complexity means a fixed polynomial in D, the dense polynomial degree, and log p; it is not polynomial in the cardinality p^D. Products and quotients below are represented by bases and linear maps.

The pinned paper *Deterministic Polynomial Factorization over Prime Fields*, introduction thm:factorization, gives complete irreducible factorization with multiplicities in O(((n+1)ceil(log2 p))^(10^12)) bit operations, absolute implied constant. It includes small p, inseparable multiplicities, and constants. Its sections02 and08 explicitly provide dynamic evaluation, Frobenius fixed algebras, polynomial CRT, and a driver handling every characteristic. Section07 supplies the full odd-split procedure and its geometric/divisor interfaces; section10 supplies its small auxiliary-prime argument from the stipulated companion's zero-free input. No randomness, integer-factorization or primitive-root oracle is introduced here.

Actual primary comparison: Friedl–Ronyai, Oregon report CIS-TR-85-03 (1985), Proposition3.3, Theorem5.7, Propositions6.4–6.5, and the SPLIT2 proof/Proposition7.7/Theorem7.8. They already compute minimal polynomials by linear dependence, split commutative semisimple algebras by factoring them, and recurse on the resulting ideals. Their general radical procedure is stronger than the elementary commutative Frobenius procedure below. Their finite-field factoring subroutine was randomized or polynomial in p; the pinned theorem pays that subroutine deterministically in log p. The source's Berlekamp operation also gives the particularly transparent prime-field-only reduction below. This is ordinary composition, not a claimed new algebra decomposition theorem.

## 2. Nilradical and the canonical coefficient algebra

Let J be the nilradical. Finite-dimensional commutative Artinian structure gives J^D=0 and A/J a product of finite fields. One way to see the exponent bound is to use the descending radical-power chain: before zero, equality J^i=J^(i+1) would force J^i=0 by Nakayama; there are at most D strict dimension drops. Equivalently one may use the usual triangular representation of a commutative Artinian algebra. This elementary structural input is credited, not newly invented.

Let F:A->A be x |-> x^p, an F_p-linear ring endomorphism. Choose k>=0 with p^k>=D, using the least such k. Then

    ker(F^k)=J,    S=im(F^k),    A=S directsum J as F_p-vector spaces.

Indeed every j in J has j^(p^k)=0. Conversely any element killed by a power is nilpotent. The map induced on B=A/J is bijective since B is a product of perfect fields. Thus S maps surjectively onto B, and dim S=D-dim J=dim B, so the map is an isomorphism and S intersects J trivially. S is a unital subalgebra. It is the unique coefficient subalgebra: any reduced finite subalgebra mapping isomorphically onto B is perfect and hence contained in im F^k, with the same dimension. In particular no arbitrary incompatible field sections are chosen on different components.

Compute F by powering each basis element, then F^k by matrix powering; compute its image/kernel and the quotient map by linear algebra. Here k<=ceil(log2 D), so the complexity is polynomial. More generally, F^s for a binary integer s is computed in O(log(s+1)) matrix multiplications. The astronomically long integer p^s need never be written. This will matter in section6.

## 3. Full component splitting, with no hidden extension-field factoring oracle

Work in S. Set E=ker(F-id on S). If S=product_i K_i with [K_i:F_p]=d_i, then E=F_p^r where r is the number of factors. An ordered vector basis of E is available by linear algebra.

Start with the identity projector e=1. On a current piece eE of dimension>1, some projected basis vector b is nonscalar (not in F_p e). Find one by linear algebra. Compute its minimal polynomial over F_p from the first linear dependence among e,b,b^2,... . It is squarefree and splits into distinct linear factors because b has its coordinates in F_p. It has at least two distinct factors. Factor it using the pinned prime-field algorithm. Polynomial CRT yields projectors P_alpha(b) for its distinct roots alpha; their sum is e, they are orthogonal nonzero idempotents, and each proper piece has smaller dimension. Continue until each e_i E is one-dimensional.

There are at most r-1 genuine refinements and O(r) pieces overall. All linear systems/polynomials have dimension/degree at most D. The primitive projectors e_i of E are exactly those of S and A. Thus

    A=product_i A_i,   A_i=e_i A,   J_i=e_i J,   K_i=e_i S,
    A_i/J_i=K_i.

All equalities are explicit maps: a |-> (e_i a), with inverse summation. This construction works when r>p; it never assumes that a product of too many copies of F_p has one primitive element with all coordinates distinct. The source's large-p scalar-grid search is not incorrectly imposed on small characteristic. The classical primary proof already allows iterative splitting. Using the fixed algebra to keep every factorization over F_p is a standard Berlekamp composition.

Now let K be an explicitly given finite extension of F_p of degree d and h in K[T] dense. Squarefree decomposition is deterministic: inverse coefficient Frobenius is F^(d-1), and the derivative-zero step reduces degree without looping p times. For squarefree h, regard C=K[T]/h as an F_p-algebra of dimension d deg h. Apply the reduced splitting just described. Each e_i C is a field and retains the explicit embedding K->e_i C, a |-> a e_i. The first K-linear dependence of e_i,e_i T,... computes the irreducible factor h_i of h. Multiplicities are restored from squarefree decomposition. This supplies complete deterministic factoring over every explicit K, with polynomial complexity in d,deg h,log p, without assuming Lenstra's unread isomorphism theorem or a primitive-root/discrete-log oracle.

## 4. All simple residue roots and their exact lifts

For f in A[T], compute on each K_i the distinct roots r of its residue polynomial for which the residue derivative is nonzero. This uses section3, including arbitrary degree drops. Lift r via K_i inside A_i. If f(x) lies in J_i^t and f'(x) is a unit, replace

    x by x - f(x)/f'(x).

The new error belongs to J_i^(2t), by the polynomial Taylor identity, in every characteristic. A unit inverse is computed by solving its multiplication matrix (or by a geometric series after reduction). At most ceil(log2 D) steps give an exact root. Uniqueness in that residue class follows from

    f(x)-f(y)=(x-y)(f'(y)+(x-y)g),

because the second factor is a unit when x-y is nilpotent. This is ordinary nilpotent Hensel/Newton lifting. It retains the exact polynomial coefficients and does not assume a reduced algebra.

The output is local root lists and the explicit product map. A global list may have exponentially many elements, so no polynomial-time explicit enumeration of every tuple is claimed. If all local residue polynomials are nonzero and squarefree, this gives the FULL root set as a Cartesian product of lists. For general f it gives precisely the roots whose derivatives are units, not an answer to singular root finding.

## 5. The whole square-zero case is also paid

Suppose J^2=0. This allows full root finding, including singular and identically zero residue polynomials. Treat each local piece A_i=K_i directsum J_i, where J_i is a K_i-vector space with known basis u_1,...,u_t. Write

    f(T)=f_0(T)+sum_l u_l f_l(T),     f_l in K_i[T].

For r in K_i and j in J_i,

    f(r+j)=f_0(r)+f_0'(r)j+sum_l u_l f_l(r).

If f_0 is not identically zero, factor it to list its distinct roots r. For f_0'(r) nonzero, there is exactly one lift, j= -sum_l u_l f_l(r)/f_0'(r). For f_0'(r)=0, there are all |J_i| lifts if every f_l(r)=0, and no lifts otherwise. Thus the complete local root set is a union of singleton lifts and cosets r+J_i, with at most deg f pieces.

If f_0 is identically zero, roots are precisely the cosets r+J_i for common roots r of all the f_l. Compute their monic gcd and factor it. If all f_l vanish identically, the entire A_i is the root set and is returned symbolically as such. This handles also the identically zero local polynomial, constants, mixed local degree drops, and arbitrary p. Counting and selecting one root use the same representation. For global A, take the Cartesian product and multiply counts.

This is a fully paid extension, not an unpaid 'nilpotent compatibility' bridge. The square-zero Taylor identity and ordinary field gcds are sufficient. Nor is it a substantial nominee merely because the source title mentions fields rather than algebras.

## 6. Unit powers, even with compressed p-power exponent

Consider unit a in A, a nonnegative integer s in binary, and a positive integer m coprime to p. Write the exponent symbolically as p^s m. Complexity here is polynomial in D, log p, m, and log(s+1). Dependence on m is its NUMERICAL value, not just its bit length. Nothing below solves general binary-exponent root extraction over finite fields in time polynomial in log m.

Use section2 to write uniquely

    a=a_0(1+b),   a_0 in S*,   b in J.

On each residue field K_i, compute a_0^(F^(-s)) using s modulo d_i and factor T^m-a_0^(F^(-s)). Its roots r_i are exactly the solutions of r_i^(p^s m)=a_0. Store them by components; the number is either zero or gcd(m,p^(d_i)-1). The order p^(d_i)-1 has polynomial bit length; this gcd uses no integer factorization or discrete logarithm.

Choose k with p^k>=D. On 1+J, the p^k-th power is1. If J=0 this group is trivial and no correction is needed. Otherwise choose v with mv=1 mod p^k. Set

    c=(1+b)^v - 1 in J.

All solutions of x^(p^s m)=a have the form

    x=r(1+j),    r=(r_i) in S*,    F^s(j)=c in J.

Proof: x=r(1+j) is the unique decomposition into S* and1+J; commuting factors separate the two equations. The m-th power is an automorphism of1+J with inverse v. In characteristic p, (1+j)^(p^s)=1+F^s(j). Thus the remaining equation is exactly the displayed F_p-linear system. If it is soluble its full solution set is j_0+ker(F^s|J). The root count is

    p^(dim_Fp ker(F^s|J)) times product_i # {r_i}.

The dimension computation, root representation, and all compatibility maps are explicit. When m=1, the even simpler equation F^s(x)=a is linear on ALL of A, including nonunits, and gives either an empty set or an affine F_p-subspace. These observations close both the pure inseparable case and the arbitrary-unit case. They do not treat a nonunit with a nontrivial prime-to-p exponent.

## 7. What the stronger local-root primary already supplies

Berthomieu–Lecerf–Quintin, acquired author-hosted file BerLecQui2013.pdf, is actually HAL-00642075 v1 dated17November2011. It treats complete commutative Noetherian unramified REGULAR local domains R, with roots modulo powers of the maximal ideal. Its Lemmas5–8, Proposition9, Algorithm1 and Proposition10 prove a root-class recursion. Lemma6 bounds the sum of multiplicities by polynomial degree; Proposition9 bounds the number of root classes. Theorem19, Lemma20 and Corollaries21–24 identify the actual remaining coefficient-ring operations. For F_q[[t]] and Galois rings the finite-field subroutines can be supplied by section3 and inverse Frobenius. Thus neither arbitrary precision nor singular roots in a truncated one-parameter regular ring is an unpaid operation here. The faster quasi-homogeneous algorithms were not read in full; the slower complete algorithm already suffices for this comparison.

The proof uses a valuation induced from a regular local domain and homogeneous computations in an integral polynomial ring. An arbitrary multiplication law on J/J^2 -> J^2 is not the associated graded polynomial algebra used there. Presenting an arbitrary finite local algebra as a quotient of a power series ring does not turn its defining ideal into a power of the maximal ideal. This observation only delimits applicability; it does not establish novelty by a theorem-title mismatch.

Chakrabarti–Dwivedi–Saxena's2024 primary Theorem1 was read through web PDF extraction, with its final complexity proof at PDFp16. It treats n-variate systems over a Galois ring with runtime polynomial in d^c_(nk),m,deg(phi)log p, where c_(nk)<=(nk)^(O((nk)^2)); it is efficient for fixed n+k. The proof builds a tree of ideals, performs Groebner arithmetic, then invokes finite-field point finding; small fields use exhaustive search. Thus it is an actual stronger systematic treatment of singular lifting, but not a dimension-uniform solution to arbitrary quadratic systems. The appendices and invoked Huang–Wong proof were NOT read in full, and two direct downloads returned503, so no authenticated local PDF identity or full transitive-coverage claim is made. No new derandomization or sharper complexity statement is inferred from this incomplete read.

## 8. A precise singular quadratic encoding

For an odd prime p, let V,W be finite-dimensional F_p-vector spaces and beta:V x V->W any symmetric bilinear map. Define

    A=F_p directsum V directsum W,
    (c,v,w)(d,u,z)=(cd,cu+dv,cz+dw+beta(v,u)).

This is commutative, associative, and unital. For a third element (e,t,h), associativity follows by expanding: the W component of either triple product is cd h+ce z+de w+c beta(u,t)+d beta(v,t)+e beta(v,u). Equivalently all triple products of elements of V directsum W vanish, so associativity on the radical is automatic and scalar compatibility does the rest. The ideal J=V directsum W has J^3=0 and quotient F_p; every element outside it is a unit by a finite geometric series. Hence J is exactly the radical.

For a=(0,0,a_W), one has

    (c,v,w)^2=(c^2,2cv,2cw+beta(v,v)).

Thus x^2=a is equivalent to c=0 and beta(v,v)=a_W, with w arbitrary. The residue root is uniquely0. Because p is odd, every list of homogeneous quadrics Q_1,...,Q_h on V is beta(v,v) for a computable symmetric beta: diagonal coefficients are unchanged, and off-diagonal multiplication coefficients are half the cross coefficients. Consequently simultaneous quadratic equations are literally a single nonunit square-root equation in an explicit local algebra with J^3=0. This is a classical algebraization, not an inference from a failed Newton step.

For specificity the reduction can preserve a counting identity from any3-CNF formula with n variables and c clauses over F_3. Use V-coordinates t,x_1,...,x_n,y_1,...,y_c. For each literal put its truth form L equal to x_i (positive) or t-x_i (negative), and its false form U=t-L. Define the homogeneous quadratic list

    Q_0=t^2;
    Q_i=x_i^2-t x_i                     (1<=i<=n);
    Q_(n+2j-1)=U_(j,1) U_(j,2)-t y_j;
    Q_(n+2j)=y_j U_(j,3)                 (1<=j<=c).

Let W=F_3^(1+n+2c) and a_W=(1,0,...,0). Then Q(v)=a_W forces t=+1 or-1. Divide all other V-coordinates by t. Each x_i/t is0 or1; y_j/t is uniquely the product of the first two false indicators; the last equation says the clause is satisfied. Conversely every satisfying assignment gives exactly one solution for each t. Therefore the full root count in A is

    # {x in A:x^2=a}=2 * 3^(1+n+2c) * #SAT(formula).

A has dimension 3+2n+3c, its multiplication table is polynomial-size in the formula, its characteristic and root degree are fixed(3 and2), a is nonzero and square-zero, and J^2 is nonzero since Q_0=t^2 occurs. We do not require W=J^2 or claim a belongs to J^2 for every unsatisfiable instance. That extra condition is unnecessary for the displayed reduction. All roots are singular because their scalar parts are0.

This proves a direct search/decision/counting reduction, not just an experiment. Using the familiar NP-completeness of3SAT would give the corresponding complexity consequence. A full original Cook/Karp transitive literature audit and an exhaustive search for precisely this ring-root encoding were NOT completed; no new-to-literature hardness theorem is nominated. The encoding is a routine symmetric-bilinear realization of quadratic equations and is independent of the pinned factorization input. Combining two routine reductions does not itself supply the campaign's missing substantial operation.

## 9. Why componentwise linear lifting does not finish it

For J^3=0, choose a vector-space section V of J/J^2 and W=J^2 (or use the explicitly graded construction above). Around a residue root r, Taylor's exact truncated identity is

    f(r+v+w)=f(r)+f'(r)(v+w)+f^[2](r) v^2,

where f^[2] is the second Hasse derivative; this avoids division by2 in a general characteristic. If the residue derivative is zero, its nilpotent part times v can still give a nonzero linear term in W, while the quadratic term can retain all products among V-coordinates. The lifting equation is then a vector-valued quadratic system. Computing its linear tangent space, or solving one layer for each fixed v, does not choose a globally soluble v. Section8 exhibits the entire coupling even for f=T^2-a, fixed p and unique residue root.

One could record a polynomial-size arithmetic circuit for this quadratic system. That is an exact description of the root set but does not find a point, count points, or give a small union of affine classes. Calling this a compressed root solver would just rename the original problem. Conversely the general root problem is decidable by enumeration; no impossibility or absolute exponential lower bound is claimed. The comparison gives no finite-field factoring contradiction.

## 10. Original project overlap and limits

Actual original i104 lines178–205 constructs connected symmetric finite-field algebra forms with different Frobenius cycles; i108 lines73–91 includes its trace/radical explanation and finite-field tensor-factor interpretation; i110 lines190–215 contains the nontrivial Brauer-local-point pairing and its residual trivial-point limitation. These retain all original quantifiers. Their shared ingredients are nilpotent radicals, separable residue factors, Frobenius and primitive idempotents. The present commutative explicit root calculation does not produce a Morita equivalence, a group-block realization, a global/weight comparison, or any missing cancellation. Reading these bodies does not clear the rest of their archives. The i108 range also exposed unrelated A5 arithmetic context, which is unused.

The required five r124 originals were read separately as direct exceptions. None of the norm-torus, quaternion/spinor, metric or other excluded active mathematics supplies a premise. Broad history results were partial and coarse; the known derivative/summary admissions, output truncations, and source-read limitations are detailed in READING.md. No exhaustive-history, perfect-isolation, global-priority, or family-exhaustion certificate is made.

## 11. Research disposition

The integrated paid reduction is stronger than 'factor first and try Hensel': it gives the canonical coefficient algebra, prime-field-only component splitting, arbitrary explicit extension-field factorization, all simple roots, the entire square-zero case, pure Frobenius equations, and all unit powers with exactly stated representation costs. Classical regular-local root-class recursion already handles substantial singular cases too. These are not proposed as substantial findings.

The remaining nonunit singular operation in arbitrary finite commutative algebras contains the explicit quadratic system of section8. No dimension-uniform algorithm, new special-class classification with a nonroutine operation, or substantial source-dependent construction was closed. The quadratic encoding itself is a routine diagnostic; an uncomputed general solver and an uncompleted priority audit are not findings. Therefore the result remains PREFREEZE/no nominee. No theorem freeze, full author-proof candidate, independent correctness/contribution verdict, acceptance or count is assigned. All old scopes, proofs and dispositions stay unchanged, and parent alone integrates and reviews.
