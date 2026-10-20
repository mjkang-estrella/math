# Commuting quadratic rows and the auxiliary division degree

**PREFREEZE / no nominee.** This is an author research derivation, not an independent correctness or contribution grade. The operation investigated is optimal auxiliary degree for the **full** family200 triangular construction. The results below are supporting obstructions and a compatible single-row construction. They do not determine that optimum and are not submitted as the remaining campaign acceptance.

## 1. Exact interface and research question

Fix the stipulated source pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. For a regular sequence of quadrics f_1,...,f_n in C[x_1,...,x_n], the companion *Commuting Division-Coefficient Forms* (Theorem1.1, `thm:construction`) supplies a finitely generated extension k/C, a central division k-algebra D of degree r, and a commutative graded algebra

    k[x] ⊆ A ⊆ D[x],

which is generated over k by commuting degree-one forms and is finite over k[x]. There are t_1,...,t_n in A_1 such that

    t_i² = c_i f_i + Σ_(h<i) b_ih f_h + Σ_(j>i) C_ij t_j,       (1)
    c_i ∈ k*, b_ih ∈ k, C_ij ∈ A_1,

and the unrestricted ordered monomials in the t_i are a left-D basis of D[x]. In particular the t_i are left-D linearly independent. Degree-zero coefficients are scalar because A is generated over k in degree one. None of these operative source properties is audited or weakened here.

The exploratory question U106 is: for **every ordered regular triple** f=(f_1,f_2,f_3) of complex ternary quadrics whose span contains no nonzero square after any field extension, determine the minimum r among **all** tuples (k,D,A,t,c,b,C) satisfying this full interface, with matching constructions and lower bounds. The ordering, arbitrary field extension allowed by the source, all multipliers, full ordered basis, and actual center of D are retained. No constant answer, including r=4, has been proved or frozen. U106 was never a proof-feasible nominee. It is not a substitute for older relative-Tor C, U105, or an old frozen target.

Put W=span_C{f_i}. Say W is geometrically square-free in degree two if W_E contains no nonzero scalar multiple of l² for any extension E/C and nonzero l∈E[x]_1. This terminology here concerns the **linear space of quadrics**, not squarefree polynomial factorization. Equivalently P(W) misses the rank-one Veronese locus. Its emptiness over the algebraically closed base implies emptiness after every field extension. The familiar no-square ternary examples and this geometric condition are already present in I226; they are not new examples of this round.

## 2. Degree-one centralizers in a quaternion algebra

Let k have characteristic different from2, let Q=(a,b)_k be a quaternion division algebra, and use basis1,i,j,ij with i²=a, j²=b, ij=-ji. Write a homogeneous linear pencil as

    t=l + i p + j q + ij s,    l,p,q,s∈k[x]_1.

The pure part u=i p+j q+ij s has scalar square. If t is noncentral and t² is scalar, then l=0: the pure part of t² is 2lu, and a nonzero scalar polynomial cannot annihilate u. This also follows from the reduced characteristic polynomial.

Suppose the span of p,q,s has dimension at least2. Then

    {v∈Q[x]_1 : vt=tv} = k[x]_1 ⊕ k u.                       (2)

Here t and u have the same centralizer, even when l is nonzero. To prove (2), write v=m+i p'+j q'+ij s'. The commutator formulas in the displayed quaternion basis show that [u,v]=0 is exactly the vanishing of the three two-by-two minors of (p,q,s) and (p',q',s'). The factors2,a,b are invertible. Over K=k(x), the second vector is h times the first for some h∈K. At least two of p,q,s are independent linear polynomials; their greatest common divisor in k[x] is1. Write h=A/B in coprime form. Since all h p,h q,h s are polynomials, B divides each nonzero coordinate, hence B is a unit. Homogeneity forces h∈k. The reverse inclusion is immediate.

For completeness, if the pure-coordinate span has dimension1, then u=e l_0 for a fixed nonzero pure quaternion e and a scalar linear l_0. Its centralizer in degree one is k[x]_1⊕e k[x]_1, of dimension2n. If u=0 it is all Q[x]_1, of dimension4n. These alternatives explain why the rank hypothesis in (2) cannot be dropped. If t² is scalar and t is in the span-one case, t²=e² l_0² is a nonzero scalar multiple of a square.

The centralizer operation is classical. Voight, *Quaternion algebras*, v1.0.7u, Corollary4.4.5 and Proposition7.7.8 give its field-level form and proof. The coprime-coordinate argument simply identifies its homogeneous degree-one part. No claim to invent quaternion centralizers is made.

## 3. The last two rows exclude quaternion coefficients

**Supporting assertion.** For every n≥2 and every regular sequence of complex quadrics whose W is geometrically square-free in degree two, every full source tuple (1) has even degree r≥4.

First exclude r=2. In that case D is quaternion. The final row gives

    t_n²=q_n∈W_k,    q_n≠0.                                  (3)

The nonzero assertion follows from division and t_n≠0. The pencil cannot be scalar or have a one-dimensional pure-coordinate span: either would put a scalar square in W_k. Thus t_n is pure with pure-coordinate span at least2. Formula(2) applies to **every** element of A_1, including the multipliers, because A is commutative.

For the penultimate row write

    t_(n-1)=l+αt_n,    C_(n-1,n)=m+βt_n,
    l,m∈k[x]_1, α,β∈k.

Let q_(n-1)=c_(n-1)f_(n-1)+Σ_(h<n-1)b_(n-1,h)f_h. Substitution in that row gives

    l²+2αl t_n+α²q_n = q_(n-1)+m t_n+βq_n.

Scalar and pure-quaternion parts are independent. Therefore

    m=2αl,    l²=q_(n-1)+(β-α²)q_n∈W_k.                     (4)

The scalar linear form l is nonzero, since otherwise t_(n-1)=αt_n violates left-D linear independence. Equation(4) contradicts the assumed absence of scalar squares. This excludes quaternion coefficients for the full source interface, including all choices of A and all multipliers; it is not merely an obstruction to a preferred choice of generators.

The exclusion of odd r is already a classical part of the final-row reduction. Extend the center to K=k(x). The algebra D_K is still division: D[x] is a domain by its leading-term rule, central localization is a domain, and a finite-dimensional domain over K is division. A rank-at-least-two homogeneous quadric q_n is not a square in K (unique factorization reduces a rational square to a polynomial square). Thus K[t_n] is a quadratic field in D_K. It lies in a maximal subfield, whose degree over K is r by the double-centralizer theorem; hence2 divides r. Degree1 is also excluded directly by (3). Together these facts give r≥4. No assertion that4 divides every possible r is made.

I226 already supplies the stronger bound 2^floor(rho/2) dividing r when every nonzero quadric in W has rank at least rho. The present two-row argument adds information when that bound allows r=2. It does not improve its large-n asymptotic estimate and does not regrade I226.

## 4. The final row really can be quaternion in three variables

The preceding incompatibility is not justified by failure of a guessed construction. A strongest known reduction actually supplies the last row at degree2.

For any regular triple of ternary quadrics over C, introduce independent z_1,z_2,z_3 and put K=C(z_1,z_2,z_3), q=Σz_i f_i. Eisenbud–Peeva–Schreyer, *Quadratic complete intersections* (Journal of Algebra571,2021), Theorem2.1 proves that the full Clifford algebra Cl_K(q) is division. Its operative proof identifies the polynomial Clifford order with the quadratic dual of the complete intersection, uses the finite linear resolution, and localizes; it also treats extra generators by specialization. This is an existing construction, not an unproved generic-division assumption.

The generic ternary q is nondegenerate. One way to see this is that the base-point-free system W on P² has a smooth general member in characteristic zero. Alternatively, division of the full Clifford algebra excludes a radical vector, whose square would be zero. In odd dimension3, the usual diagonal Clifford basis shows that its center is K plus the volume element, a quadratic extension: the volume cannot become scalar since the eight Clifford basis monomials remain independent. It is a field because the algebra is division. Denote this center by k. Then

    dim_K Cl_K(q)=8, [k:K]=2, dim_k Cl_K(q)=4.

The algebra D=Cl_K(q), regarded over its **actual** center k, is therefore quaternion. Its universal degree-one pencil t has t²=q, with nonzero f_3 coefficient z_3. The center is finitely generated over C. For geometrically no-square W, §3 proves that this legitimate final row cannot be completed to the full ordered triangular system inside any quaternion division algebra. Calling the dimension8 over K a central degree would be wrong; the center change is essential.

This does not construct A,t_1,t_2 or the full ordered basis. It is a comparison between a paid single-row construction and a separate compatibility obstruction. Neither piece determines the minimum for U106.

## 5. Why two independent quaternion roots still do not finish the construction

A stronger attempted composition was to use separate Clifford roots in two quaternion factors. Its exact limitation can also be proved.

Let Q_1,Q_2 be quaternion division k-algebras and suppose D=Q_1⊗_k Q_2 is division. Let u∈(Q_1)_0⊗k[x]_1 and v∈(Q_2)_0⊗k[x]_1 be pure pencils, embedded in their separate factors, each having pure-coordinate span at least2. Then

    {w∈D[x]_1:[w,u]=[w,v]=0}=k[x]_1 ⊕ k u ⊕ k v.             (5)

Indeed over K=k(x), each quaternion centralizer has basis1,u or1,v. Taking kernels of the two commutator maps over the field, and tensoring the factors, gives joint centralizer with basis1,u,v,uv. Write w=L+A u+B v+C uv with rational scalar coefficients. The scalar-scalar component forces L to be a polynomial linear form. The pure-scalar and scalar-pure components, by the coprimality argument of §2, force A,B∈k. The mixed pure-pure component has coordinates C p_i q_j. Each family of nonzero coordinate linear forms has gcd1, so their pairwise products also have gcd1. The denominator of C must therefore be a unit. But degree1 requires C homogeneous of degree-1; hence C=0. This proves(5).

Suppose n≥3 and a full tuple(1) has its final two distinguished forms t_n=u and t_(n-1)=v in such separate factors, with u²,v²∈W_k. Every element of A_1 then has the form in(5). Write t_(n-2)=l+αu+βv and do the same for the two multipliers in its row. Projection D=k⊕(Q_1)_0⊕(Q_2)_0⊕((Q_1)_0⊗(Q_2)_0) onto the scalar-scalar component shows

    l²∈W_k,

because the other scalar terms are scalar multiples of u² and v². Independence of t_(n-2),u,v forces l≠0. Thus this entire separated-root construction is incompatible with a no-square W.

This is **not** an obstruction to every degree-four construction. The actual second row may have t_(n-1)²=q_(n-1)+C t_n with a mixed nonconstant C, and its coefficients need not lie in a separate tensor factor. The enlarged commuting degree-one space in the source is explicitly permitted. No argument here conjugates arbitrary data into the separated form while preserving the rows, the center, division, and the ordered basis. That is exactly where the attempted composition stops.

## 6. Strongest source construction and remaining operation

The pinned construction already solves unrestricted existence. Its actual binary-addition curve has group order b^b (degree4 for b=2), a genuinely linearized bundle, and commuting multiplication pencils. Assembly substitutes commuting previous inputs into new tensor factors, descends the full relation spaces, and preserves all earlier rows. The index proof controls division by integral Euler characteristics and prime-power truncation. These compatible operations are paid; neither a naive matrix shortcut nor the separated-root failure challenges them.

At b=2, each binary link contributes degree4 and the full assembly uses many links. This gives finite full constructions, not a matching degree4 construction for U106. Reducing the number of links, replacing their division algebra by a smaller one, or replacing the formal degree-one space requires new compatibility arguments. The proof's module-divisibility conclusion cannot simply be applied to a proposed smaller algebra.

The precise missing operation is a full optimal construction and lower bound, for every original ordered no-square ternary regular triple, retaining all source tuples in the minimization. No mixed degree-four construction, exclusion of every mixed degree-four construction, or determination of the minimum at higher degrees has been obtained. Even a claimed lower divisibility4 for arbitrary r would require an argument beyond §3. Splitting an odd factor may replace a division algebra by a matrix algebra and lose the original coefficient action; it is not such an argument.

The closed supporting proofs above use classical quaternion centralizers, elementary polynomial divisibility, the source's exact row interface, and the existing generic Clifford theorem. Their project-local derivation is not a substantial-contribution verdict. The research therefore ends **PREFREEZE/no nominee**, without freezing U106 or relabelling these method obstructions as its solution. No worldwide priority, current-open or exhaustion assertion is made.

The eight finite centralizer checks in diagnostic.py only check the displayed rational linear algebra. The Hamilton tensor diagnostic is split and is explicitly **not** a division witness. The general supporting proofs do not depend on those computations. All prior accepted, technical and unresolved scopes remain unchanged.
