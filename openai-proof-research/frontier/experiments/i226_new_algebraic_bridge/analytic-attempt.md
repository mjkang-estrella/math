# I226 analytic work — initial target and first calculation

All pinned OpenAI inputs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are accepted. This file records new deductions, not an audit.

## Target selected before a broad literature survey

Family 200: strengthen the characteristic-zero lex-plus-powers (LPP) Betti inequality to a consecutive-cancellation statement. If S=F[x_1,...,x_n], I contains a homogeneous regular sequence of degrees 2<=a_1<=...<=a_n, and J is its prescribed LPP ideal, seek nonnegative **integers** c_{p,j}, with c_{0,j}=c_{n+1,j}=0, such that

    beta_{p,j}(S/J)-beta_{p,j}(S/I)=c_{p,j}+c_{p+1,j}.

Thus c_{p,j} cancels one pair in homological positions p-1,p at fixed internal degree j. This is stronger than entrywise domination. The initial scope is full-length sequences over C; field descent and shorter sequences require separate justification. No substantial-finding status is attached to this target: a standard filtered-complex consequence does not meet the contribution gate.

## Early partial mathematics: the exact obstruction to naive division

For finite complexes C and gr(C) with equal dimensions in each position, write r_p=rank(d:C_p->C_{p-1}) and r_p^0=rank(gr(d)). Then

    dim H_p(gr C)-dim H_p(C)=(r_p-r_p^0)+(r_{p+1}-r_{p+1}^0).

The filtration gives r_p>=r_p^0. Applied to the accepted division-coefficient construction, the two homology dimensions are m times the desired Betti numbers, m=dim_k Delta. Dividing arbitrary nonnegative integers by m is NOT justified. The candidate repair is that the differential, the filtration, and its associated graded are all left-Delta-linear: the variable action is right multiplication by the commuting t_i. Therefore every rank is a multiple of m. This needs to be checked at the Koszul-complex level, not merely asserted from the terminal Betti numbers.

## Two different planned routes

1. Division-linear filtered Koszul ranks, then the already-existing pure-powers cancellation theorem of Mermin–Murai. This is likely to yield a paid technical theorem but may be a standard transfer.
2. A direct commutative degeneration/marked-basis construction to an ideal containing the powers. Unlike Route 1, this would construct actual scalar ideals rather than a module with division coefficients. Actively test the necessary pure-power initial-ideal assertion; it may be false even for smooth complete intersections.

Only the listed I226 paths will be written. No research code, numerical experiment, or additional agent is used.

## Route 2 develops a size obstruction (working calculation)

A stronger issue than the scalar case is whether the division-algebra auxiliary size could be bounded uniformly in the number of quadratic equations. Let W be the span of n quadrics over C, and let rho(W) be the minimum matrix rank of a nonzero quadric in W. Suppose Delta is central division of degree r over an extension k/C, and a nonzero linear form t in Delta[x] satisfies t^2 in Delta tensor W. After splitting Delta over an algebraic closure K of k, t becomes an r by r matrix T of linear forms.

Because Delta[x] has no zero divisors, T^2 is not the zero matrix. After a constant change of matrix basis, one diagonal entry of T^2 is nonzero. Indeed a nonzero endomorphism B has vectors u and v with v(u)=1 and v(Bu) nonzero; apply this to a nonzero coefficient B of T^2 and complete u to a basis whose first dual vector is v. The resulting nonzero quadric is

    q = T_11^2 + sum_{a=2}^r T_1a T_a1 in W_K.

Hence rank(q) <= 1+2(r-1)=2r-1. Therefore

    rho(W) <= 2r-1,   r >= ceil((rho(W)+1)/2).

This uses only the final quadratic row of the pinned triangular construction; it imposes no extra commutativity on individual division coefficients. It is an obstruction to SMALL auxiliary division algebras, not to the accepted existence theorem.

For a generic n-dimensional system of quadrics in n variables, let k_n be the least positive integer with k_n(k_n+1)/2 >= n. The symmetric determinantal variety of quadrics of rank <= n-k_n has codimension k_n(k_n+1)/2. A generic projective (n-1)-plane misses it, so rho(W)>=n-k_n+1. Intersect with the nonempty open complete-intersection locus. Thus the degree r of every pinned-style division construction for such a system must obey

    r >= ceil((n-k_n+2)/2),   dim_k Delta >= ceil((n-k_n+2)/2)^2.

The incidence dimension count, base extension, nonzero diagonal assertion, and source overlap still need a complete written check. This is a uniform obstruction to a proposed bounded-size construction. Its quantitative order is quadratic in n for division dimension. No significance or novelty claim is inferred from a search miss.

## Route 2, final strengthening: a Clifford divisibility obstruction

The elementary corner bound above is valid but substantially weaker than the following. This supersedes it as the strongest mathematical output. The core centrality step must not be omitted.

### Theorem Q226 (all square identities, including specialized coefficients)

Let F0 be a characteristic-zero field, and let f_1,...,f_c be a regular sequence of quadrics in F0[x_1,...,x_n]. Write W=span_{F0}{f_1,...,f_c}. Suppose the geometric minimum rank of W is at least rho: for every field extension E/F0 and every nonzero (b_1,...,b_c) in E^c, the symmetric matrix of sum b_j f_j has rank at least rho.

For every extension k/F0, every finite-dimensional central division k-algebra Delta of degree r (so dim_k Delta=r^2), every nonzero linear form t=sum_i A_i x_i in Delta[x], and every B_1,...,B_c in Delta satisfying

    t^2 = sum_j B_j f_j,                                             (Q1)

there is an integer s>=rho for which

    2^{floor(s/2)} divides r.                                        (Q2)

In particular 2^{floor(rho/2)} divides r, and dim_k Delta >= 4^{floor(rho/2)}. No genericity is assumed on the B_j. They need not be central in Delta. The theorem needs no other rows of the pinned construction and no commutation between different t_i.

### Proof

1. **No linear syzygies.** Flat extension preserves the regular sequence. Its Koszul complex over k[x] is exact. Consequently a relation sum_j l_j f_j=0 with all l_j linear has all l_j=0: the first Koszul syzygies have coefficients of degree two, so the syzygy module has no degree-three element. This remains true with coefficients in the k-vector space Delta, by expanding in a k-basis. This use of Koszul exactness is about an ordinary polynomial regular sequence; it does not audit any upstream statement.

2. **Central coefficients inside the generated algebra.** Since t commutes with t^2, (Q1) gives sum_j [t,B_j] f_j=0. The coefficients [t,B_j] are linear forms. Step 1 forces [A_i,B_j]=0 for every i,j. The f_j are linearly independent. Choose linear functionals on k[x]_2 dual to them; applying such a functional to (Q1) expresses each B_j as a k-linear combination of products A_i A_l. Therefore every B_j belongs to the finite-dimensional k-subalgebra D generated by the A_i and commutes with all of D. In particular the B_j commute with each other.

The commutative algebra F=k[B_1,...,B_c] is a finite-dimensional domain, since it lies in Delta, and is therefore a field. It is a finite extension of k, it centralizes all A_i, and q=sum_j B_j f_j is a quadratic form over F. The central polynomial algebra over a division algebra is a domain, as seen from the leading term in any monomial order. Hence t^2 is nonzero, q is nonzero, and s=rank_F(q)>=rho.

3. **Anticommuting units.** Diagonalize q over F. On its nondegenerate part it is sum_{i=1}^s d_i z_i^2, with d_i in F^*. Express t in these coordinates; denote the corresponding coefficients by u_i. Comparison in t^2=q gives

    u_i^2=d_i,          u_i u_j=-u_j u_i  (i!=j).                     (Q3)

Each u_i is invertible in Delta. Elements of F commute with all the u_i. No extraction of square roots is necessary.

4. **Exact dimension divisibility.** For I subset {1,...,s}, put u_I in increasing index order. Conjugation by u_i acts on this product with eigenvalue

    (-1)^{|I|-1_{i in I}}.

These conjugation operators commute on the F-span of the products. If s is even, their joint eigenvalue strings are distinct for all 2^s subsets. Indeed equality for I,J implies all indicators of I symmetric-difference J equal its cardinality modulo two, forcing that set empty when s is even. If s is odd, the strings are distinct on the 2^{s-1} even-cardinality subsets, since the only other possible symmetric difference is the whole odd set. Distinct joint eigenvectors of commuting involutions in characteristic zero are independent; this follows also by applying their explicit projectors product_i (1+epsilon_i Ad(u_i))/2. The products are nonzero since the u_i are units.

For even s let H be the F-span of all products. For odd s let H be the F-span of the even products. Relations (Q3) make H a unital subalgebra. Its F-dimension is 2^{2 floor(s/2)}. It lies in Delta, hence has no zero divisors, and being finite-dimensional over F it is a division algebra. Delta is a finite-dimensional left H-vector space, even though H need not be central in Delta. Taking dimensions gives

    r^2 = dim_k Delta
        = dim_H(Delta) [F:k] 2^{2 floor(s/2)}.

Thus 2^{2 floor(s/2)} divides r^2. Taking the 2-adic valuation proves (Q2). This is a divisibility assertion, not merely an inequality. QED.

### Corollary G226 (generic EGH auxiliary size)

For n>=1 let k_n=min{k>=1:k(k+1)/2>=n}, and set rho_n=n-k_n+1. There is a nonempty Zariski-open set U_n of ordered n-tuples of complex quadrics in n variables such that every tuple in U_n is a regular sequence, and for every extension k/C and every pinned-style commuting-form construction for that tuple, the auxiliary central division algebra has degree r satisfying

    2^{floor(rho_n/2)} divides r,
    dim_k Delta >= 4^{floor(rho_n/2)}.                               (G1)

Thus the auxiliary dimension for these inputs is at least 2^{n-O(sqrt(n))}. This rules out any polynomial-in-n or n-independent dimension bound for all quadratic inputs within that construction format. It says nothing about the complexity of all conceivable EGH proofs.

**Proof of the open-set assertion.** Put N=n(n+1)/2. In P(Sym^2 C^n), the rank-at-most n-k locus has codimension k(k+1)/2. One can derive its dimension by choosing the k-dimensional kernel (dimension k(n-k)) and then a nondegenerate quadratic form on the quotient (dimension (n-k)(n-k+1)/2-1); the rank-exactly stratum is dense in the rank-at-most locus. If this locus is empty (n=k), the avoidance statement below is immediate.

The Grassmannian of n-dimensional vector subspaces W in C^N has dimension n(N-n). For a fixed projective point [q], those W containing it have dimension (n-1)(N-n). The incidence of W meeting the rank-at-most n-k_n locus therefore has dimension at most

    N-1-k_n(k_n+1)/2 + (n-1)(N-n)
      <= n(N-n)-1.

Its projection is closed, since the incidence is projective. Its complement is thus nonempty open. Every W in this complement has geometric minimum rank at least rho_n. The property persists under arbitrary field extension because its excluded projective intersection is empty as a scheme.

The locus where n quadrics have no projective common zero is also nonempty open: the bad incidence projects properly, and the span of x_1^2,...,x_n^2 is a good example. On this locus the ideal is maximal-ideal-primary of height n; n generators in the Cohen-Macaulay polynomial ring form a regular sequence. The Grassmannian is irreducible, so intersecting these two nonempty open sets is nonempty. Pull back to the space of ordered bases to obtain U_n.

For any tuple there, the final row of pinned Theorem 1.1 has a_n=2 and no later t_l. Its degree-zero multipliers belong to Delta and it reads exactly (Q1). The full ordered-basis property implies t_n is nonzero. Apply Q226. QED.

### Counterexample attempts and scope checks

* Replacing "division" by "matrix algebra" destroys Q226: t=x_1 E_12 is nonzero but has square zero, so satisfies (Q1) with all B_j=0 for every W. The nonzero-q step is indispensable.
* Removing the regular-sequence condition destroys the centrality mechanism. In M_2(F0), choose A=diag(1,2) and B=[[0,1],[1,0]], t=Ax+By, and W=span{x^2,xy,y^2}. The coefficients A^2,AB+BA,B^2 need not commute with A and B; W is not a regular sequence in two variables. This example only tests the centrality step, not the division conclusion.
* A common tempting use of the generic Clifford algebra is invalid here: the specialized B_j need not be algebraically independent. Q226 avoids that assumption by using the actual rank s of q over F.
* No uniform lower bound applies to every quadratic regular sequence. For f_i=x_i^2 the scalar construction t_i=x_i has r=1. The geometric minimum rank is 1 and Q226 gives exactly no nontrivial divisibility.
* The lower bound is not claimed sharp. There is no matching upper bound, no explicit tuple in U_n for arbitrary n, and no theorem that an arbitrary EGH proof requires this resource. The finite-open-set construction is an existence proof, not a numerical experiment.

### Primary-art limitation

The central algebra here is a specialization of the familiar Clifford algebra attached to a quadratic complete intersection. Eisenbud–Peeva–Schreyer (2021), Theorem 2.1 and its proof, already establish division for the Clifford algebra of a *generic* linear combination and derive large matrix-factorization bounds; Hu–Mori (2023), Definition 1.5 and Theorem 1.9, explicitly develop the quadratic-dual/Clifford correspondence. The proof above makes the specialized-coefficient and auxiliary-EGH-size interfaces explicit, but cannot honestly be presented as discovery of the Clifford bridge itself. A search miss does not establish priority for (Q2) or (G1). Contribution status is reserved to the final report.

## Route 1, completed: consecutive cancellation (technical consequence)

### Theorem C226

For every characteristic-zero field F, every S=F[x_1,...,x_n], every homogeneous proper ideal I containing a homogeneous regular sequence of length 1<=c<=n and degrees 2<=a_1<=...<=a_c, and the LPP ideal J prescribed by the pinned theorem, there are nonnegative integers c_{p,j}, supported in finitely many pairs (p,j), such that

    beta^S_{p,j}(S/J)-beta^S_{p,j}(S/I)=c_{p,j}+c_{p+1,j}
    (0<=p<=n, j in Z),    c_{0,j}=c_{n+1,j}=0.                       (C1)

Thus the quotient Betti table of I is obtained from that of J by adjacent homological cancellations at the same internal degree. If I=S both quotients are zero and the same statement holds trivially. This statement does not construct a scalar flat family of ideals or a degeneration of algebra structures.

### Full-length proof over C

Use the accepted construction and notation of pinned Proposition 4.2: a field k/C, a central division algebra Delta of k-dimension m, the right polynomial action T=k[y_1,...,y_n] on N=Delta[x] given by right multiplication by t_i, Q=N/IN, and a monomial ideal M containing the powers. The accepted Lemma 4.1 gives beta^T(Q)=m beta^S(S/I). Its leading-coefficient construction gives gr Q=Delta tensor_k T/M and hence beta^T(gr Q)=m beta^S(S/M).

Fix an internal degree j. The finite filtration on the Koszul complex K(Q)_j described in Proposition 3.3 is left-Delta-linear: the coefficient subspaces are left ideals, and its differential is right multiplication by t_i. Associativity gives a(t_i action on v)=(t_i action on av); no commutativity of individual Delta-coefficients is used. Its associated graded complex is exactly K(gr Q)_j. Let R_p and R_p^0 denote ranks over the division ring Delta of its pth differential and of the associated graded differential. Filtering kernels, as in the accepted rank comparison, gives R_p>=R_p^0. Define d_{p,j}=R_p-R_p^0, a nonnegative integer. Equality of term dimensions and the elementary homology-rank formula give

    m[beta_{p,j}(S/M)-beta_{p,j}(S/I)]
       = m[d_{p,j}+d_{p+1,j}].

The division by m is legitimate because ranks were computed over Delta, not because arbitrary k-ranks happen to have a divisible sum. This proves cancellation from M to I. Mermin–Murai, Theorem 9.2 (with quotient indexing shifted by one), supplies cancellation from J to M. Add the two nonnegative cancellation arrays to obtain (C1). Their theorem is a prior-art input; it is not claimed as new here.

### Shorter sequences

Choose n-c linear forms that extend the regular sequence to a homogeneous system of parameters; over the infinite field C they exist by avoiding the finitely many relevant associated primes at each step. Powers of a regular sequence remain regular. For any D>a_c put

    I_D=I+(l_{c+1}^D,...,l_n^D).

It contains a full regular sequence with degree list (a_1,...,a_c,D,...,D). For a fixed j choose also D>max(j,0). The degree-e pieces of I_D and I agree for e<D. The LPP prescriptions J_D and J agree there as well, since the newly prescribed powers all have degree D. Their degree-j Koszul complexes therefore coincide with those of I and J, respectively. The full-length conclusion supplies the desired nonnegative cancellation coefficients for this j.

There is no compatibility issue among different choices of D. If delta_{p,j} is the left side of (C1), the coefficients are uniquely recovered by c_{0,j}=0 and c_{p+1,j}=delta_{p,j}-c_{p,j}. Thus they depend only on the two original Betti tables. Outside their finitely many supported internal degrees the recurrence gives zero throughout. This proves the asserted finite support.

### Other characteristic-zero fields

Choose a finitely generated subfield F_1 of F over Q containing coefficients of finite generators of I and of the specified regular sequence. Faithful field extension reflects the exactness of the associated Koszul complex, hence reflects regularity. Embed F_1 in C. Flat field extension preserves graded Koszul homology and Hilbert functions, and the LPP exponent prescription is determined by these Hilbert functions. The two Betti tables over F and C coincide. Apply the result just proved. QED.

### Why this route is not a substantial nomination

C226 is a filtered-complex enhancement of accepted Proposition 3.3/Lemma 4.1 followed by an explicit theorem of Mermin–Murai. The characteristic-zero and shorter-sequence steps are standard field descent and high-degree truncation. The integrality check is necessary, but it does not turn this into a new structural method under the task's contribution threshold.

## Scalar degeneration route: an exact obstruction, already part of known G-quadratic theory

In C[x,y,z] let

    f_1=x^2+yz,   f_2=y^2+xz,   f_3=z^2+xy,   I=(f_1,f_2,f_3).

They have no nonzero common projective zero: multiplying the three equations f_i=0 gives (xyz)^2=-(xyz)^2, hence xyz=0, and the equations then force x=y=z=0. Their ideal has height three, so they form a regular sequence.

No nonzero square (ux+vy+wz)^2 lies in I_2. Comparing square and mixed coefficients would give

    u^2=2vw,   v^2=2uw,   w^2=2uv.

If one variable is zero, they are all zero. Otherwise multiplying gives 1=8, impossible in characteristic zero. This remains true over any extension of C.

For any linear coordinate system and any monomial order, if in(I) were the pure-square ideal then the square of the least variable would be a leading term in degree two. It is the least degree-two monomial, so its homogeneous witnessing polynomial would have to be exactly that square. The preceding calculation rules this out. Hilbert equality forces any initial ideal containing all three prescribed squares to equal the pure-square ideal, so even that weaker initial-ideal assertion fails. In the pinned triangular construction with Delta=k the final row would similarly force a nonzero scalar square in I_2. Thus the scalar replacement fails, while the division-coefficient construction is consistent.

Conca's Theorem 1.1(2) already identifies exactly this no-square complete-intersection class as the exception to G-quadraticity in the relevant small Hilbert function. The example is a diagnostic, not a new obstruction to claim for the literature. It does not disprove arbitrary flat deformations or chains of deformations; only the stated coordinate-change/initial-ideal mechanism is excluded.


## Final source-scope correction and contribution disposition

The pinned theorem places B_{ij} in A_{a_i-a_j}, with A generated over k in degree one. For an all-quadratic sequence this is A_0=k. Thus the final-row coefficients in the actual construction are scalar already. Q226 is a broader statement, but its coefficient-centrality argument is not needed to apply the result to the pinned quadratic construction. G226 is therefore an ordinary scalar Clifford representation bound combined with a determinantal incidence count. This strengthens the reason to regard it as technical rather than the sought tenth substantial finding. No proof claim above depends on the multipliers being genuinely noncentral.

Final verdict: Q226, G226 and C226 are fully paid deductions; no unresolved analytic estimate is disguised as a theorem. No substantial finding is nominated. Source-relative truth is separate from contribution significance, and the latter is not established here. Both independent gates remain with the parent.
