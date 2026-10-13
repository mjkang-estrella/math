# I199: structured Foulkes analytic record

2026-10-12. **UNRESOLVED — NO SUBSTANTIAL NOMINATION.** This record proves the auxiliary assertions below, not the seed target. All corpus theorems and lower operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted. In particular F210's canonical range `b >= (a-1)^2` is paid and is not nominated. Two genuinely different approaches to one exact target are developed: polynomial restrictions of the actual structured annihilator, and multiplication on the actual normalization quotient.

## 1. Conventions, dependencies, and the chosen target

Over C, use normalized averaging to set

    R_b(V) = ((Sym^b V)^(tensor a))^(S_a) = Sym^a(Sym^b V),
    R = direct sum_b R_b,   A = C[R_1] inside R,
    mu_{a,b,V}: Sym^b(Sym^a V) -> R_b,
    C_b = R_b/A_b.

Here C is an A-module, not a quotient ring of R: A is a subalgebra, generally not an ideal. Set m=A_+. The conductor is

    c = Ann_A(C) = {h in A : hR is contained in A}.

The same set is an ideal in R contained in A. One must not multiply arbitrary classes of R/A together.

The quadratic source's §2 proves that C_b* identifies with symmetric a-linear forms T on E=Sym^b V for which

    T(P,...,P)=0 for every P=u_1 ... u_b.                 (D)

Let F(P)=T(P,...,P). In this interpretation F is a degree-a equation on the Chow variety of products of b vectors. The roles of a and b in this equation interpretation are reversed from those in the normalization algebra R. We retain this distinction throughout.

**Target S78.** For every finite-dimensional complex V,

    mu_{7,8,V}: Sym^8(Sym^7 V) -> Sym^7(Sym^8 V)

is surjective, equivalently C_8(V)=0, equivalently every T satisfying (D) for (a,b)=(7,8) is zero.

This target is proposed, not asserted true or globally open. The inspected sources neither establish nor refute it. Its importance is precise: it would prove the complete ordinary seventh case, beyond the accepted sixth case. In the common invariant-tensor realization, transposition of the 7-by-8 array and orthogonal averaging show that the transpose of mu_{7,8} is the opposite canonical map Psi_{7,8} on V*. Hence S78 is equivalent to injectivity of that specified map. Ikenmeyer's Theorem 1.3 propagates such a seed to all b>=9, with b=8 supplied by the seed. Ordinary comparison at b=7 is automatic because both representations coincide. The source's module-generation lemma also gives propagation directly, as proved in §3.1 below.

The target can be tested in V=C^7 without a dimension-dependent loss. Cauchy's formula shows that R_b has only Schur constituents of length <=7. The natural map between these polynomial functors acts on their stable multiplicity spaces; every such Schur functor is nonzero on C^7. Thus vanishing of its cokernel on C^7 implies vanishing in every dimension. This is a reduction, not a rank calculation.

**Paid contracts.** The quadratic paper's §2, `lem:shift` and `prop:vanishing`; the sixth-power paper's `lem:chart`, `lem:polarization`, `cor:module-generation`, `prop:large`; I198 F210; RSW Theorem 2.3, Remark 2.9 and Theorem 3.9; and Ikenmeyer Theorem 1.3 are the relevant inputs. The sixth-power comparison, its rectangular occurrence and leading-monomial lower bounds do not imply injectivity of Psi_{7,8}. Its verification programs are not used or replayed.

## 2. Route A: keep the structured annihilator

Fix T satisfying (D) for (7,8). Every assertion until explicitly marked as a gap is proved below.

### 2.1 The exact first contraction and its limitation

Take Q=y_1 y_2. The polynomial x^6+c t^6 splits into six linear factors over C. Thus (x^6+c t^6)Q is a product of eight vectors. The coefficient of c in (D) gives

    T((x^6 Q)^6,t^6 Q)=0.                              (A1)

Repetition notation denotes slots, not multiplication inside E. Form

    H=T((x^6 y_1 y_2)^6,t^8).

The two operators D_{y_i,t}=y_i dot partial_t give

    D_{y_2,t} D_{y_1,t} H = 8*7 T((x^6 Q)^6,t^6 Q)=0.

Before the first operator the (t,y_1) degrees are (8,6); before the second the (t,y_2) degrees are (7,6). Both strict inequalities are valid, so the source's one-step injectivity, with all other variables as spectators, proves

    T((x^6 Q)^6,t^8)=0 for every decomposable Q.         (A2)

For fixed x,t define a symmetric six-linear form

    S_{x,t}(Q_1,...,Q_6)=T(x^6 Q_1,...,x^6 Q_6,t^8)

on Sym^2 V. Its diagonal vanishes on decomposable quadrics. It is not legitimate to apply a lower canonical-surjectivity theorem here: the lower pair is (6,2), not (6,b>=6), and the accepted ordinary sixth comparison supplies no such assertion.

This failure is substantive. In dimension three, represent a quadratic form Q by its symmetric 3-by-3 coefficient matrix and write Delta(Q)=det(Q). A product of two linear forms has rank at most two, so Delta vanishes on every decomposable Q. Conversely every complex quadratic form of rank at most two factors. The polarization of Delta(Q)^2 is a nonzero symmetric six-linear form on Sym^2 V whose diagonal vanishes on all products. Nonzero follows by evaluating at the identity quadratic form. This is an actual lower annihilator, not just an ambient differential kernel.

It does **not** produce a T satisfying (D) for (7,8). We have not shown that this lower annihilator is compatible with simultaneous variation of x,t and extension to a symmetric seven-linear T obeying all product identities. Conversely we have not excluded such compatibility. Precisely that additional structure would have to replace the failed induction step.

### 2.2 A stronger paid restriction: a determinant square, not just a determinant

**Lemma A.** For every T as above, every ternary subspace W of V and every x in V, the polynomial

    g(x,Q)=F(x^6 Q),  Q in Sym^2 W,

has the form

    g(x,Q)=Delta_W(Q)^2 L(x,Q),                       (A3)

where L is polynomial of degree 42 in x and degree one in Q. Also, for every t in V,

    T((x^6 Q)^6,t^8)=Delta_W(Q) H(x,t,Q),              (A4)

with H of Q-degree three. These identities are simultaneous polynomial identities, not pointwise choices of quotients.

**Proof.** By (A2) and the spanning of Sym^8 V by pure eighth powers,

    dF_{x^6 Q}(R)=7 T((x^6 Q)^6,R)=0

for every R in Sym^8 V whenever Q is decomposable. Consequently g and every Q-partial derivative of g vanish on Delta_W=0. The determinant of a generic symmetric 3-by-3 matrix is irreducible: the rank-at-most-two locus is irreducible, being the image closure of pairs of vectors under symmetrized product, and the determinant has a nonzero derivative at a rank-two matrix. Its hypersurface ideal is therefore (Delta_W), with multiplicity one. Thus g=Delta_W h in C[x,Q]. Differentiation gives

    partial g = (partial Delta_W) h + Delta_W partial h.

For a partial derivative of Delta_W not divisible by Delta_W, primality implies Delta_W divides h. This proves (A3); bidegrees give the degrees of L. Equation (A4) follows directly from (A2), primality, and the Q-degree six of the left side. All conclusions also hold when x=0 by polynomial identity. □

This is a concrete exploitation of the original condition: every candidate degree-seven equation is singular at all forms x^6 Q with Q decomposable. Merely observing that an ambient determinant counterexample fails (D) would not give this assertion.

For V=W of dimension three, the restriction map F -> L is equivariant. Its target is

    (det V*)^4 tensor Sym^42 V* tensor Sym^2 V*.

Indeed Delta(gQ)=(det g)^2 Delta(Q); its square accounts for the determinant twist. Pieri's formula leaves exactly the types

    (48,4,4), (47,5,4), (46,6,4).                       (A5)

The source's chart proof, with a=7,b=8, places every R_8 weight space of tail sum <=8 in A_8. Hence the type (48,4,4) is absent from C_8 and its dual from the candidate equation space. If a candidate has nonzero restriction L, only the other two types in (A5) can contribute to that restriction. This does not assert that either type actually occurs in the kernel. Nor does it describe candidate equations with zero restriction.

### 2.3 Why vanishing on the restricted locus would still be insufficient

Let Z={x^6 Q : x in V, Q in Sym^2 V}, now in V=C^3. The restriction map on *all* degree-seven polynomials on Sym^8 V is not injective.

Here is a written witness. For P in Sym^8 V, its third catalecticant is the contraction map

    Cat_3(P): Sym^3 V* -> Sym^5 V.

For P=x^6 Q, every third derivative is divisible by x^3. Its image lies in x^3 Sym^2 V, of dimension six, so all 7-by-7 minors vanish on Z. At least one such minor is a nonzero degree-seven polynomial: choose distinct scalars t_1,...,t_7 and vectors

    l_i=e_1+t_i e_2+t_i^4 e_3,   P=sum_i l_i^8.

The cubes l_i^3 are linearly independent, because their coordinates contain nonzero multiples of the seven powers t_i^0,...,t_i^6: use the monomials e_1^3, e_1^2 e_2, e_1 e_2^2, e_2^3, e_1^2 e_3, e_1 e_2 e_3, e_2^2 e_3. The fifth powers l_i^5 are also independent: use e_1^(5-j)e_2^j for 0<=j<=5, and e_1^2 e_2^2 e_3 for exponent six. Both are Vandermonde arguments. Cat_3(P) factors through the seven evaluations at l_i followed by the independent l_i^5, up to a nonzero scalar; it has rank seven. Thus some minor is nonzero. No parameter scan or computation was used.

This witness is not asserted to satisfy (D). It only disproves the ambient shortcut “F vanishes on Z, therefore F=0.” The restriction of this map to the actual structured annihilator might be injective, but that is unproved.

### 2.4 All-slot identities retained, and the next failed attempt

There are additional identities, which must not be discarded. If Q_0 is a product of 8-d vectors and W is binary, every member of Q_0 Sym^d W is decomposable. Polarizing (D) therefore gives

    T(Q_0 R_1,...,Q_0 R_7)=0 for R_i in Sym^d W.        (A6)

More generally let P(s)=product_{j=1}^8(u_j+s_j w_j), and P_B=product_{j in B} w_j product_{j not in B} u_j. Coefficients of squarefree monomials in F(P(s)) give, for any nonempty J subset {1,...,8},

    sum_{pi partition of J, |pi|<=7}
        (7)_{|pi|} T((P_B)_{B in pi}, P_empty^(7-|pi|))=0.    (A7)

The falling factorial counts injections of blocks into the seven slots. For |J|=2 this is

    7 T(P_{12},P_empty^6)
      +42 T(P_1,P_2,P_empty^5)=0.

It is a sum identity, not termwise vanishing. Deriving it uses only the original product parametrization and symmetry; it is a paid polarization identity, not a new independence theorem.

An attempted improvement uses the c^2 coefficient of the split sextic to free two slots together. That coefficient gives T((x^6 Q)^5,(t^6 Q)^2)=0. But differentiating an expression with two t^8 slots distributes replacements across both slots: terms in which both copies of a y land in the same slot occur along with the desired terms. For a single directional derivative D applied twice to T(A^5,t^8,t^8), the terms already have the form

    2*8*7 T(A^5,t^6 y^2,t^8)
      +2*8^2 T(A^5,t^7 y,t^7 y).

The binomial identity does not individually kill the first term. All-slot symmetry only equates terms with exchanged slots; it does not remove this distribution. Equations (A6)-(A7) retain relations among them, but no elimination proving their separate vanishing has been obtained. No positivity is available for the complex coefficients of T.

**Route A gap.** Prove that the family S_{x,t}, with the compatibility (A3)-(A7) and the original seven-slot symmetry, is zero, and then control the kernel of the restriction to Z (or find a different full set of restrictions). We have neither a nonzero original T nor a proof that these constraints force T=0. The source's unrestricted six-block cancellation would require b>=36; using it at b=8 is false. This route does not resolve S78.

## 3. Route B: multiplication on the normalization defect

This route does not use the binary-factor annihilator induction.

### 3.1 An exact quotient formulation and propagation

The accepted polarization lemma with L=1 implies

    R_j=A_1 R_{j-1},   j>=7.

Taking quotients is legitimate as A-modules and gives

    C_j=A_1 C_{j-1},   j>=7.                           (B1)

Therefore

    C_8=A_1^2 C_6.                                    (B2)

Consequently S78 is equivalent to **A_1^2 C_6=0**, and if it holds, (B1) gives C_j=0 for every j>=8. This is also an independent check on the endpoint of the propagation argument. The accepted F210 only proves A_1^30 C_6=C_36=0. Replacing exponent thirty by two here requires a new statement about actual multiplication, not a finer count of unrestricted weights.

There is an explicit nonzero element to keep in view. In dimension seven R_6 contains the determinant representation (det V)^6: in the dual polynomial realization it is represented by

    det(x_1,...,x_7)^6.

The even exponent makes it invariant under all seven slot permutations. But A_6 is an image of Sym^6(Sym^7 V), whose Schur support has length at most six. Hence this seven-row representation survives in C_6. It is the standard length obstruction below b=a, not a new systematic kernel in the ordinary Foulkes range. It supplies an actual quotient class, not an ambient analogy.

Its products z(e_1)^2 times this determinant vector are nonzero in the domain R, of highest weight (20,6,6,6,6,6,6). Whether their classes in C_8 are zero is a membership question in A_8. Nonzero multiplication in R says nothing by itself about multiplication in the A-module C. We have not settled even this class; settling it would still leave the other C_6 constituents.

### 3.2 What chart denominators really prove

For a=7, the accepted chart lemma gives

    z(v)^(6k) R_k is contained in A_(7k).

Module generation in degrees <=6 then gives z(v)^36 R contained in A, so z(v)^36 belongs to the conductor for every v. The accepted ambient polarization statement turns these conductor elements into surjectivity only in degrees j>=7*36=252. This is the old cubic route, not a new estimate on C.

The known quadratic/F210 result is stronger, giving C_j=0 for j>=36. Neither proof says that z(v)^2 C_6=0, or that all degree-two products in A annihilate C_6. These assertions must not be inferred from local equality after inverting z(v). Local equality shows support at the irrelevant ideal; it gives no bound of two for this nilpotence.

Indeed, the ideal generated by z(v)^36 also has an invariant ambient obstruction in degree eight. In the dual W_8 model, det(x_1,...,x_7)^8 is S_7-invariant. After x_i -> x_i+t_i y its total t-degree is at most eight, because a determinant can use the common vector y in at most one column. Thus its coefficient of product_i t_i^L is zero whenever 7L>8. It annihilates the span of z(v)^L R_(8-L) for L>=2 (when the expression is defined). This does not give a functional on C_8: vanishing on those products is weaker than annihilating A_8. It blocks an ambient span replacement and nothing more.

### 3.3 Regularity of R does not control the missing multiplication

Use S=Sym(Sym^7 V), so A and R are graded S-modules. For dim V=7, R has dimension 7*6+1=43. RSW prove it is Cohen–Macaulay and reg_S(R)=36 (their d=7,n=6, with n even). C has finite length. The exact sequence

    0 -> A -> R -> C -> 0

gives, for the irrelevant ideal, H^0(A)=0, H^1(A)=C, and H^i(A)=H^i(R) for i>=2. Here H^0(R)=H^1(R)=0 by depth 43, and higher local cohomology of C is zero. Thus, with end(0)=-infinity,

    reg_S(A)=max{reg_S(R), end(C)+1}.                  (B3)

This follows directly from the local-cohomology definition of regularity. The grading and support ideals agree because R is finite over A and A is standard graded.

Using F210, end(C)<=35. Equation (B3) therefore proves reg_S(A)=36, regardless of whether C_8 is zero. In particular even the exact equality of the two regularities in this case cannot decide the seed. RSW's Theorem 3.9 bounds their normalization/covariant modules, not this finite-length defect. Treating its number as a bound of seven for end(C) would apply the theorem to the wrong module.

The missing estimate can equivalently be stated as H^1_m(A)_8=0, or, by (B1), end(C)<=7. Since reg(R)=36 dominates (B3), this is a deficiency-module estimate substantially finer than regularity of A or R.

### 3.4 What the primary effective bound and equations literature supply

Brion's 1997 publisher sample states Theorem 3.3: for dim V=d, let N be the smallest integer with d*N >= binomial(m+d-1,d-1). Then his h_{m,n}:Sym^n(Sym^m V)->Sym^m(Sym^n V) is onto for

    n >= (m-1)(d-1)(mN+m-N).

Here m=7 and n is our b. The product d*N was checked in the PDF text coordinates; it is not d to the N. This is a high-degree bound, not S78. The full proof was not obtained; no inference about its internal possible improvements is claimed.

RSW's equations section also prevents replacing the defect with just the Brill ideal. Brill equations cut out the Chow variety set-theoretically, but the paper explains additional rank equations and failures of equality of the relevant ideals/saturations. Moreover the equation interpretation of C_8* here involves degree-seven equations on the *eighth* Chow variety; standard Brill equations there have degree nine. Their existence or set-theoretic completeness does not prove absence of degree-seven equations. The bidegrees must not be swapped.

**Route B gap.** A proof must show that the actual A-module multiplication A_1^2 C_6 is zero, equivalently kill every degree-six generator after two steps, or compute H^1_m(A)_8 by a valid geometric argument. No such multiplication or deficiency estimate was obtained. The explicit surviving determinant class in C_6 does not decide it. This route stops at a precise unresolved statement rather than relabeling the cubic chart argument.

## 4. Verdict, novelty limits, and validation

S78 is neither proved nor refuted. The formal consequences in §§1 and 3.1 establish why a positive result would be substantial, not that it holds. There is no new subquadratic canonical range, complete seventh comparison, or new systematic canonical-kernel family in the remaining ordinary range.

The paid work beyond I198 consists of the exact (7,8)->(6,2) contraction, the simultaneous determinant-square restriction (A3), the explicit noninjectivity diagnostic for the Z restriction, the retained all-slot jet relations, and the identification of A_1^2 C_6 as the precise quotient bottleneck. These are auxiliary deductions and failure diagnoses. Their ingredients are source polarization, rank-two quadrics, determinantal contraction, and basic commutative algebra. They are not presented as new-to-literature theorems or a ninth accepted finding.

All checks were written mathematics: degrees (8,6) and (7,6) in the two differentiations; degree 7=6+1 in (A3); total degree 56 and determinant twist in (A5); dimension six for x^3 Sym^2 C^3; Vandermonde independence in §2.3; j>=7 and exponents two/thirty in (B1)-(B2); dimension 43 and regularity 36 in (B3). Zero-dimensional V is automatic for S78, and binary V is covered by the primary normality/Hermite-reciprocity discussion. Known diagonal canonical kernels at (5,5) and (6,6) are kept separate from ordinary comparison and from this off-diagonal seed.

No research program, parameter scan, numerical test, certificate replay, snapshot, seal, staging, commit, publication, or child agent was used. Both independent acceptance gates remain with the parent; there is no nomination to submit to them.
