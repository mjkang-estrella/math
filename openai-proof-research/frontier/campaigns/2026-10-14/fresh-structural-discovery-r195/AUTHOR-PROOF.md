# Author proof of the frozen independent-family statement

This proof concerns exactly FROZEN.md (SHA256 823bddbdf60d3827d4f0cbf5684d559de760646b811f1626db497ed1786f8be8). It is submitted for independent review, without assigning correctness, contribution, acceptance or count. The hypotheses and operative proofs of Source319 at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. Source labels below identify precise operations, rather than unproved appeals to the headline. All categories and thick closures are ordinary, not tensor-ideal closures.

## 1. Fixed source data and what must be added

Fix p,M as in the frozen statement. Put D=2(p-1), q=p+1, k=F_(p^2), R=k[[x]], K_0=k((x)), Lambda=mu_q(k), Phi=K_0^Lambda=k((w^-1)), w=x^-q. The source supplies the coefficient diagram

N <-r- M_k -e-> M_0 -i-> M,

and pure chart generators T', T_k, T_0, T_Zp. Sections homotopy means pi_i P=[O[i],P]; it is not sheaf homology. On N, the height-one open is Spec k. The source twisted periodic derived category uses C_(i+D)=C_i(1).

Write H=G^1/(1+p Z_p), Omega=k[[H]], Delta=R[[H]], with coefficients on the LEFT and multiplication g c=g(c)g. The source geometry group-filtration and skew-filtration propositions give ordered coordinates g_1,g_2,g_3=gamma, U_i=g_i-1, and gr Omega=k[A,B,C], with weights 1,1,3. The first two group coordinates span the additive first-digit space k over F_p. The third belongs to H(2) and commutes with Lambda. Gamma_s=H(2s+1) has coordinates divisible by p^s.

The source completion operations proposition identifies a graded algebra E with E_(sD)=(x^-s Delta)^Lambda, zero in other degrees, and

E[t^-1]=(Delta[x^-1])^Lambda[t,t^-1], |t|=D.

The actual strict realization equivalence is Perf(E) -> Thick(T'-hat). It realizes cones, finite sums and retracts; its overlap is derived tensor with Phi[t,t^-1]. Completion is exact and has the source fracture square. In particular, the full subcategory C_comp of objects with perfect completion is thick and idempotent complete.

Let C_fin be the full subcategory of C_comp whose sections homotopy is finite in every degree. It too is thick and idempotent complete: use the long exact sequence, the fact that an extension of finite groups is finite, and direct summands. T' belongs to it, by the source chart computation. The topology and global-map propositions apply to every object of C_fin: overlap homotopy is locally compact, maps of perfect completions are continuous, and the image of the open homotopy is a discrete lattice. These are intrinsic topologies obtained from reduction maps.

The source uses one operator with initial reduction C. We require countably many irreducible symbols, a joint-kernel estimate for each, and a relative version of the reversal of coefficient changes. Sections 2–7 supply these steps.

## 2. Filtrations and invariant symbols at one fixed prime

### 2.1 Arbitrary coefficient weight

For any integer W>3, put wt(x)=W and keep the group weights 1,1,3. Then Delta has a complete separated multiplicative filtration with

gr_W Delta=k[X,A,B,C], |X|=W, |A|=|B|=1, |C|=3.

Here is the modification of source geom:skew-filtration. Ordered difference monomials are a topological basis by the same finite binomial change of basis on H/Gamma_s. The word filtration and ordered filtration agree because every interchange has a strict weight gain. The g_1,g_2 commutator contributes weight at least 3>2. A commutator with g_3 contributes weight at least p>4. For coefficients, U_i x-x U_i=(g_i(x)-x)g_i has weight at least 2W>W+3. Thus reordering can be iterated in the complete topology without introducing initial relations. At a finite group/coefficient quotient all letters generate a nilpotent ideal; conversely the ordered basis shows that sufficiently deep word stages contain neighborhoods. Consequently the topology is unchanged when W changes. Normality and regularity of x, and the quotient Delta/(x)=Omega, are unchanged.

The action of Lambda on the first digit has eigencharacters chi and chi^-1 over k. Indeed conjugation acts on the digit by its weight-one scalar; multiplication by a norm-one element on the F_p-vector space k has eigenvalues lambda and lambda^p=lambda^-1. Choose eigenbasis A,B of the degree-one plane. These letters replace the original linear basis, without changing the polynomial graded ring. Tame character averaging of linear combinations of U_1,U_2 gives exact eigenvectors V_1,V_2 in Omega, with these initial symbols. Their product V_1 V_2 is exactly invariant. U_3 is exactly invariant as well. All averages are finite, since q is prime to p.

### 2.2 A countable irreducible family

Choose strictly increasing ordinary primes d_j>=p. Choose a monic irreducible polynomial f_j(z)=sum_(h=0)^d_j c_(j,h) z^h over k of degree d_j. Such a polynomial exists: for prime d the Frobenius orbits of elements in F_((p^2)^d) outside F_(p^2) all have length d, giving ((p^2)^d-p^2)/d monic irreducibles. Its constant coefficient is nonzero because d_j>1.

Define

P_j(A,B,C)=sum_(h=0)^d_j c_(j,h) C^(2h)(AB)^(3(d_j-h)),
b_j=sum_(h=0)^d_j c_(j,h) U_3^(2h)(V_1 V_2)^(3(d_j-h)) in Omega^Lambda.

Each P_j is homogeneous of weight e_j=6d_j and is irreducible. To prove irreducibility, work first over an algebraic closure. If alpha runs through the distinct roots of f_j, the factors are C^2-alpha A^3B^3. Each is irreducible over kbar(A,B), because the A-adic valuation of alpha A^3B^3 is odd; Gauss's lemma gives irreducibility in kbar[A,B,C]. The factors are monic as polynomials in C, so any factorization over k would select a Frobenius-stable subset of these factors. Frobenius acts transitively on the roots of the irreducible f_j. There is no nonempty proper such subset. This proves the assertion. In particular P_j is not divisible by A, B or C. Distinct degrees make the P_j pairwise nonassociate.

The displayed b_j has initial symbol P_j in Omega. Both factors in every summand are invariant, so b_j is invariant. Moreover P_j is fixed by the involution A,B,C -> -A,-B,-C: the C exponents are even and AB is fixed. This will preserve the prime under operator adjoints.

### 2.3 Vanishing in the first congruence quotient

Let H_2 be the source congruence subgroup for which h(x)/x is 1 modulo x^2. The displacement and initialization calculations identify H/H_2 with the additive first-digit quotient k. For clarity, elements of H(2) have no first digit, hence lie in H_2; the initialization computation gives [H:H_2]=p^2, while [H:H(2)]=p^2. Thus H_2=H(2).

Its group algebra over k is commutative, and every augmentation element has p-th power zero: for a sum sum a_g(g-1), the p-th power is sum a_g^p(g^p-1)=0. The image of U_3 is zero. For h>0 the h-th summand of b_j therefore vanishes in this group algebra. The h=0 summand vanishes because 3d_j>=p and the image of V_1 V_2 is an augmentation element. We obtain

b_j maps to 0 in k[H/H_2].                                      (2.3)

This quotient condition, rather than the linearity of C, is the precise input to the initialization step.

## 3. Operators and paired gluing without losing their symbols

Take b=b_j. Regard its group-algebra measure as a measure in Delta. The function u_g=h_g-1, h_g=g(w)/w, has u_g/x modulo x constant on H/H_2. Equation (2.3) implies

integral b(g)(u_g/x)^n =0 modulo x, 0<=n<p^2.

The source first p^2 balanced orbit points have distinct residues u_g/x in k. Their Vandermonde matrix is invertible over R. Solve the p^2 equations for corrections supported at these points. Their right-hand sides lie in xR, so all correction coefficients lie in xR. Adding them kills the indicated moments exactly. Average under Lambda; vanishing is preserved by equivariance, and reduction stays b because b is invariant. Multiplication by x^n now gives integral nu(g)u_g^n=0 for n<p^2.

The remaining source operator construction has the following specific inputs, all unchanged: the first p^2 moments vanish; nu is invariant; the orbit indices satisfy r'_m=sum_l floor(m/N_l)<=p m/(p-1); and the inequalities on p,M hold. The coefficient-control lemma changes a chosen matrix depth by any polynomial of degree at most M in the next digit, independently for every lower digit label. Its corrections belong to (x^(p^r+1) Delta)^Lambda, preserve earlier depths and converge. The finite-field choice argument for pivot/nonpivot digits, and the infinite digit matching, use these inputs but do not use b=U_3. Apply that algorithm separately to each initialized b_j and weight by h_g^(-1/2).

It yields actual a_j in Delta^Lambda such that

a_j modulo x=b_j;                                              (3.1)

the Laurent matrix has finite crossings at every fixed pole; and its persistent unmatched rows and columns have the source lower bound c_j N^beta at every sufficiently large N, where

beta=log_p(2 floor(M/8))>1/3.

The positive constants and onset may depend on j. All this takes place at our fixed p. The measures, coefficient corrections and limiting actions are computed at the source's finite compatible coefficient/group levels. They are not formal operators invented from their symbols.

For every W>e_j, (3.1) implies sigma_W(a_j)=P_j: all x-divisible corrections have weight at least W, and b_j has first weight e_j. The same operator a_j works for every such W.

Use source glue:overlap, glue:pairs and glue:object with this operator. Put

m_j=cofib(a_j:T'-hat -> T'-hat),
Y_j=direct sum_(r=0)^(D-1) m_j[r].

Its overlap in every degree is Q_j plus K_j, with Q_j=Phi/a_j Phi and K_j=ker(a_j:Phi->Phi). Finite crossings make the image closed. The source matching produces q_s=w^s, s>0, and k_l in K_j cap R with distinct initial w-powers l<=0. Pair them in increasing s and |l|. At scale N at least c_j N^beta pairs have s<=N and |l|<=N, and their kernel projections are independent modulo x^(qN+1)R.

Choose a discrete complement to the source compact open subspace of Q_j plus K_j that contains these paired vectors, extend to a basis, and realize it as an open object V_j. Form the ACTUAL fracture pullback

U_j=Y_j times_(L Y_j) V_j.

The source gluing proof gives finite sections homotopy in every degree, completion Y_j, open part V_j, and the prescribed paired discrete lattice. In particular U_j belongs to C_fin. Only the new initialization and symbol were changed; the closed-image, lattice and homotopy-finiteness arguments have their original hypotheses.

## 4. Microlocal separation and the generalized growth estimate

Fix j and choose W>e_j. Localize the graded ring gr_W Delta at the multiplicative set of homogeneous elements outside the prime (P_j). There is a complete filtered ring S_j receiving Delta, flat on both sides, with this associated graded. We spell out why the source's construction applies beyond a coordinate prime.

For a complete positively filtered algebra A over finite k with polynomial associated graded, finite modules have complete good filtrations. Lift finitely many initial submodule generators and successively subtract initial terms; convergent coefficients express every member using those lifts. Compactness of finite products of A makes the resulting submodules closed. This proves noetherianity and strict finite presentations on both sides, as in source obs:microlocal-flat.

For the Rees ring, at each quotient modulo s^n invert homogeneous elements whose initial reduction is outside (P_j). The set is multiplicative and all its reductions are nonzero in a domain. Regularity follows through the s-layers. The commutator of any two elements is divisible by s, so ad_d^n(e)=0 modulo s^n. Its expansion gives the required left and right Ore relations with powers of d. Localized truncated Rees modules are exact and have surjective transition maps in every fixed degree. Their inverse limits, followed by the increasing union over filtration shifts, define the complete microlocal module. Its associated graded is the desired localization. Strict exact sequences stay exact at every truncation, then under these inverse limits and unions. On finite presentations the functor equals tensor with S_j, hence S_j is flat on both sides. Nothing in this argument requires P_j to be a coordinate: a multiplicative homogeneous regular denominator set suffices.

Every nonzero homogeneous element of gr S_j is P_j^v times a homogeneous unit for some integer v>=0, by unique factorization. The source principal-ideal argument now applies with P_j in place of C. In a nonzero right ideal choose an element of minimum initial P_j-order. Subtract right multiples matching successive initial symbols. The remainder's filtration increases, and the multipliers converge, expressing every element as a multiple of the chosen one. The argument on the left is identical. Thus S_j is a domain with principal left and right ideals. It has a two-sided Ore division ring of fractions, and its finite modules have the free-plus-torsion and length-one-resolution properties in source obs:periodic-splitting.

Since X is outside (P_j), x is a unit in S_j, by lifting its graded inverse and correcting higher errors. The same inverse argument shows that any element with symbol outside (P_j) becomes a unit. The element a_j has initial symbol P_j and has no one-sided inverse; S_j/a_j S_j is nonzero torsion. As in source obs:coefficient-extension, the tame character decomposition makes Delta[x^-1] finite free on both sides over its invariants. Therefore

E -> B_j=S_j[t,t^-1]                                           (4.1)

is flat on both sides. It defines an exact functor Psi_j:C_comp->Perf(B_j). We have Psi_j(T')=B_j and H_i(Psi_j(U_j))=S_j/a_j S_j in every degree.

### 4.1 The cubic-root bound for an arbitrary chosen prime

Suppose a,b in Delta have nonzero reductions with sigma(bar a)=P_j and Q=sigma(bar b) not divisible by P_j. For every fixed L>=0,

dim_k image({f in x^-L R : a f=b f=0} -> K_0/x^n R)
   = O((1+n)^(1/3)).                                         (4.2)

Here constants may depend on a,b,L,j, and no uniform bound over the family is claimed.

The first part of the source growth proof is independent of the symbols. For a finite independent family f_i modulo x^n, the orbit functions h(f_i) span a K_0-vector space with a full R-lattice of integral-valued functions. Independence and Weierstrass preparation bound the pole orders of coefficients of integral combinations by O(n). Truncating the resulting series gives an integral orbit polynomial of degree J=O(n) with the same residue. The normalized Newton basis is

x^-r'_m product_(v<m)(z-z_(b_v)), 0<=m<=J.

Balanced orbit valuations make it integral; evaluation successively at b_m proves that it is a basis. If two orbit points agree modulo x^l and N_l>J, their basis residues agree: replacing one factor contributes l valuation, while deleting that factor loses at most l-1 required matches. Choose s with N_(p^s)>J and p^s=O(n^(1/3)), using N_(p^s)>=p^(3(s-1)). The residue lattice injects into functions on H/Gamma_s annihilating the left translates of bar a,bar b. Its dimension is bounded by the associated graded quotient

k[A,B,C]/(P_j,Q,A^T,B^T,C^T), T=p^s.                            (4.3)

Changing the degree-one basis does not affect the power ideal: since T is a p-power, an invertible linear change sends (A^T,B^T) to itself. This is the only place where the source proof used its coordinate symbol C. Since P_j is irreducible and Q is not divisible by it, P_j,Q is a regular sequence in k[A,B,C]. If Q is constant, (4.3) is zero. Otherwise the Hilbert series of the quotient by P_j,Q is

(1-z^e_j)(1-z^deg Q)/((1-z)^2(1-z^3)).

Its coefficients are bounded: at z=1 two numerator zeros cancel two of the three denominator zeros; at either other cube root the denominator has at most a simple zero. Polynomial division and partial fractions therefore give bounded coefficients in all degrees. Adding A^T,B^T,C^T leaves representatives of weight at most 5(T-1), so (4.3) has dimension O(T). This proves (4.2), retaining the source exponent 1/3. This calculation does not assume that P_j becomes a coordinate after changing variables.

### 4.2 Correct-sided remainders and adjoints

Two consequences of (4.1) and the initial ideal are needed.

(a) If J is a right x-saturated right ideal in Delta, a_j Delta is contained in J, and J S_j=S_j, there exists b in J with sigma(bar b) outside (P_j).

(b) If b_0 in Delta[x^-1] is outside S_j a_j and annihilates a subspace V of ker(a_j:K_0->K_0), there exists b in Delta annihilating V with sigma(bar b) outside (P_j).

For (a), if all reductions lay in bar a_j Omega, repeatedly write j=a_j d_0+j_1 x, using right normal division and right saturation. The convergent expansion would put J inside a_j Delta, contradicting J S_j=S_j. Choose a reduction outside that right ideal. If its symbol is divisible by P_j, subtract a right multiple of bar a_j matching its symbol. Infinite continuation would converge to an expression in bar a_j Omega, a contradiction. Thus finitely many subtractions yield the desired symbol. For (b), first clear x-denominators on the LEFT. Repeatedly subtract left multiples of a_j and divide on the LEFT by x. Nontermination would put the original element in Delta a_j, hence S_j a_j. Subsequent initial-symbol subtraction terminates for the same reason. All these operations preserve annihilation of V. No step commutes x through a_j.

The source constant-term pairing CT_x(uf) supplies a continuous adjoint on Delta. On c delta_g it is

g^-1(c) [x (g^-1 x)'/(g^-1 x)] delta_(g^-1).

Modulo x it is group inversion on Omega. On its commutative associated graded it sends A,B,C to -A,-B,-C. Hence it preserves (P_j) by Section 2.2 and takes symbols outside it to symbols outside it. The generalized growth estimate applies to a_j^dagger,b^dagger as well. It is reduction followed by the Omega symbol that is used here, not an assumed action of S_j on Laurent functions.

## 5. Global ghost control with the enlarged target class

For every P in C_fin and global map g:U_j->P,

H(Psi_j(g))=0 implies H(Psi_j(g)^*)=0,                           (5.1)

where * is the module dual over B_j, a left module. This is the needed enlargement of the target quantifier in source obs:dual-ghost. Here is its proof, including the dependence on the target.

Assume ordinary homology vanishes. Restrict the completed map to m_j[r] and precompose with its cofiber inclusion T'-hat[r]->m_j[r]. Denote this homology class by h. Before microlocalization, extend only to D_loc=Delta[x^-1][t,t^-1]. Its right annihilator J_h intersected with Delta contains a_j Delta and is right x-saturated. If I_h denotes the annihilator over Delta[x^-1], then I_h=J_h Delta[x^-1], by clearing right x-denominators. The cyclic injection Delta[x^-1]/I_h -> H_r(P-hat_(D_loc)) stays injective after tensoring with S_j by left flatness. Its generator becomes zero because h factors through the assumed ghost. Thus J_h S_j=S_j. Section 4.2(a) gives b in J_h with sigma(bar b) outside (P_j).

The equations h a_j=h b=0 are zero derived maps from a free shift before microlocalization. Derived tensor with K_0[t,t^-1] preserves them; no flatness of this Laurent representation is required. Associativity identifies that tensor with the original perfect E-module tensored with K_0[t,t^-1]. The tame average pr:K_0->Phi is E-linear. Projecting AFTER this tensor operation shows that the overlap map W(h) kills pr(a_j f) and pr(b f) for every f in K_0. We do not assert Delta[x^-1]-linearity of pr.

Choose a compact open target subspace C_P. A continuous functional vanishing on it pulls back along W(h)pr to CT_x(u f). Continuity puts all such u in one fixed bounded lattice x^-L R. The two vanishing equations give a_j^dagger u=b^dagger u=0. Section 4.1 and the adjoint compatibility imply that the images of the polar representatives w^s, 1<=s<=N, have rank O(N^(1/3)) modulo C_P. More explicitly, independent functionals on their images pull back to u independent modulo x^(qN+1)R, so (4.2) bounds their number.

Enlarge C_P to contain the images of the compact kernel subspace K_j cap R. The global origin of g sends the paired vectors (q_s,k_l) into the discrete lattice of the target open homotopy. Its intersection with C_P is finite dimensional. The source lattice supplies c_j N^beta simultaneous pairs; their polar images have rank O(N^(1/3)) modulo C_P. Their span therefore contains a subspace killed by W(g-hat) of dimension

c_j N^beta-O(N^(1/3)).                                        (5.2)

Its kernel projection has the same dimension modulo x^(qN+1)R, by the independent leading powers of the k_l. These projected vectors lie in R and are killed by a_j.

Take any pre-extension perfect-module map theta:P-hat->T'-hat[ell]. On each m_j[r], the composite theta g-hat kills the cofiber inclusion: its composite c with that free shift satisfies c a_j=0, and E embeds in the domain Delta[x^-1][t,t^-1]. It consequently factors through the connecting map as b' partial_r. If the operation degree is not a multiple of D it is zero already. Otherwise normalize by t to regard b' as an element of (Delta[x^-1])^Lambda.

This composite kills all cokernel components on the overlap, while in residue r+1 the only kernel component is that of m_j[r]. Thus b' annihilates the projected subspaces in (5.2). If b' were outside S_j a_j, Section 4.2(b) would give a single integral b_1, with symbol outside (P_j), annihilating the span of ALL those projected subspaces. Applying (4.2) to a_j,b_1 and n=qN+1 contradicts beta>1/3. Hence b' belongs to S_j a_j. After coefficient extension, b' partial_r=0 because a_j[1] partial_r=0. Every theta g-hat is therefore zero after extension.

For a perfect right E-module M, finite-cell evaluation and closure under retracts give

B_j tensor_E^L RHom_E(M,E) = RHom_(B_j)(M tensor_E^L B_j,B_j).

Right flatness of B_j commutes the left-hand tensor with homology. Every class in the resulting dual homology is a finite sum of coefficients times pre-extension classes theta. Their composites with g have just been proved zero. This proves (5.1).

The target assumptions used were precisely: perfect completion for finite-module realization, flat base change and dual evaluation; finite sections homotopy for intrinsic topology and the discrete lattice. Both hold for all P in C_fin. No use was made of an expression for P using only T'. This verifies (5.1) on every tail in a tower built from any finite collection of C_fin objects.

## 6. Galois conjugates and relative nonmembership on N

Let tau be the nontrivial element of Gal(k/F_p). The mod-p formal-law stack and the chart with v_2=1 are defined over F_p. The quotient by the central subgroup 1+p Z_p is compatible with that base change: its automorphisms are the scalar multiplications [c], fixed under the field action. Thus tau induces a semilinear exact involution on D(N), preserving T', completion, and finite sections homotopy. It intertwines r^* with the corresponding involution of D(M_k).

On the coefficient chart x is a variable defined over F_p, so tau fixes x and conjugates coefficients. On group coordinates it applies Frobenius to formal-group digits. Hence it preserves H(i), Gamma_s and Lambda, and induces a filtered semilinear automorphism of Omega. To check the weight-three issue explicitly, an element of H(2) has first two ordered coordinates divisible by p, so those contributions to its difference from 1 have weight at least p>3. The leading class of tau(U_3) is a nonzero multiple of C. The weight-one plane is carried isomorphically to itself, with possible terms of higher weight. Applying tau twice gives the inverse filtered map. The same reasoning with x fixed works for every W in Section 2.1.

It follows that tau(P_i) is homogeneous irreducible of the SAME weight e_i. The completion of tau U_i is the sum of the D shifted cones on tau(a_i); any semilinear change of chart-generator trivialization conjugates these maps and does not change whether they become invertible. Whenever W>e_i, the relevant symbol is tau(P_i).

Fix j and a finite set F of positive integers not containing j. Choose

W>max({e_j} union {e_i : i in F}).

Use S_j and Psi_j formed with this W. For i in F, neither P_i nor tau(P_i) is associated to P_j: their degrees differ, and all are irreducible. Thus a_i and tau(a_i) become units in S_j. Consequently

Psi_j(U_i)=0=Psi_j(tau U_i), i in F.

Put T_F=T' plus direct sum_(i in F)(U_i plus tau U_i). Then T_F belongs to C_fin and Psi_j(T_F)=B_j. Moreover H(Psi_j(U_j)) is nonzero torsion. Equation (5.1) applies to every map U_j->P with P in Thick(T_F).

We use the source finite-tower criterion, recalling its complete induction to make explicit why these conditions address all ordinary thick constructions. Over a two-sided principal domain S, finite modules split as free plus torsion and have free resolutions of length at most one. Hence perfect D-periodic modules over S[t,t^-1] split into the periodizations of their homology: lift each free presentation to cycles and boundaries and sum the D resulting quasi-isomorphisms. They split as free shifts plus a torsion-homology summand. Every object of Thick(T_F) is a retract of a finite tower whose layers are finite sums of shifts of T_F. Octahedral concatenation gives this for cones, and extending maps by zero on retract complements moves every retract to the end.

If U_j were such a retract, write its maps to successive tower tails as g_l. At the final zero tail both ordinary and dual homology vanish. Suppose these vanish at the next tail, whose microlocalization splits as V plus L, with V free and H(L) torsion. Dual vanishing says the map from Psi_j(U_j) to V is the ZERO DERIVED MAP, since projections to free shifts are dual homology classes. Lift the map to the preceding tail through the fiber of its projection to V. This fiber fits into a triangle F_free -> Z -> L. The map preceding H(F_free)->H(Z) has torsion source and free target, hence is zero. The lifted map from H(Psi_j(U_j)) lands in H(F_free), because its composite to H(L) is zero by the induction hypothesis. A torsion module has no nonzero map to a free module over a domain. Ordinary vanishing follows at this tail, and (5.1) restores dual vanishing. Induction reaches the initial retract insertion, contradicting its nonzero split injection on homology.

Therefore

U_j not in Thick(T', U_i, tau U_i : i in F).                    (6.1)

This applies also to F empty, so each U_j satisfies all three hypotheses of source transfer:criterion. The common W is only a tool for the finite comparison, not part of the definition of U_j or X_j. No single finite W is asserted to dominate all e_i, and no such assertion is needed.

## 7. Relative reversal of reduction, finite-field descent and the center

Write F_j=e_*r^*U_j in D(M_0). Let Z_j in Sp_(E(2)) correspond under the stipulated homology-compatible TRIANGULATED equivalence to i_*F_j. Set X_j=tau_(>=0) Z_j.

By (6.1) with F empty, source transfer:criterion applies. Thus X_j is connective p-complete, pi_i Z_j and pi_i X_j are finite p-groups, X_j has fp-type at most two, L_2 X_j=Z_j, and X_j is outside Thick(b_p). This use does not require a monoidal comparison. The underlying-spectra and pure-generator identifications are those actually proved in source comp:generators.

We now prove the relative assertion. Suppose, for some finite F not containing j,

X_j in Thick(b_p, X_i : i in F).                               (7.1)

Exact E(2)-localization and the triangulated comparison carry (7.1) to

i_*F_j in Thick(T_Zp, i_*F_i : i in F).

Apply the source exact derived reduction Li^*. It sends T_Zp to T_0. Write R_i=Li^*i_*F_i. We obtain R_j in Thick(T_0,R_i : i in F).

For every F_i the source reduction triangle is

F_i[1] -> R_i -> F_i --delta_i--> F_i[2].                        (7.2)

The natural delta_i is nilpotent here, in the uniform-on-shifts sense used by the source. Indeed U_i has perfect completion; source transfer:central-completion identifies completed r^*T'-hat with the fiber of c-1 on T_k-hat, so the completions of r^*U_i and e_*r^*U_i are in the requisite finite thick closures. On the complete generators the degree-two natural map vanishes by sparsity (D>12), and it vanishes on the pure height-one open. Thick nilpotence and the actual fracture square give the source nilpotence statement for F_i. These hypotheses hold for our U_i without reference to its special symbol.

We use the precise uniform-on-shifts nilpotence lemma, without assuming that a natural degree-two transformation commutes with shift. Its additional hypothesis is that the cone at A[h] is a shift of B(A[h]) for an exact functor B. Exactness then puts all those cones in Thick(B(A)); octahedral triangles put the cone of a vanishing successive power there too. That last cone is A[1] plus A[2n], so A belongs to Thick(B(A)). For (7.2), B=Li^*i_* is exact, and its comparison triangle verifies this cone hypothesis. It yields

F_j in Thick(R_j), hence F_j in Thick(T_0,R_i : i in F).         (7.3)

Extend scalars by e^*. Finite separability gives the EXACT decomposition

e^* e_* G = G plus tau G                                      (7.4)

on D(M_k). It follows termwise from k tensor_(F_p) k = k times k, is compatible with differentials, twists and the groupoid maps, and therefore descends to the periodic derived category. In particular r^*U_j is a retract of e^*F_j. From (7.3),

r^*U_j in Thick(T_k,e^*R_i : i in F).

Apply the exact functor Q=Rr_*. It sends T_k to T'. Thus Qr^*U_j belongs to Thick(T',Qe^*R_i : i in F).

Each R_i belongs to Thick(F_i) by (7.2), irrespective of whether that triangle splits. By (7.4) and compatibility with r^*,

Qe^*R_i belongs to Thick(Qr^*U_i, Qr^*(tau U_i)).                (7.5)

For every V, the source central comparison triangle is

V -> Qr^*V -> V[-1] --epsilon_V--> V[1].                        (7.6)

Consequently Qr^*V belongs to Thick(V). Combining this with (7.5) shows that Qr^*U_j lies in Thick(T',U_i,tau U_i : i in F).

Finally epsilon_(U_j):U_j->U_j[2] is nilpotent by the source argument: it is zero on complete generators and on the pure open and extends by thick nilpotence and fracture. The same cofiber-of-a-power argument applied to (7.6) implies U_j in Thick(Qr^*U_j). We have contradicted (6.1).

Thus (7.1) is impossible for every finite F not containing j. Any expression in the thick closure of an arbitrary set uses only finitely many of its objects. This proves the frozen assertion with ALL other X_i. The Galois terms in (7.5) are why distinct degrees were built into the symbol construction; discarding them would not prove the relative claim.

## 8. Exact fp-type, the two comparisons, and the lattice consequence

The source transfer proof verifies fp-type by an actual finite-total test. A finite type-three V kills Z_j by E(2)-locality and finite duality. In the triangle X_j->Z_j->N_j, N_j=tau_(<0) Z_j, one gets V smash X_j = Sigma^-1(V smash N_j). The left side is bounded below with finite homotopy groups, the right side bounded above. Thus it has finite total homotopy. Mahowald–Rezk Proposition 3.2 gives fp-ness and type at most two for the connective p-complete X_j.

If its type were at most one, Lee–Pstragowski's height-one theorem would put X_j in Thick(BP<1>_p-complete). The source scope:exact-height proof constructs that standard generator as the completed v_2-cofiber of b_p, including its standard mod-p cohomology identification. It therefore lies in Thick(b_p), contrary to Section 7 with F empty. Each X_j has exact fp-type two.

For the localization comparisons, the hypotheses of source scope:telescopes are satisfied objectwise: Z_j is E(2)-local, its homotopy is degreewise finite p-primary, and X_j is its connective cover. The negative tail N_j is a filtered colimit of finite Postnikov ranges, each built from shifts of H F_p by composition series. The source argument makes H F_p acyclic for T(0),T(1),T(2); finite localization is smashing and has the joined telescope Bousfield class. Hence N_j is L_2^f-acyclic. The source's E(2)-local comparison calculation identifies L_2^f Z_j with Z_j and L_(T(2)) Z_j with L_(K(2)) Z_j. Applying the localizations to the same tail triangle gives the two canonical equivalences in the frozen statement. This invokes the source's actual restricted comparisons, not an unrestricted telescope conjecture or a monoidal property of the algebraic equivalence.

For I subset of the positive integers let C_I=Thick(b_p,X_i : i in I). If I is contained in J then C_I is contained in C_J. Conversely, if some j belongs to I but not J, Section 7 says X_j is not in C_J, since C_J is contained in Thick(b_p,X_i:i!=j). Therefore containment of categories implies containment of subsets. This proves the order embedding and the continuum cardinality conclusion.

The ambient class of bounded-below p-complete spectra of fp-type at most two is thick. Indeed bounded-below and p-complete are preserved by the permitted finite constructions. Fix a finite type-three test spectrum; finite-total homotopy after smashing is preserved by its exact smash functor and finite long exact sequences, shifts and retracts. The standard b_p and all X_i pass this test. Thus each C_I has the claimed ambient scope.

Finally, if C_N had finite thick generators G_1,...,G_m belonging to it, each G_a would use b_p and only finitely many X_i. Take the finite union F of these indices. Then Thick(G_1,...,G_m) is contained in C_F. Choosing j outside F contradicts X_j in C_N and X_j not in C_F. This proves precisely the finite-generation assertion in FROZEN.md, and says nothing about finite generation of a larger fp category.

This completes the author argument at the frozen scope. Its distinctive bridge consists of invariant high-degree symbols surviving the operator construction, the non-coordinate regular-sequence kernel bound, the enlarged global ghost implication, and relative descent with all Galois and nilpotent-boundary terms retained. Independent correctness and substantial-contribution assessment remain external to this author packet.
