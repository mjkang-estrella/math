# r177 — prefreeze construction and calculations

No theorem was frozen and there is no author-proof nominee. These are retained research derivations, including closed reductions and the exact unfinished extension. They do not constitute a correctness or contribution disposition. All symbols refer to INTERFACES.md and the fixed source cofiber X=C(f) at p=1009.

## The tested full operation

The investigated operation was a map nu:X smash X -> X with both unit identities for the source's bottom unit eta_X. The spectrum X and map f=mu(a smash 1) are retained. No prime change, higher power of v4, replacement by a module, conditional hypothesis on a product, or weaker final target is proposed. Associativity of nu was not part of this attempted operation. This was a prefreeze feasibility direction, not a frozen statement or a retry of an old frozen target.

Let barX=C(eta_X). The unit subcomplex U=(S smash X) union_S (X smash S) has its prescribed map g to X. There is a cofiber sequence

U -> X smash X -> barX smash barX.

The exact obstruction is the image of g under the connecting map

[U,X] -> [Sigma^(−1)(barX smash barX),X].

It is this selected element, including unit compatibility, that must vanish. Vanishing of every group used below would suffice, but is not necessary. A nonzero May group does not show this selected element is nonzero.

The 31 nonbottom cells give 961 ordered product cells. For two nonempty subsets S,T of {0,...,4}, put e_i=1_(i in S)+1_(i in T), rho=sum e_i, U_e=sum e_i u_i. A cell has dimension q U_e+rho and its extension obstruction lies in pi_(q U_e+rho−1)X. Every profile e_i in {0,1,2} with rho>=2 is realizable by such a pair. A profile records a degree, not its cellular multiplicity. The ANSS candidates are exactly

(s,w)=(qk+1−rho,U_e+k), k>=1.

The normalized bound gives (q−1)k<=U_e+rho−1. Throughout this finite range w<u5, so the additive comparison for BP*/I5 applies in both adjacent cobar degrees. Moreover w<p^4: only exterior intervals in positions 0,1,2,3 and the six polynomial letters below occur. Thus the diagnostic is genuinely finite; it has not truncated an unknown infinite weight tail.

## First splitting page, with exact enumeration

Use the ten intervals [a,b), 0<=a<b<=4, ordered lexicographically. For an exterior monomial write m for its length and H_j for its coverage of position j. The splitting differential replaces [a,b) by [a,c)[c,b), summed over a<c<b with exterior signs. The code checks its square is zero on all 1024 exterior monomials and computes kernels modulo images over F_1009 separately in each (m,H). The resulting exterior cohomology has total dimension 120. This numerical statement is a reproducible diagnostic, not an independent topological theorem.

Order the polynomial letters as

(A,B,D,C,E,F)=(b10,b20,b30,b11,b21,b12),

with weights (p,p+p^2,p+p^2+p^3,p^2,p^2+p^3,p^3), respectively. If L is their total exponent, then m+2L=s. Since every polynomial weight is at least p and m<=10,

k <= floor((2U_e+p(rho+9))/(2(p^2−p−1))).

Intersect this with the normalized bound. Reduction modulo p gives k=H0−U_e modulo p; the code retains every admissible positive representative, including possible carries. Given D,E,F exponents, subtract their weights and counts, calling the remaining count ell and remaining weight R. Set v=R/p−ell. The equations for A,B,C become

p B+(p−1)C=v, A+B+C=ell.

Consequently C=−v modulo p, 0<=C<=min(ell,floor(v/(p−1))), B=(v−(p−1)C)/p and A=ell−B−C. This enumerates all solutions, not a bounded guess for polynomial exponents. The high-letter count is bounded by floor((w−exterior weight)/p^3), which is at most two here. Each recorded solution is checked against the original weight and degree equations.

The result is 1049 degree/profile/basis candidates after the splitting differential, distributed as follows:

| k | candidates |
|---|---:|
|2|15|
|1001|9|
|1002|36|
|1003|93|
|1004|164|
|1005|217|
|1006|216|
|1007|162|
|1008|92|
|1009|36|
|1010|9|

There are none with e4=0, 33 with e4=1, and 1016 with e4=2. The largest exponents of A,B,D,C,E,F are respectively 1017068,1017,1,1009,0,0. The complete list, sparse-differential procedure and bounds are private/product-may.json and private/product_may.py. This is an upper envelope before later May differentials, ANSS differentials, extensions and evaluation on the actual attaching maps. It does not compute Ext itself.

For example e=(1,0,0,0,1) gives rho=2,U_e=u4. At k=2 a splitting-page candidate is

(h10 h20 h30) A^1006 B^2 C^1006,

in degree (4031,u4+2). Other candidates in that degree have exterior degrees five. The primary Lee–Ravenel differential delta_(2p−1)B=h12 A−h11 C applies to the small-coordinate algebra. Its Leibniz expression on the displayed element is a difference of the two products obtained by adjoining h12 or h11, with coefficient 2 and one less B. It cannot be replaced by the assertion that the entire ambient group vanishes: ambient incoming boundaries, later differentials and the additional fourth-position letters still require a calculation. No assertion of permanence, or of an actual nonzero product obstruction, is drawn from this example.

## A closed lower-spectrum improvement: the first faces really are paid

The source's binary product on Y initially has no stated associativity. It is possible to remove this particular concern directly, without changing Y or its product. For 1<=rho=sum_(i=0)^3 e_i, with 0<=e_i<=4, put U_e=sum e_i u_i. Then the same elementary source argument gives

pi_(q U_e+rho)Y=0.                                             (L)

Here is a hand calculation, so this step does not rest on the finite search. An ANSS term has s=qk−rho,w=U_e+k, k>=1. The normalized bound first confines w to less than 4,100,000, hence below u4 and p^3. Thus the additive comparison and the six exterior letters x=h10,a=h20,c=h30,y=h11,b=h21,z=h12 apply. Only A=b10,B=b20,C=b11 are polynomial letters. Write

F0=e1+e2+e3, F1=e2+e3, F2=e3, U_e=F0+pF1+p^2F2.

They satisfy F0<=12,F1<=8,F2<=4. With m<=6 and L=(s−m)/2, the polynomial lower bound is

(p^2−p−1)k <= U_e+p(rho+m)/2 <=4p^2+19p+12.

At p=1009 this is less than 5(p^2−p−1), so k<=4. Thus F0+k<=16<p and reduction modulo p forces H0=F0+k. Also w<=4p^2+8p+16<5p^2, so nB+nC<=4. Put delta=(rho+m)/2; parity makes it integral, 0<delta<=11. The exact weight equation now gives

H1−F1−k−delta−nC=p(F2−k−H2−nB−nC).

The left side is strictly between −p and p (its absolute value is at most 27), so both sides vanish. Therefore

H0=F0+k, H2+nB+nC=F2−k, H1=F1+k+delta+nC.

Of the three exterior letters covering position zero, only x and a do not cover position two. Hence H2>=H0−2, giving F0−F2+2k<=2. It follows that k=1,F0=F1=F2=f,nB=nC=0,H0=f+1,H2=f−1; only f=1,2 remain. If f=1 the exterior monomial must contain x,a, may contain y, and has H1<=2, contradicting H1=2+delta. If f=2 it must contain x,a,c, may contain y, and has H1<=3, contradicting H1=3+delta. No monomial exists already on the initial May upper page. Strong convergence proves (L). This is a small extension of the source's own digit argument, not a substantial nominee.

All positive cells of Y^r, r<=4, have degrees in (L). Finite cellular induction therefore gives [C(S->Y^r),Y]=0. In particular maps Y^r->Y are determined by their bottom-cell value when they exist. The source's two products mu and mu followed by the twist agree on that value; so do the two three-input parenthesizations. Thus mu is homotopy commutative and homotopy associative. For the actual relative unit comparison, the same argument applies to the reduced cells of the fat wedge quotient. The source constructed mu as an extension of the prescribed unit subcomplex; associativity and commutativity comparisons can be taken relative to those prescribed unit restrictions. This does not install all higher coherent structure or an E-infinity algebra on Y.

Put d4=q u4, F0'=Sigma^d4 Y and c:Y->X. Let m0=c mu:Y^2->X. The two maps

m0(f smash 1), m0(1 smash f):Sigma^d4 Y^2->X

are null. For the first, associativity identifies mu(mu(a,−),−) with f mu, followed by c f=0. For the second, use commutativity to move the even class a and then associativity. These are maps on the source's actual Y and f, not just BP-module equalities. Thus the two primary faces of the cofiber square can be extended. The finite calculation lower_multiplication.py independently finds no splitting-page candidates for (L), including all nonempty profiles for r=2,3,4.

## The remaining cofiber-square operation

There is a square with corners F0' smash F0', F0' smash Y, Y smash F0', Y smash Y and edges given by f. Its total cofiber is X smash X. Extending m0 from the last corner requires the two face null-homotopies just described and a compatibility null-homotopy on their common corner. Once faces H_L,H_R are chosen, their difference defines a secondary class

omega(H_L,H_R) in [Sigma(F0' smash F0'),X]
                  = [Sigma^(2d4+1)(Y smash Y),X].             (Q)

Changing a face changes omega by the corresponding precomposition of a map on Sigma(F0' smash Y) or Sigma(Y smash F0') with 1 smash f or f smash 1, with the appropriate sign. Thus the actual question is whether zero belongs to this specified obstruction set, together with the restrictions ensuring the two units on X. The resulting product must have both unit restrictions; an arbitrary nonrelative extension is not automatically enough. This record does not claim the face choices already solve that relative secondary problem.

The cells testing (Q) have dimensions

2d4+1+q sum_(i=0)^3 e_i u_i+sum_(i=0)^3 e_i,

which are exactly the e4=2 product-obstruction dimensions above. The 1016 candidates with e4=2 are therefore relevant to a concretely identified secondary operation, rather than an unspecified demand for a structured lift. The e4=1 candidates do not by themselves obstruct the primary faces, because the specific faces have just been nullified by associativity and commutativity. Killing entire groups was stronger than necessary there. The remaining problem must likewise evaluate the actual secondary operation or construct compatible null-homotopies; a count of groups cannot settle it.

The cofiber long exact sequence further identifies every remaining homotopy group as an extension of the cokernel of f_* on pi_*Y by the kernel of f_* one degree lower, with the d4 shift. That is an exact reduction with the actual self-map. BP multiplication by v4 does not determine these homotopy kernels or the secondary class. No replacement of (Q) by a regular quotient in a category of MU-modules has been made.

## A stronger scalar annihilation operation, without assuming a product on X

There is a useful additional payment. The source proves the translated basis first for the free BP-module BP*DT, before tensoring with Y. The same integral carry identity therefore makes the constant beta cocycle a boundary already with coefficients BP*DT. The normalized bars have positive weights and the coefficient weights are nonnegative. In stem d=pq−2 all possible higher terms are again (s,w)=(2+qj,p+j), impossible for j>=1. Naturality places beta in filtration at least two; the boundary raises that filtration and finite convergence for DT removes the possible hidden value. Hence the sphere-valued map

beta epsilon_T:Sigma^d T -> S

is null. This uses the actual integral comodule and detector; it is not inferred from its nullity after smashing with Y.

Toda's original 1968 Theorem 3, with gamma=beta and p beta=0, gives alpha beta^p=0 in the sphere. The statement and its extended-power argument were read, including the displayed original formula in the rendered page. Choose a sphere-valued J-lift of beta^p. If gamma:S^b->Z is any stable map with alpha gamma=0, choose its J smash Z lift. Smash it with p−2 copies of the sphere lift, then average the J factors. Its top value is beta^(p(p−2)) gamma. Smashing the preceding sphere-valued null map with Z gives

beta^((p−1)^2) gamma=0 whenever alpha gamma=0.              (B)

No multiplication or module action on Z is used. In particular this operation is available for Z=X. The proof uses only finitely many smash factors, an averaging idempotent with invertible denominator and finite duality. With gamma=beta^p it recovers the classical Toda upper exponent p^2−p+1; it is not offered as a new nilpotence theorem or as a nominee.

This strengthened operation does not complete (Q). To apply (B) to an obstruction, one needs an actual homotopy factor gamma, its alpha-null-homotopy, and enough beta divisibility, compatibly across the cofiber square. Most of the high candidates do not even have K=(p−1)^2 factors of A in this first splitting model: the minimum A exponents for k=1001,...,1010 are

1007980,1008989,1009997,1011007,1012016,1013026,1014035,1015045,1016055,1017066.

The k=2 candidates have A exponents as low as 1004. Even where an A^K factor appears, E2 divisibility alone is not a realized gamma with alpha gamma=0. The source's final obstruction proof supplied precisely those additional low-stem facts for its E2^(5,W)(Y); those facts have not been reproduced for the secondary operation (Q).

## Prefreeze endpoint

What remains is not the original bare question whether V(4) exists. X already exists by stipulation. The lower product can be compared and the first faces extended; the carry construction even gives a sphere-valued null operation and the uniform scalar relation (B). The unpaid operation is the relative nullification of the concrete secondary cofiber-square class (Q), or an alternative complete construction giving the same unit-preserving product on X, through the remaining May/ANSS and homotopy interfaces. The present work proves neither that this obstruction is nonzero nor that a product is impossible. It provides no substitute nominee, no exhaustion statement and no revision of an old scope or disposition.
