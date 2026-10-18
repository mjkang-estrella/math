# Family 060: anticanonical-index arithmetic, pre-freeze screen

Myeongjin Kang; no affiliation. Original text CC BY 4.0. Status: NO NOMINEE; no theorem target was frozen, no acceptance or count. The proposed direction was to determine the largest finite numerical anticanonical index at fixed second Betti number, using the stipulated GSS theorem to reach Kato surfaces. The substantive arithmetic is already explicitly parameterized in the primary literature; no new construction was found here.

## Exact antecedents and scope

Pinned source `Global-Spherical-Shells-on-Minimal-Surfaces-of-Class-VII-September-24-2026/build/paper.tex`, Theorem `thm:main`, gives a global spherical shell for every connected minimal compact complex surface with b1=1, b2>0 and Kodaira dimension −infinity. Its topology/deformation and aspherical-geography corollaries are already paid, as are the corresponding arguments in `conclusion.tex`. We do not reprove or audit that theorem.

Fujiki–Pontecorvo, *Index of Kato surfaces*, arXiv:1406.2214v1, Definition 3.4, Theorems 3.5 and 4.1 and Proposition 5.7 provide the precise numerical index formula below. This index concerns the cohomology class of −iK represented by an effective divisor; it is not the least exponent of an untwisted holomorphic anticanonical section. Their main computation is for intermediate Kato surfaces. The introductory Enoki exceptions prevent silently declaring the formula valid for every minimal class VII surface. No restriction to intermediate surfaces has been adopted as a replacement theorem after a failed freeze: there was no freeze.

Write a simple Dloussky component as [s_(a1)...s_(ap) r_m], with ai,m positive integers and cost c=sum(ai)+m. Let f be the continuant, f(empty)=1, and put

    P(a1,...,ap)+1 = f(a1,...,ap)+f(a1,...,a_(p−1)),
    K_f=P(a1,...,ap)+1,
    Q_f=P(a2,...,ap)+m,

where P(empty)=0. For N components, with total cost b, the primary formula is

    K=product_f K_f,
    S=sum_h Q_h product_(f>h) K_f,
    index=(K−1)/gcd(K−1,S).

The exact affine return map t -> Kt−S, its fixed point S/(K−1), the common denominator interpretation, and the germ-composition correspondence are all primary operations, not new contributions of this screen. The source theorem would merely extend access to the already classified Kato setting.

## Elementary bound and why it does not supply a nominee

Let F_0=0,F_1=1 be the Fibonacci sequence. For an integer a>=1 put M(a)=[[a,1],[1,0]]. Entrywise M(a)<=M(1)^a: the latter has entries F_(a+1),F_a,F_(a−1), and F_(a+1)>=a. Multiplication preserves this order for nonnegative matrices. The top row of M(a1)...M(ap) is (f(a1,...,ap),f(a1,...,a_(p−1))). Consequently, with n=sum(ai),

    K_f <= F_(n+2) <= F_(c+1).

The identity F_(u+v+1)=F_(u+1)F_(v+1)+F_u F_v gives

    K <= product_f F_(c_f+1) <= F_(b+1),
    index <= F_(b+1)−1.

For multiple components the last inequality for K is strict, since each c_f>=2. A single component with m=1 and all ai=1 attains the bound for K. This does not establish equality for the index: the gcd in the already-known formula can lower it. The bound is a direct, elementary nonnegative-matrix optimization of the primary formula, not an eligible new substantial operation.

The diagnostic exhaustively enumerates all ordered positive simple-component data of total cost b<=12, merging states with identical (K,S); it computes the maximum of the primary index formula. At b=9 this maximum is 49, whereas F_10−1=54; at b=10 it is 80, whereas F_11−1=88. Thus simply identifying the largest lattice denominator K−1 with the largest numerical index is already invalid in this finite arithmetic model. These are arithmetic checks, not a new realization/classification proof. We have not proved a general exact-extremum formula, and no absence-of-literature claim follows.

The remaining arithmetic optimization could be asked independently, but neither that question nor numerical evidence is a candidate. No new geometric operation beyond classification transfer was identified. This closes only the proposed index-bound route; it does not exclude other deductions from the GSS theorem.
