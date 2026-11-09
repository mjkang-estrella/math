# 380100: full ordinary bridge; no new-credit claim

Exact source: Braun–Develin, Conjecture 2.4, sources/380100.pdf.
Relevant later primary body: Pfeifle, arXiv:0707.3010v2, Theorem 4.11,
Corollary 4.9, equation (7), Proposition 4.5 and the definition following Example 4.6.
Read from sources/pfeifle.pdf and sources/pfeifle.txt. Kölbl, INTEGERS 25 (2025)
A68, Conjecture 2 and Theorems 4/7, still describes only a restricted canonical-line result.
The latter does not establish absence of an older subsumer.

Put b_j(z) = binom(z+d-j,d), 0<=j<=d. For y>0 choose the unwrapped
arguments Theta_j(x,y) as the sum of the d arguments in (0,pi) of the
linear factors z+d-j-r. Successive differences are

Theta_(j+1)-Theta_j = arg(z-j)-arg(z+d-j) > 0.

Their total spread is

A_d(x,y) = sum_(r=0)^(d-1) [arg(z-r)-arg(z+r+1)].

For a=r+1/2 and u=x+1/2 the r-th summand equals

F_a(u,y) = arctan((a-u)/y)+arctan((a+u)/y).

It is even in u. For u>=0 its derivative is

-y/((a-u)^2+y^2)+y/((a+u)^2+y^2) <= 0.

Therefore F_a(u,y)<=F_a(0,y)=2 arctan(a/y), and
A_d(x,y)<=Phi_d(y):=2 sum_r arctan((r+1/2)/y).
For d>=2, Phi_d decreases continuously from d*pi to 0. There is a unique
b_d>0 with Phi_d(b_d)=pi. If y>b_d, all the b_j(x+iy) lie in one open
half-plane through zero: rotate by the midpoint of Theta_0 and Theta_d;
every rotated real part is strictly positive. Every nonzero nonnegative
linear combination is consequently nonzero. Conjugation proves |Im z|<=b_d
for every root of every SNN polynomial.

At z=-1/2+i b_d, the products b_0(z) and b_d(z) have the same modulus
(termwise paired factors) and arguments differing by pi. Thus M_d=b_0+b_d
vanishes there. Every root of M_d lies on Re z=-1/2: if x>-1/2 then each
|z+r+1|>|z-r|, so |b_0(z)|>|b_d(z)|; if x<-1/2 the strict reverse holds.
Together with the just-proved bound this identifies the largest-norm roots
of M_d as the pair -1/2 +/- i b_d. For d=1 all SNN polynomials are positive
linear combinations of z+1 and z, so all roots are real; M_1=2z+1.
This proves the literal ordinary statement.

Novelty decision: Pfeifle's Theorem 4.11 already describes the ENTIRE feasible
nonreal root locus as the closed outer oval, and equation (7) describes
that oval by this same viewing-angle sum. The evenness/one-line derivative
calculation above identifies its highest point and M_d attainment. This is
an explicit routine bridge from the older full root-locus theorem, not a
claim of a new substantive solution. The elementary cone proof above is
recorded so a root reviewer can check the exclusion, instead of relying on
a title or abstract. No Lean endpoint or credit is claimed for 380100.
