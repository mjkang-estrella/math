# Exact polynomial isolation: reduction and a failed uniform induction

Research date: 2026-10-29 UTC (2026-10-28 America/Los_Angeles).
Credit 0. No complete eligible candidate, acceptance, or Lean endpoint.

## Target and actual source bodies

Roger Tian, *Identities of the Function f(x,y)=x²+y³*, arXiv:0910.1571v1,
Conjecture 3, actual PDF page 3; preceding Lemma 2 is on page 2.
https://arxiv.org/pdf/0910.1571v1
https://arxiv.org/html/0910.1571v1
MathDB319089, UUID9c7dc071-f1c3-422d-8257-c3749763ed69.

Let T be any finite ordered full binary tree with at least one leaf, with
operation F(a,b)=a²+b³ at internal nodes. Write p_T(x) for its all-x
polynomial. T is isolated if p_S=p_T for any one-variable expression S
forces S=T syntactically. For every isolated T, every n>=1, and every
assignment c of its leaves to x_1,...,x_n, Conjecture3 asserts that the
resulting polynomial cannot equal any syntactically different expression
in these n variables. Variables may repeat and need not all appear.
No bounded-depth or bounded-leaf condition is in the source.

Lemma2 assumes that ALL one-variable trees are isolated. Its substitution
of a selected variable by F(x,x) produces expanded trees which need not be
T. Consequently the local isolation hypothesis for T cannot be substituted
into that proof. Source Propositions6/7 reconstruct a root with a bare
leaf child by order2/order3 terms. The later lexicographic machinery treats
special shapes; none of these bodies states the full Conjecture3.
The companion0910.1576 concerns exponential Diophantine equations and does
not prove this tree-labeling assertion. Its Proposition7/11 and final
Conjecture13 were inspected. No upstream theorem is assumed beyond these
explicitly stated source contracts; no corpus theorem is used as a black box.

## A full-quantifier sufficient condition, with proof

Give T's l leaves independent variables z_1,...,z_l, and denote its
polynomial P_T. Define

    w_i(x) = (partial P_T / partial z_i)(x,...,x).

If these l polynomials are Q-linearly independent, every labeling of T is
uniquely reconstructible among labelings of that same tree. Indeed equality
of two labeled polynomials implies, after differentiation with respect to
x_j and diagonal restriction,

    sum_{i:c(i)=j} w_i = sum_{i:d(i)=j} w_i

for each j. Independence makes all indicator coefficients equal, hence c=d.
If T is isolated and an arbitrary expression H equals a labeling of T,
setting every variable equal to x shows that H has the same tree T.
The preceding argument now proves H has the same labels as well.
This proves the entire source conclusion under the single sufficient
hypothesis of gradient independence for every isolated T.

This is a helper reduction, not an eligible outcome. Independence for all
T is a stronger sufficient assertion. It is not asserted equivalent to the
source: only certain coefficients in {-1,0,1} are needed, and higher
polarizations might distinguish labels even when first derivatives cannot.

## Recursive gradient spaces and the exact obstruction

Let W_T be the rational span of its diagonal leaf gradients. For T=F(A,B),
write a=p_A,b=p_B. Chain rule gives the exact recursion

    W_T = 2a W_A + 3b² W_B,

with the individual columns obtained by multiplying the left gradients by
2a and right gradients by3b². Thus induction on column independence would
close if

    a W_A intersect b² W_B = {0}                         (G)

at every relevant root. This uniform intersection assertion is UNPROVED.
For a child polynomial of degree d, every leaf gradient has degree <=d-1,
because differentiation lowers every monomial's total degree by1.
Put d=deg a,e=deg b,h=deg gcd(a,b²). Coprimality after dividing by the gcd
shows aU=b²V forces U=(b²/g)H,V=(a/g)H. Therefore the degree envelopes
prove (G) whenever

    2e-h > d-1 OR d-h > e-1.                            (D)

This sufficient test genuinely fails; it is not legitimate to assert it
for every root. Put q=F(x,x), A=F(q,q), B=F(q,x), T=F(A,B) (seven leaves).
Then

    a=x^9+3x^8+3x^7+2x^6+2x^5+x^4,
    b=x^6+2x^5+x^4+x^3,
    gcd(a,b²)=x^4, (d,e,h)=(9,6,4).

Both strict inequalities in(D) fail: 2e-h=8=d-1 and d-h=5=e-1.
More strongly, the enveloping spaces really intersect: U=b²/x^4 and
V=a/x^4 are nonzero, have degrees8 and5, and satisfy aU=b²V identically.
Their full coefficients appear in exact-checks.json. Thus a proof retaining
only degree bounds and this gcd has lost essential information.

This is NOT a gradient dependence or a source counterexample. For this T,
the actual seven gradient columns have the coefficient minor at powers
x^7,...,x^13 equal to -2176782336. They are independent. Moreover U is not
in the actual left space W_A, as an exact augmented rank test certifies.
Source isolation of this seven-leaf T has not been established here; this
example only defeats the proposed unrestricted degree-envelope induction.
Even if isolated-tree hypotheses rescue a refined criterion, that bridge
still requires proof. Prove(G) for all isolated roots, or obtain a different
uniform labeling reconstruction argument, before claiming a full result.

## Bounded exact diagnostics

check.py constructs exactly212 prescribed/seeded trees, not an exhaustive
Catalan enumeration: six balanced trees (up to64 leaves), two comb families
through24 leaves, and160 seeded random trees with4..32 leaves. It evaluates
leaf gradients over F_1000003 at 2l+5 integer points and computes exact ranks.
Every listed matrix has column rank l. Since coefficients are integers,
a nonzero modular minor is a rigorous certificate of rational independence
for THAT shape. Repeated shapes are allowed;212 is a case count, not a claim
of212 distinct shapes. These checks do not prove source isolation or a
uniform statement and earn no fixed-parameter credit.

gcd_check.py draws350 fixed-seed trees, checks244 with degree<=180, and
retains the seven-leaf failure above. exact_check.py independently constructs
the integer coefficient matrix and exact minor, verifies the polynomial
intersection and nonmembership, and checks the companion arithmetic bound
at6831 (m,n) pairs. All three executables set512MiB RLIMIT_AS,45CPU seconds,
and BLAS1 before computation. No Lean, floating point or exponential tree/
coloring enumeration is used.

## Earlier target excluded by an actual theorem body

MathDB333392 / You–Chen–Yuan1606.05039v1 Conjecture2.2 asks for ALL k>=1
and f:N->C satisfying f(u²+kv²)=f(u)²+k f(v)², with positive u,v,
classifying f as zero, signed identity, or signed constant1/(k+1), the signs
forced positive on represented integers. The original proves k2..5 only.
Bui Minh Mai Khanh, *On conjecture concerning the functional equation*,
Annales Univ.Sci.Budapest.Sect.Comp.46(2017)123–135, Theorem on printed
page124, proves exactly this for every D>=1.
https://ac.inf.elte.hu/Vol_046_2017/doi/123_46.pdf
The bridge is D=k,n=u,m=v and E={u²+kv²:u,v>=1}; the theorem's epsilon(n)
is1 on E and arbitrary +/-1 elsewhere. Both direction and complex domain
match. Actual proof includes Lemmas1/2 (quadratic plus periodic reduction)
and Lemmas3/4 (elimination of periodic terms), not an abstract inference.
Received15May2017, accepted15June2017, long before this lane. Credit0.
Prior algebra lane had screened333392 without a proof; its open label is
superseded by this positive body-level exclusion, not promoted to novelty.

## Companion arithmetic conjecture: full ordinary routine bridge, credit0

Tian0910.1576v1 Conjecture13 asks whether some uniform N exists so that
for all n>=N and all even m>3,

    (m^{v_m((m-1)^n-1)})² <= (m-1)^n-1,

where v_m is the largest k>=0 for which m^k divides its argument; m need
not be prime. Elementary LTE proves N=32, so this is excluded as a routine
classical consequence, not proposed as a new arithmetic discovery.

Proof: Put z=(m-1)^n-1,k=v_m(z). If n is odd, z=-2 mod m, so k=0;
the inequality follows from z>=2. Suppose n even. If m has an odd prime
factor p of multiplicity a, LTE applied to ((m-1)^2)^(n/2)-1 gives
v_p(z)=a+v_p(n), since v_p(m-2)=0. If k>=1, ak<=a+v_p(n), hence
2^(k-1)<=p^(a(k-1))<=n. If m=2^a,a>=2, the2-adic LTE formula gives
v_2(z)=a+v_2(n), with the same conclusion2^(k-1)<=n. The case k=0
is trivial. Let j=floor(log2 n). Then k<=j+1. For n>=32,j>=5 and
4(j+1)<=2^j<=n; the first inequality holds at j5 and follows inductively.
Thus4k<=n. Also(m-1)^2>m for m>=4. Consequently
(m-1)^n > m^(n/2) >= m^(2k). Both outer quantities are integers, so
(m-1)^n-1>=m^(2k), as required. The integer subtraction step matters.
This proof covers all even composite bases, not only prime powers.
It is an auxiliary exclusion; there is no priority claim or separate count.

## Current proof screen, chronology and limits

The r7 complete cached current-head receipts, fetched2026-10-29T04:39UTC,
were reused as instructed; registry-screen.json retains exact commits,
hashes, completeness flags, entry counts and path matches. Omega D5 has
12435 paths, Problems1534, OpenAI preprints13578; count-ex-machina registry
was text-screened too. No Tian2009/Friedman-polynomial target path was found.
Broad matches are largely unrelated names/identities, not proof-body
clearance. These complete path lists are not full-text corpus searches.
No broad GitHub API traversal or fresh API request was made.

Live source bodies and targeted public search were checked before the
polynomial diagnostic work. Searches for Tian/Conjecture3/e-isolated returned
the original, its companion, and Bergman's older exercise and Wehrung's
lecture, not a located full proof. None certifies current open status.
MathDB's exact API request returned403 at05:17:16UTC; no subsequent request
to mathdb.com was made. Current MathDB solution/reply bodies therefore
remain UNREAD. No novelty clearance is asserted. Main source PDF and HTML
both retain Conjecture3; arXiv submission metadata says8October2009, while
the retrieved PDF title date says12June2018 and HTML says24August2026.
These inconsistent rendered dates are preserved, not treated as new
publication or proof chronology. Hashes pin the bytes actually read.

The retained full target is unresolved. No PROOF.md, paper, formalization,
independent review, acceptance or new count is nominated.
