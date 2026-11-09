# H013 — Global-resultant tail: a charged population obstruction

Date: 2026-10-08. Revised round following the full
[W001 Card C](../hypotheses/W001-relations.md),
[H008 proposal](H008-resultant-selector.md), and
[H008 independent review](H008-independent-review.md).

**Disposition: reject the specified full-cube selector as a route through the
stated eta = 2/5, unchanged-smoothness cost inequality.** A distribution-free
integer-point bound supplies a mandatory tail penalty

\[
 \boxed{\tau\ \ge\ \min\left(a_0,\frac{6}{5\delta^2}\right).}       \tag{1}
\]

Substitution into the requested inequality makes every cost constant
\(c=\max(3a_0,2b_0)\le193/100\) impossible. In particular it cannot beat
the cited Coppersmith constant. This is a deliberately nonoptimal rejection
threshold, **not a factoring lower bound**, and does not prove a smoothness
upper bound for correlated selected norms. The count covers cancellation;
it does not assume that small resultants imply small actual height.

Indeed that implication is false: Section 5 constructs monic irreducible
base-m polynomials f and primitive irreducible quadratics g with
\(\operatorname{Res}(f,g)=1\) and **actual height = actual Mahler measure =
declared cube height H**. It supplies only one prescribed g for each specially
constructed f, not a useful population for a given input N.

The new counting proof and model rejection are self-contained informal
mathematics, **awaiting a new independent review**. No positive complexity
claim is made. Verified new factoring improvement remains **NONE**.

## 1. Scope, fixed selector, and evidence policy

Read AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md, research/STATE.md, and all three reports linked above.
The user's narrower assignment controls ownership and scope. This pass writes
only this report and `H013-resultant-provenance.json`; it does not edit shared
code, Lean, STATE, previous findings, or research protocols. There is no
delegation, installation, commit, publication, or scheduler.

Let f be monic of degree d >= 3, with integer coefficients of height A >= 1,
and N > 1. For the NFS interpretation f is irreducible, f(m) = N,
\(A=O(m)\), and \(\log m=(1+o(1))\log N/d\). The counting lemma below
does not require irreducibility, a base-m origin, or nonnegative coefficients.

The selector scans the coefficient cube and retains precisely the primitive
irreducible quadratics

\[
 g=aX^2+bX+c,\qquad 1\le a\le H,\quad |b|,|c|\le H,
\]

for which

\[
 |\operatorname{Res}(f,g)|^{5d}N^6\le C_0^{5d},
 \qquad C_0=(3H)^d(d+1)A^2.                              \tag{2}
\]

Equivalently, with real notation used only in the proof,

\[
 |\operatorname{Res}(f,g)|\le T,
 \qquad T=C_0N^{-6/(5d)}.                                \tag{3}
\]

Membership (2) is an integer comparison, including equality; no floating
equality or evaluation at approximated roots is needed. One can scan all
\((2H+1)^3\) triples and explicitly reject a <= 0, or scan just the
\(H(2H+1)^2\) positive-leading triples. Both implementations have the same
leading scan exponent 3a0 and charge every tuple they visit, including gcd,
discriminant, and resultant failures. Primitive quadratic irreducibility is
exactly the condition that \(b^2-4ac\) is not a nonnegative integer square.

**No finite counting run is needed or performed. Experimental allocation:
0 seconds; no grid, seeds, trials, partial cases, or unstarted cases.** The
analytic upper bound decides the requested inequality for the entire stated
asymptotic regime. This choice avoids interpreting admission in a tiny-d,
slack-C0 example as evidence of asymptotic density. No executable selector or
independent Sylvester validation is claimed. The suggested scalar resultant
recurrence is not used as an oracle or an input to this proof.

Primary-source checks and local input/report hashes are recorded in the
adjacent provenance file. Hash/provenance writing is documentation work,
not an experimental parameter search. No code was changed, so the project
code/Lean checks were not run.

## 2. An exact bound for the global sublevel set

Write

\[
 \epsilon=N^{-6/(5d^2)}.
\]

This epsilon is **not a per-embedding constraint**. It appears as the d-th
root of the requested global damping. We prove

\[
 \#\{(a,b,c)\in[-H,H]^3\cap\mathbb Z^3:
          |\operatorname{Res}(f,aX^2+bX+c)|\le T\}
 \ \le\ \operatorname{poly}(d)\,(H^3\epsilon+H^2).       \tag{4}
\]

The resultant in (4) is evaluated by its monic-f root product, which remains
defined for degree-one or constant g. Thus (4) is an upper bound for the
selector before its primitive, positive-leading, and irreducible filters.
Repeated roots or zero resultants cause no exception to this bound.

### 2.1 A one-variable sublevel lemma

Let P be any complex polynomial of exact degree d and nonzero leading
coefficient L. Factor it over C as

\[
 P(z)=L\prod_{j=1}^d(z-z_j).
\]

If \(|P(k)|\le T\) for a real integer k, then at least one factor satisfies

\[
 |k-z_j|\le\rho:=(T/|L|)^{1/d}.
\]

For each j the real points satisfying this disk condition lie in an interval
of length at most 2rho. Such an interval contains at most
\(\lfloor2\rho\rfloor+1\le2\rho+1\) integers. Taking the union gives

\[
 \#\{k\in\mathbb Z:|P(k)|\le T\}\le d(2\rho+1).          \tag{5}
\]

This argument uses neither root separation nor any distribution hypothesis.
Roots are used in a proof, not computed by a proposed algorithm.

### 2.2 Integer coefficient lines with a large leading resultant

Choose a nonnegative integer s with f(s) != 0. Partition triples into the
integer lines labeled by

\[
 \beta=b+2sa,\qquad\gamma=c-s^2a.
\]

On such a line,

\[
 g=a(X-s)^2+\beta X+\gamma,
\]

and every integer triple has exactly one integer pair (beta,gamma) and one
integer parameter a. There are at most

\[
 J_s=\big(2(1+2s)H+1\big)\big(2(1+s^2)H+1\big)          \tag{6}
\]

labels for lines meeting the cube. Counting impossible labels only enlarges
this upper bound.

For each line, let

\[
 P_{\beta,\gamma}(z)
  =\operatorname{Res}\big(f,z(X-s)^2+\beta X+\gamma\big).
\]

If alpha_1,...,alpha_d are the roots of the monic f, counted with
multiplicity, this polynomial is

\[
 \prod_{i=1}^d\big(z(\alpha_i-s)^2+\beta\alpha_i+\gamma\big).
\]

Its coefficient of z^d is

\[
 \prod_i(\alpha_i-s)^2=f(s)^2\ne0.                       \tag{7}
\]

In particular every line polynomial has **exactly degree d**, even if some
points on that line have zero resultant. Applying (5) and (6) proves the
explicit bound

\[
 \boxed{\#S\le J_s d\left(1+
 6H(d+1)^{1/d}\left(\frac{A}{|f(s)|}\right)^{2/d}
 N^{-6/(5d^2)}\right).}                                \tag{8}
\]

Here S may be the whole sublevel set in (4) or any of its filtered subsets.
The line direction (X-s)^2 is an auxiliary counting direction. The counted
g's are not assumed reducible, proportional to that direction, or of small
Mahler measure. Correlations between f and g change the roots of P but do
not change its nonzero leading coefficient (7).

### 2.3 Ordinary nonnegative base-m digits: s = 1 suffices

For a monic f with nonnegative coefficients, f(1) >= A. Take s = 1 in
(8). Since \((d+1)^{1/d}\le2\),

\[
 \#S\le d(6H+1)(4H+1)\big(1+12H\epsilon\big).           \tag{9}
\]

This already proves (4) for the ordinary base-m polynomial. No assumptions
about the locations of its embeddings or its constant digit are needed.

### 2.4 Signed coefficients: a uniformly cheap direction also exists

For completeness the result does not depend on the digit-sign convention.
Interpolate f at 0,1,...,d. For the Lagrange basis

\[
 L_j(X)=\frac{\prod_{0\le k\le d,\ k\ne j}(X-k)}
                  {\prod_{k\ne j}(j-k)},
 \qquad f=\sum_{j=0}^d f(j)L_j,
\]

its coefficient l1 norm is at most

\[
 \|L_j\|_1\le\frac{(d+1)!}{(j+1)j!(d-j)!}
              =(d+1)\frac{\binom dj}{j+1}.
\]

The sum of these bounds is \(2^{d+1}-1\), by integrating (1+x)^d
from 0 to 1 and multiplying by d+1. Consequently

\[
 A\le\|f\|_1\le(2^{d+1}-1)\max_{0\le j\le d}|f(j)|.
\]

Choose a maximizing s. Its value is nonzero, and
\((A/|f(s)|)^{2/d}<2^{2+2/d}\le8\). Moreover s <= d. Substitution
into (8), using H >= 1, yields the completely explicit version

\[
 \boxed{\#S\le
 d(4d+3)(2d^2+3)H^2\big(1+96H\epsilon\big).}            \tag{10}
\]

The particular constants are intentionally loose. Finding s, if desired,
requires d+1 ordinary integer evaluations with polynomial bit work. The
argument is a count, however, not a claim that its small sublevel intervals
can be located or enumerated at that cost. It introduces no free lattice
reduction or output-sensitive enumeration oracle.

## 3. The mandatory tail cost rules out the requested inequality

Use exactly the scaling from Card C, with a0,b0 reserved for L constants:

\[
 t=\log N,\quad\ell=\log t,\quad
 D=t^{1/3}\ell^{2/3},
\]
\[
 \log H=(a_0+o(1))D,\qquad
 \log B=(b_0+o(1))D,\qquad
 d=(\delta+o(1))(t/\ell)^{1/3}.
\]

In particular

\[
 \epsilon=\exp\left[-\left(\frac{6}{5\delta^2}+o(1)\right)D\right].
\]

All polynomial factors in d in (10) have logarithm o(D). The number of
retained elements is therefore at most

\[
 \exp\left[\left(
  \max\left(3a_0-\frac{6}{5\delta^2},2a_0\right)+o(1)
 \right)D\right].                                      \tag{11}
\]

Relative to the charged H^3 coefficient population, its fraction is at most
\(L_N[1/3,-\min(a_0,6/(5\delta^2))]\), proving (1). Constant-factor
differences between cube conventions do not change this conclusion. If
there are fewer survivors or none, the necessary penalty is larger.

Now suppose the user-specified model were feasible:

\[
 3a_0\ge b_0+\tau+
 \frac{K/\delta+a_0\delta}{3b_0},
 \qquad K=14/5,\quad a_0,b_0,\delta>0.                 \tag{12}
\]

Let x = 3a0 and c = max(x,2b0). By AM-GM twice,

\[
 x-\tau\ge
 b_0+\frac{2\sqrt{Ka_0}}{3b_0}
 \ge\left(\frac{64Kx}{27}\right)^{1/4}.                 \tag{13}
\]

Since tau >= 0, this already forces

\[
 x\ge x_*:=\left(\frac{64K}{27}\right)^{1/3}
           =\left(\frac{896}{135}\right)^{1/3}
           >187/100.                                  \tag{14}
\]

Dropping positive terms in (12), but retaining b0 and the a0-delta term,
also gives

\[
 \delta\le\frac{3b_0(3a_0-b_0)}{a_0}
        \le\frac{27a_0}{4}=\frac{9x}{4}\le\frac{9c}{4}. \tag{15}
\]

Assume for contradiction c <= 193/100. From (14), a0 > 187/300 > 3/50.
From (15),

\[
 \frac{6}{5\delta^2}\ge\frac{32}{135c^2}
 \ge\frac{320000}{5028615}>\frac3{50}.                  \tag{16}
\]

Thus (1) forces tau > 3/50. But (13) and (14) imply

\[
 x-\tau\ge x_*>187/100,
\]

whereas x <= c <= 193/100 implies

\[
 x-\tau<193/100-3/50=187/100.
\]

This is a contradiction. The comparisons have fixed strict margins, so
the o(1) terms in the L notation do not repair the asymptotic feasibility.
No numerical optimizer, fitted count, or approximate equality is used.

The cited value
\(c_C=((92+26\sqrt{13})/27)^{1/3}\) is below 193/100;
even ordinary GNFS's \((64/9)^{1/3}\) is below that threshold.
The formula and its square-congruence scope were checked in
[Lee–Venkatesan, Remark 4.31](https://arxiv.org/html/1805.08873v1).
This report does not reinterpret that source as an unconditional general
factoring theorem.

**What is rejected:** (2), scanned at exponent 3a0, cannot meet (12) with
the proposed improvement in c. The elementary counting bound is unconditional;
the inference involving the smoothness term in (12) is a contradiction
*inside that supplied model*. A different joint smoothness law, rational
size law, collection target, costed enumerator, or multiple-field scheme
would require a genuinely different analysis. No universal bound on
smoothness, useful row rank, or proper-factor probability follows from (11).

## 4. Actual height and Mahler measure: the easy gain is already paid for

For a quadratic g, let h be its actual maximum coefficient magnitude and
M(g) its Mahler measure. From its two roots and the triangle inequality,

\[
 h/2\le M(g)\le\|g\|_2\le\sqrt3\,h.                  \tag{17}
\]

The upper Mahler/l2 inequality and coefficient estimates are also recorded
in [Abbott, Sections 2 and 3.2](https://arxiv.org/pdf/0904.3057).
The lower bound here follows directly: the leading and constant coefficients
have absolute value <= M(g), and the middle coefficient has absolute value
<= 2M(g). Thus for fixed quadratic degree, actual coefficient height and
actual Mahler measure have the same L constant, although either can be much
smaller than a *declared* cube height H.

The deterministic norm bound with actual height h is

\[
 |\operatorname{Res}(f,g)|\le(3h)^d(d+1)A^2.
\]

Hence taking h <= H epsilon is a sufficient way to meet (2), but the
containing coefficient cube has only O((1+H epsilon)^3) points. If
H epsilon grows on the L scale, its tail penalty is
\(18/(5\delta^2)\), three times the minimum penalty used in (1).
If H epsilon < 1 it contains no genuine integer quadratic. For actual
Mahler measure, rootwise

\[
 |g(z)|\le M(g)(1+|z|)^2\le4M(g)\max(1,|z|)^2,
\]

so M(g) <= (3/4)H epsilon is another sufficient condition; (17) gives
the same population exponent. Directly enumerating that smaller cube would
change the declared generator and its cost. Counting the old H^3 population
while assigning every member the smaller norm bound is invalid.

These are sufficient low-height constructions, **not necessary conditions
for admission**. In particular (17) does not imply a norm lower bound.
The universal bound (10) is weaker than the small-height cube bound because
it also allows correlated cancellation and integer points concentrated near
the roots of the line polynomials.

Finally, for tiny d the factor 3^d(d+1) and the possible looseness of A^2
relative to the actual root product can dwarf the requested damping. A
finite admission fraction without actual h/M(g) information and a slack
audit would not validate the target asymptotic model. No such finite
fraction is reported here.

## 5. Explicit cancellation with full actual height

Fix an even d >= 6, an integer u >= 5 with u = 1 modulo 4, and K0 >= 1.
K0 here is a construction parameter, unrelated to the constant K in (12).
Define

\[
 g=X^2+u,\qquad
 q=\sum_{j=0}^{d/2-1}X^{2j}+2K_0X^{d-4},\qquad f=gq+1. \tag{18}
\]

All of these are explicitly constructible by polynomial multiplication.
The quadratic is primitive and irreducible over Q because its discriminant
is negative. Its two roots have magnitude sqrt(u), so

\[
 H=u,\qquad h(g)=u,\qquad M(g)=u.                        \tag{19}
\]

The polynomial f is monic of degree d. Modulo 2, the geometric sum gives

\[
 f\equiv (X^2+1)(1+X^2+\cdots+X^{d-2})+1=X^d.
\]

Its constant coefficient is u+1 = 2 modulo 4, since d-4 >= 2. This proves
Eisenstein irreducibility at 2. Explicitly, a monic integer factorization
would reduce modulo 2 to two positive-degree monomials; both constant
coefficients would be even, contradicting 4 not dividing f(0).

The coefficients of f are nonnegative, its odd coefficients vanish, and
its exact height is

\[
 A=2K_0u+u+1.                                         \tag{20}
\]

Put m = A+2 and N = f(m). Every coefficient is a base-m digit. Moreover
the coefficient of X^(d-1) is zero, so

\[
 m^d<N<m^d+m^{d-1}<(m+1)^d.
\]

Thus m is exactly floor(N^(1/d)), not just a nearby chosen base;
f is the ordinary monic base-m polynomial of this N, and A = m-2.
N is even and larger than 2, so it is a composite input. Its easy factor
is irrelevant: this is a structural counterexample, not a factoring
speed example or an N-only method for constructing a field for arbitrary N.

At both roots beta of the monic g, f(beta) = 1. Since the degrees d and 2
have even product, the root-product resultant identity gives

\[
 \operatorname{Res}(f,g)=\operatorname{Res}(g,f)
                       =\prod_{g(\beta)=0}f(\beta)=1.   \tag{21}
\]

It is admitted by (2): N < (m+1)^d, A >= 16, and m+1 = A+3 < 2A yield

\[
 T>(3u)^d(d+1)A^2/(2A)^{6/5}>1.
\]

Increasing K0 makes A arbitrarily larger than u. Thus the cancellation is
not an artifact of identifying the field-polynomial height A with the
quadratic height H. The construction provides a known high-measure unit
g(theta), not a large collection of useful relations. It starts from g
and builds a special N, while the factoring contract gives only an existing
N. It supplies **one** certified member per constructed f and no lower
density for the rest of that f's cube. Its construction uses O(d)
coefficient work and polynomial bit work in the displayed inputs, but a
full scan of that fixed cube still costs H^3 visits as stipulated.

The norm identity and use of resultants for higher-degree elements are
standard background; see
[Stevenhagen, Section 3](https://pub.math.leidenuniv.nl/~stevenhagenp/ANTproc/04psh.pdf).
Neither that source nor this example supplies a new smoothness or
factor-extraction theorem. No factor library, hidden factor data, or
integer norm factorization is used in (18)–(21).

## 6. Exact selection cost and limits of the conclusion

A straightforward executable version of (2) can use an exact Sylvester
determinant per primitive irreducible quadratic. Polynomial-bit fraction-free
elimination is sufficient; faster scalar recurrences are optional and cannot
reduce the mandatory H^3 scan in this proposal. The resulting selector
description costs H^3 poly(n,d,log A,log H) bit work, where n is the bit
length of N. Integer powers and the comparison (2) also have polynomial
operand widths: even their deliberately unreduced exponents give widths
O(d^2 log(2H) + d log(2A) + n). This is a cost description, not a benchmark
or a claim that a particular unimplemented recurrence was tested.

The proof's coefficient lines are not a replacement generator. It does not
charge only survivors, drop rejected tuples, or presume that the roots of
all its line polynomials are free to obtain. The O(H^2) term in (4) is
essential: intervals shorter than one can still contain a lattice point.
Deleting it would wrongly assert that all exceptional cancellations have
continuous-volume density.

No smoothness processing was performed. If S survivors are processed by
ordinary trial division through B, budget S B poly(n) worst-case work,
in addition to the H^3 scan, base construction, and all setup. In an L
model with S = L[1/3,s], this gives the conservative processing exponent
s+b0 and total selector/processing envelope max(3a0,s+b0). The looser
H^3 B bound is also valid. One must not remove the B factor without
specifying and charging an appropriate sieve or batch algorithm. Proving
a better bound than this conservative trial-division charge would not
remove the counting obstruction to the original (12).

Rational and ideal smoothness, exceptional ideals, signs and characters,
matrix rank and filtering, algebraic square roots, and proper-factor
success remain separate obligations. For a completed trial costing Ttrial
with useful-splitting probability sigma_N, independent-restart expected
cost must include Ttrial/sigma_N. This report supplies no bound on sigma_N.

The theorem concerns this global threshold for a fixed f and the supplied
population/smoothness model. It does not reinstate H008's one-per-embedding
bound, make a false d-rank claim, preclude isolated units such as (18), or
prove that all global-resultant ideas fail. A method exploiting much smaller
norms with a different joint distribution must count those strata and pay
for selecting them; the present single-threshold model cannot stand in
for that analysis.

## 7. Sources, disposition, and next decisive action

The primary texts directly opened in this round were Abbott's *Bounds on
Factors in Z[x]* (Sections 2 and 3.2), Lee–Venkatesan's *Rigorous Analysis
of a Randomised Number Field Sieve* (Remark 4.31), and Stevenhagen's
*The number field sieve* (Sections 3–4, including the ordinary base-m
construction). Their URLs and the input/report hashes are in
`H013-resultant-provenance.json`. The sublevel-line proof, interpolation
bound, constant contradiction, and explicit example are proved here;
no external source is cited as certifying them or their novelty.

**Best supported full-work claim:** every full scan pays H^3 tuple visits,
the exact test adds polynomial-bit overhead, and its survivor population
satisfies (10). This is incompatible with
the requested eta = 2/5 leading-constant improvement under (12), even
before downstream costs are added. The conditional model rejection does
not assert a new general lower or upper bound on factoring.

**Next decisive action for the coordinator:** obtain a new independent
review of (5)–(10), the interpolation bound, the mandatory tau mapping,
the inequalities (13)–(16), and the exact floor-base/Eisenstein example.
If accepted, close this particular full-scan plus unchanged-smoothness
model. Reopen only with a concrete changed mechanism—such as a costed
enumerator or a proved joint norm/smoothness distribution—with its new
population and completion costs. No recursive review was launched here.

Verified improvement remains **NONE**.
