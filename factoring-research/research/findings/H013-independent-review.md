# H013 — Independent review of the global-resultant selector

Date: 2026-10-08. New independent review round of the frozen
[H013 report](H013-global-resultant.md) and
[provenance](H013-resultant-provenance.json), with the full
[W001 relations report, including Card C and shared accounting](../hypotheses/W001-relations.md),
[H008 proposal](H008-resultant-selector.md),
[H008 independent review](H008-independent-review.md), and
[parent disposition](H008-disposition.md).

**Disposition: accept the global counting proof, the eta = 2/5 model rejection,
and the full-height cancellation example, with their stated restricted scope.**
No mathematical correction to the frozen H013 report is required. Its count is
unconditional; its leading-constant rejection is conditional on the supplied
population, smoothness, and cost model. It is not an upper bound on the number
of useful smooth survivors obtained by multiplying a count by an assumed
smoothness probability.

The optional extension can also be decided analytically: in the specified
general-eta relaxation, **every eta in [0,1] is infeasible when c <= 2**, hence
when c <= c_C. Section 7 supplies the proof without a parameter sweep. This
is a new reviewer derivation, not an independently reviewed or Lean-verified
extension. It does not close changed joint smoothness models or changed,
explicitly costed generators.

Verified new factoring complexity improvement: **NONE**.

## 1. Review boundary and evidence

Read AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md, research/STATE.md, and all reports linked above in full.
The assignment's narrower scope controls: this review owns only this file and
`H013-review-*`. No proposer evidence, shared code, Lean, STATE, protocols or
task registry was edited. There was no package installation, delegation,
commit, publication, scheduler, finite factoring/counting experiment, or
parameter search. Experimental allocation and number of experimental runs
are both zero. Documentation hashing is not an experimental run.

At the initial review capture, all nine initial and all nine final input
hashes in the proposer manifest matched the files read here. The report
SHA-256 also matched:
`6ecb3ccd3ae78f84300251b3329878edc30930690c87edde9924f04183dfe59a`.
The parent H008 disposition and proposer provenance file were additionally
hashed as review inputs. Initial/final hashes, source-check details, and this
review's hash are recorded in [H013-review-provenance.json](H013-review-provenance.json).
These hashes establish version correspondence, not correctness of proofs.
At final capture, research/STATE.md had changed in the shared workspace;
this reviewer did not edit it. Its initial and final hashes are retained.
All other review inputs, including both frozen H013 artifacts and every
mathematical report under review, remained unchanged.

H008 remains closed only for the stipulated thin single-embedding population
of primitive irreducible quadratics. Its reducible branch requires the reviewed
linear-factor and parity accounting; it does not have a d-row or d-rank bound.
H013 changes the admission condition and must be judged on its own count.
The H013 proof does not reapply H008's separation threshold to global norms.

## 2. Exact threshold, norm bound, and line count

Assume d >= 3, H >= 1 an integer, f monic of degree d and integer height A.
For the NFS interpretation, retain the stated monic irreducible ordinary
base-m setting. The counting theorem needs neither that interpretation nor
irreducibility of f. Let

\[
 C_0=(3H)^d(d+1)A^2,\quad
 T=C_0N^{-6/(5d)},\quad \epsilon=N^{-6/(5d^2)}.
\]

Because N and C0 are positive, taking a positive 5d-th root proves the exact
equivalence between the integer test and |Res(f,g)| <= T. Equality is admitted;
there is no strict-threshold or rounding substitution at this step.

For any g of height h and degree at most two, at a complex number z,

\[
 |g(z)|\le h(1+|z|+|z|^2)\le3h\max(1,|z|)^2.
\]

Multiplication over the d roots of monic f, with multiplicities, gives

\[
 |\operatorname{Res}(f,g)|\le(3h)^dM(f)^2
 \le(3h)^d\|f\|_2^2\le(3h)^d(d+1)A^2.                 \tag{R1}
\]

The Mahler/l2 inequality follows by averaging log|f| on the unit circle,
using concavity of log and the identity for the integral of |f|^2. Unit-circle
zeros are handled by the usual limiting integral. It also appears in
[Abbott, Sections 2 and 3.2](https://arxiv.org/pdf/0904.3057).
This is an upper bound, not a typical-size assertion or a lower bound.
Repeated roots of f and vanishing evaluations do not invalidate it.

**One-dimensional lemma.** For exact degree d, nonzero leading coefficient L,
and T >= 0, write P(z) = L product_j(z-z_j), counting root multiplicities.
If all |k-z_j| exceeded rho = (T/|L|)^(1/d), their product would exceed
T/|L|. Thus |P(k)| <= T puts k in at least one of the closed disks of radius
rho. Each disk meets the real axis in an interval of length at most 2rho,
possibly empty, containing at most floor(2rho)+1 integers. Therefore

\[
 \#\{k\in\mathbb Z:|P(k)|\le T\}\le d(1+2\rho).      \tag{R2}
\]

Multiplicity only repeats disks and weakens the union bound. At T = 0 this
reduces to at most d distinct integer zeros. Neither separation nor a random
root distribution is assumed. The leading coefficient must be nonzero;
H013 supplies that condition for every line.

Choose a nonnegative integer s with f(s) != 0. The integral change of
coordinates

\[
 (a,b,c)\longleftrightarrow(a,\beta=b+2sa,\gamma=c-s^2a)
\]

is bijective, with g = a(X-s)^2 + beta X + gamma. A line meeting the full
coefficient cube has
|beta| <= (1+2s)H and |gamma| <= (1+s^2)H. Hence the number of its possible
labels is at most

\[
 J_s=(2(1+2s)H+1)(2(1+s^2)H+1),                      \tag{R3}
\]

which is O((1+s)^3 H^2). The parameter a values lying in the cube can safely
be enlarged to all integers when applying (R2).

The line polynomial is

\[
 P_{\beta,\gamma}(z)
 =\prod_{i=1}^d\big(z(\alpha_i-s)^2+\beta\alpha_i+\gamma\big).
\]

Its leading coefficient is product_i(alpha_i-s)^2 = f(s)^2, a nonzero
integer. It has exact degree d even with repeated alpha_i or special
beta,gamma. In particular a line cannot be identically zero because some
of its points have zero resultant. Substituting L = f(s)^2 and T into (R2)
gives precisely

\[
 \#S\le J_s d\left(1+6H(d+1)^{1/d}
          (A/|f(s)|)^{2/d}\epsilon\right).             \tag{R4}
\]

This bounds the entire cube, including reducible, imprimitive, zero, and
lower-degree g. Using the monic-f product definition consistently avoids
degree-drop ambiguities for g. The primitive irreducible positive-leading
subset is consequently bounded too. If f itself is irreducible and d > 2,
a nonzero quadratic cannot have zero resultant. For reducible f, zero
resultants remain covered by the count; they are not thereby usable field
relations.

For ordinary nonnegative digits, f(1) >= A, so s = 1 yields
d(6H+1)(4H+1)(1+12H epsilon), as asserted. No hypothesis about real roots
or the constant digit is needed.

For signed coefficients, Lagrange interpolation at 0,...,d gives

\[
 \|L_j\|_1\le\frac{(d+1)!}{(j+1)j!(d-j)!},\qquad
 \sum_{j=0}^d\|L_j\|_1\le2^{d+1}-1.
\]

The first bound follows by multiplying coefficient l1 norms of X-k and
dividing by j!(d-j)!. The sum follows from integrating (1+x)^d over [0,1].
Thus A <= ||f||1 <= (2^(d+1)-1) max_j |f(j)|. A maximizing s is nonzero
in value, has s <= d, and satisfies (A/|f(s)|)^(2/d) < 8. Along with
(d+1)^(1/d) <= 2 and H >= 1, (R3) becomes
J_s <= (4d+3)(2d^2+3)H^2. Therefore

\[
 \boxed{\#S\le d(4d+3)(2d^2+3)H^2(1+96H\epsilon).}    \tag{R5}
\]

Every constant and inequality in this derivation checks. The potentially
exponential interpolation factor is harmless here because it is raised
to 2/d; it was not silently discarded as polynomial. Evaluating the d+1
integer arguments has polynomial bit cost, but neither the evaluations nor
the proof provide a cheap enumerator of the sublevel points on all lines.

The H^2 term cannot be discarded on the ground that intervals have tiny
length: they can still contain integers. With reducible f, exact common-factor
planes can even give that scale of zero resultants. The proof is a lattice
point bound, not a continuous-volume density approximation.

## 3. Exponent mapping and the eta = 2/5 contradiction

Use fixed positive constants a0,b0,delta and
D = (log N)^(1/3)(log log N)^(2/3). Under the stipulated scaling,

\[
 \epsilon=\exp(-(6/(5\delta^2)+o(1))D),\qquad
 \log\operatorname{poly}(d)=o(D).
\]

Consequently (R5) gives a survivor exponent at most

\[
 s\le\max(2a_0,3a_0-6/(5\delta^2)).
\]

Relative to the charged full H^3 population this is exactly the necessary
loss

\[
 \tau\ge\min(a_0,6/(5\delta^2)).                       \tag{R6}
\]

If an asymptotic survivor exponent does not exist, the same statement holds
as an upper exponential envelope for the count; it does not require a
matching lower count. Zero survivors only strengthen the obstruction.
Primitive and irreducibility filters cannot enlarge the population.

At the larger norm-log scale E = (log N)^(2/3)(log log N)^(1/3), (R1)
and the global damping give an algebraic upper coefficient
a0 delta + 4/(5 delta). The rational bound |g(m)| <= 3Hm^2 has coefficient
2/delta; log H contributes only lower order on this side. Their combined
coefficient is a0 delta + 14/(5 delta), verifying the eta = 2/5 mapping.
The factors 3^d and d+1 are lower order. An atypically smaller actual A or
actual norm may change a distribution model; an upper bound alone does not
license treating these main scales as typical.

Now assume the supplied feasibility inequality, not a theorem about
selected smooth values. Put x = 3a0 and K = 14/5. Two AM-GM applications give

\[
 x-\tau\ge b_0+\frac{2\sqrt{Ka_0}}{3b_0}
       \ge(64Kx/27)^{1/4}.
\]

Since tau >= 0, x >= x_* = (896/135)^(1/3) > 187/100.
The latter strict comparison follows by cubing positive rationals.
Also, dropping positive terms while retaining b0 and a0 delta/(3b0),

\[
 \delta\le3b_0(x-b_0)/a_0
       \le9x/4\le9c/4.
\]

For c <= 193/100, this implies

\[
 6/(5\delta^2)\ge32/(135c^2)
 \ge320000/5028615>3/50,
\]

while a0 > 187/300 > 3/50. Thus (R6) forces tau > 3/50. Monotonicity of
(64Kx/27)^(1/4) and x >= x_* gives x-tau >= x_* > 187/100. But x <= 193/100
gives x-tau < 187/100, a contradiction. Strict signs, constants, and powers
are correct. The positive gaps absorb asymptotic o(1) terms; equality at the
integer selector threshold does not repair the leading-constant model.

The comparison constant and its square-congruence scope are stated in
[Lee–Venkatesan, Remark 4.31](https://arxiv.org/html/1805.08873v1).
The asserted rejection threshold exceeds both c_C and the ordinary GNFS
constant. This does not turn either reference into an unconditional theorem
for factoring arbitrary inputs.

**Scope that must be retained:** (R5) and (R6) are unconditional population
statements in their stated scaling. Multiplying that count by the usual
smoothness heuristic is not a rigorous bound on useful smooth survivors.
The report correctly labels the infeasibility calculation as internal to
the unchanged model. Selected units, other highly smooth concentrations,
or different rational/ideal correlations could violate that model; they
would require new yield and cost analysis. Nothing here proves a factoring
lower bound or an unconditional probability estimate.

## 4. Actual height and the special family

For a genuine quadratic, the leading and constant coefficients have
absolute value at most M(g), and the middle one at most 2M(g). Thus
h/2 <= M(g) <= ||g||2 <= sqrt(3)h. Coefficient height and Mahler measure
have the same L constant at this fixed degree. They need not be comparable
to a declared larger cube height.

From (R1), h <= H epsilon is sufficient for admission because
epsilon^d = N^(-6/(5d)). It supplies at most O((1+H epsilon)^3) coefficient
tuples. When log(H epsilon)/D tends to a positive constant, the relative
loss is 18/(5 delta^2), as claimed; if H epsilon < 1 there is no genuine
integer quadratic in that cube. At the boundary of zero exponent the
population is at most sub-L scale, not a positive-volume family. The
rootwise bound |g(z)| <= M(g)(1+|z|)^2 similarly verifies the sufficient
condition M(g) <= (3/4)H epsilon. None of these sufficient conditions is
necessary.

For the proposed counterexample let d >= 6 be even, u >= 5 with u = 1
modulo 4, and K0 a positive integer. Then

\[
 g=X^2+u,\quad q=\sum_{j=0}^{d/2-1}X^{2j}+2K_0X^{d-4},\quad f=gq+1.
\]

The discriminant of g is -4u, so it is primitive irreducible with positive
leading coefficient and h(g) = M(g) = H = u. The leading coefficient of f
is one. Its constant coefficient is u+1; the two increased interior
coefficients are u+1+2K0 at X^(d-2) and u+1+2K0u at X^(d-4). All remaining
nonzero interior coefficients are u+1. The exponents remain distinct and
interior even at d = 6. Therefore its exact height is
A = u+1+2K0u, all digits are nonnegative, and its X^(d-1) coefficient is zero.

Modulo 2 the geometric sum telescopes, giving f = X^d. Its constant
coefficient is 2 modulo 4. Hence f is Eisenstein at 2 and irreducible.
No irreducibility of q is needed.

Set m = A+2. All coefficients are less than m, and explicitly

\[
 0<N-m^d\le A\sum_{i=0}^{d-2}m^i
       =A\frac{m^{d-1}-1}{m-1}<m^{d-1}.
\]

Thus m^d < N < m^d+m^(d-1) < (m+1)^d, proving the exact floor-root
condition, not merely an asymptotic base choice. Both A and m are even,
so N is even and greater than two (in fact N = 2 modulo 4).

At both roots of monic g, f is one. The sign in swapping resultants is
(-1)^(2d) = 1, so Res(f,g) = Res(g,f) = 1. Finally N < (A+3)^d < (2A)^d
and A >= 16 give

\[
 T>(3u)^d(d+1)\frac{A^2}{(2A)^{6/5}}>1.
\]

For example the final A-dependent factor is at least 4 at A >= 16, so
there is ample strict margin. Every member of the family is admitted.
Taking K0 large makes A/H arbitrarily large; for fixed d,u it also sends
H epsilon to zero while this full-height g persists. This rigorously
refutes a universal necessary-low-height implication.

It does not give useful density, a generator for an arbitrary supplied N,
or an improved factoring algorithm. Only one prescribed g is certified
per constructed f. The easy even factor and special construction are
disclosed. The family is a structural counterexample, not evidence that
the NFS asymptotic population model is realized on general inputs.

## 5. Construction and completion costs

The scan visits H(2H+1)^2 positive-leading triples, or (2H+1)^3 triples
before sign rejection. Both have exponent 3a0. Gcd/primitivity and the
integer discriminant-square test are polynomial bit work per visited
tuple. For primitive quadratics, failure of the nonnegative-square
discriminant condition is exactly irreducibility over Q.

An exact Sylvester determinant of order d+2, computed with pivoting and
exact elimination, suffices for membership. Bounds on minors give
polynomial operand widths and polynomial bit work in d, log A and log H.
The special determinant structure is not needed for that complexity
claim. In the final power comparison, the widths are

\[
 O(d^2\log(2H)+d\log(d+1)+d\log(2A)+\log N).
\]

The d log(d+1) term is absorbed by d^2 log(2H), so the report's shorter
bound is valid. This accepts a costed mathematical specification; no
implementation, scalar O(d) recurrence, determinant cross-check, or
benchmark was performed. The optional unverified recurrence is unnecessary
to either the proof or the H^3 scan charge.

The line proof does not enumerate its intervals or price computing all
their polynomials, roots, integer endpoints, and outputs. It supplies no
free output-sensitive generator. A changed generator would require an
explicit construction and a fresh cost/population analysis.

For S survivors, ordinary rational-value and integer-norm trial division
through B costs at most S B times polynomial bit overhead in the stipulated
NFS scaling, in addition to base construction and the scan. Thus the
report's conservative exponent max(3a0,s+b0) is a valid processing envelope
when S has exponent s. It does not include ideal decomposition or complete
factor extraction, and an upper bound on S does not prove processing needs
that much work. A better sieve/batch charge must actually be specified
before claiming the optimistic processing cost in Card C.

The usual separate obligations remain: distinct prime ideals, exceptional
data, signs/characters, useful rank, filtering and storage, algebraic square
roots, proper-factor success and restarts. Norm parity is not enough for
an algebraic square; see
[Stevenhagen, Sections 4–10](https://pub.math.leidenuniv.nl/~stevenhagenp/ANTproc/04psh.pdf).
There is no lower bound on the proper-splitting probability sigma_N here.
The expected independent-restart cost Ttrial/sigma_N cannot be suppressed.

## 6. Primary citations and limitations of verification

The three primary texts cited in H013 were independently opened and their
relevant passages checked:

- [Abbott, Sections 2 and 3.2](https://arxiv.org/pdf/0904.3057): Mahler
  measure, its l2 upper bound, and coefficient bounds. The quadratic and
  resultant inequalities used here also have the explicit derivations above.
- [Lee–Venkatesan, Remark 4.31](https://arxiv.org/html/1805.08873v1): the
  exact c_C formula and the statement about generating a square congruence.
  It is not used as a general unconditional factor-extraction theorem.
- [Stevenhagen, Sections 3–4](https://pub.math.leidenuniv.nl/~stevenhagenp/ANTproc/04psh.pdf):
  norms of higher-degree expressions via resultants, the ordinary floor-root
  base-m construction, and the distinction between square norms and squares.

The [original Coppersmith institutional publication record](https://research.ibm.com/publications/modifications-to-the-number-field-sieve)
was also opened; its abstract confirms the reuse of smoothness work across
polynomials. This review does not claim to have retrieved the complete
original Coppersmith article; the exact constant was checked in the
Lee–Venkatesan primary text. No cited source certifies the new line proof,
the special construction, or the extension below, and no novelty claim is
made. These are checked informal derivations, not formal machine-cost
theorems or Lean proofs.

## 7. Optional extension: tuning eta cannot rescue this relaxation

For eta in [0,1], put

\[
 q_\eta=2(1-\eta),\quad K_\eta=2(1+\eta),\quad
 \epsilon_\eta=N^{-q_\eta/d^2}.
\]

Replacing the damping by N^(-q_eta/d) in (R4)–(R5) proves
tau >= min(a0,q_eta/delta^2), including eta = 1 where this simply says
tau >= 0. The rational-plus-algebraic coefficient is
K_eta/delta + a0 delta. We therefore consider exactly the necessary
relaxation requested in the brief:

\[
 x=3a_0\ge F_\eta:=
 b_0+\min(x/3,2(1-\eta)/\delta^2)
       +\frac{2(1+\eta)/\delta+x\delta/3}{3b_0},
 \quad c=\max(x,2b_0).                                 \tag{R7}
\]

Larger actual losses only make it harder. We prove infeasibility already
under x <= 2, even without imposing b0 <= c/2.

For fixed x,b0,delta, F_eta is concave in eta: its only nonlinear term
is the minimum of a constant and an affine function. Hence
F_eta >= (1-eta)F_0 + eta F_1. It suffices to rule out both endpoints
for every fixed choice with x <= 2. This is an analytic endpoint reduction,
not an assumption that optimizing all parameters commutes with taking an
endpoint.

At eta = 1, tau's lower bound is zero and K = 4. The AM-GM calculation
already used in Section 3 yields x^3 >= 256/27 > 8, contradicting x <= 2.
Thus F_1 > x throughout this domain.

At eta = 0 there are two branches. If the minimum in (R7) is x/3,
the same AM-GM calculation with K = 2 gives

\[
 2x/3\ge(128x/27)^{1/4},\quad\text{so}\quad x^3\ge24>8,
\]

again impossible. Equality of the two arguments of the minimum is covered
by this branch as well.

In the remaining branch, assuming F_0 <= x gives

\[
 x\left(1-\frac{\delta}{9b_0}\right)
 \ge b_0+\frac2{\delta^2}+\frac2{3b_0\delta}>0.
\]

Therefore delta < 9b0, and increasing x to 2 preserves this necessary
inequality. Applying AM-GM in b0 then forces

\[
 2\ge\frac2{\delta^2}
       +\frac23\sqrt{2\delta+6/\delta}.                \tag{R8}
\]

For 0 < delta <= 2, the first term is at least 1/2. Also
2delta+6/delta >= 4sqrt(3) > 6, so the second term is greater than 3/2.
This contradicts (R8).

For delta >= 2, divide (R8) by 2 and square its nonnegative remaining
left side. The resulting necessary condition is

\[
 P(\delta):=2\delta^5-9\delta^4+6\delta^3+18\delta^2-9\le0.
\]

But, writing v = delta-2 >= 0, direct expansion gives

\[
 P(\delta)=2v^5+11v^4+v(14v^2-2v+1)+15v+31>0.
\]

Indeed 14v^2-2v+1 = 14(v-1/14)^2+13/14 > 0. This rules out the other
branch and establishes F_0 > x. Concavity now proves F_eta > x for every
eta in [0,1] when x <= 2.

Thus no admissible tuple in this relaxation has c <= 2. Since
sqrt(13) < 4 gives c_C^3 < 196/27 < 8, it certainly excludes c <= c_C.
This argument covers equality endpoints and uses no computed optimizer,
sample grid, or fitted constants. For any proposed asymptotic constants
the inequalities have a strict contradiction; the stronger threshold 2
also leaves a fixed margin around the requested c_C comparison. No claim
about parameter regimes outside the stated fixed-constant scaling is made.

**Scope of this new extension:** it excludes tuning a single global
threshold within (R7), with the full H^3 scan and the same conditional
norm/smoothness/population accounting. It is not a density theorem for
useful smooth relations, an optimal lower constant, a universal rejection
of global-resultant ideas, or a factoring lower bound. Combining different
norm strata under a changed joint law, multiple fields, changing degree,
or replacing the scan requires a separate analysis with paid construction.

## 8. Handoff

The parent can accept H013's frozen main results as independently reviewed
informal mathematics and close the eta = 2/5 full-scan proposal under its
unchanged model. No unresolved mathematical objection to those main proofs
was found. The general-eta extension above is additionally available for
parent checking; it is not needed to accept the original report.

The unresolved algorithmic obligations are substantive: actual selected
joint rational/ideal smoothness and useful-row statistics, an executable
changed selector if one is proposed, and complete processing/extraction
costs and success probability. A paid output-sensitive selector could change
the feasibility inequality, but the count alone does not construct it. A
next round should identify such a changed mechanism and its precise model
before any finite run; any run still needs its own prior registration and
at-most-60-second budget.

Best supported result: the explicit cancellation-inclusive count (R5), its
population-loss consequence (R6), and rejection of the supplied model, plus
the exact full-height special-family counterexample. No new factoring
algorithm or verified complexity improvement has been established.
Verified improvement remains **NONE**.
