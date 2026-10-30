# BBK 5.4: additive cancellation trees obstructed; full target unresolved

Research: 29 October 2026 UTC (28 October local America/Los_Angeles).
Credit 0. No acceptance authority, full candidate, PROOF.md or Lean certificate.

## Literal target and early source gate

For integers k>=1,n>=0, write

    G(k,n)=prod(i=0..n-1)(1-q^(2k-1+2i)) / prod(j=0..n)(1-q^(2j+1)).

BBK arXiv:2601.04014v1 Section 5, Conjecture 5.4 asks for
G=sum(j=0..n) z_j(q)/(1-q^(2j+1)), with nonnegative coefficients in every
z_j. Polynomial numerators are understood, as instructed; neither suppressed
n dependence nor implicit polynomial wording is exploited. Actual Section 5
was freshly retrieved and read before the structural work. Its 5.1 is the
weaker all-coefficient positivity conjecture. No fixed row is proposed here.

Read ancestor/campaign AGENTS, current ledger, NEXT, prior-campaign-context,
root-bbk-positive-fractions-r1/FINDINGS and both witness/checker sources,
root-bbk-handoff-r4, sol-bbk-full-refinement-r4, and root-bbk-r1 failures.
The supplied commit56b819b60e was not resolved with git: git operations were
prohibited. Actual input bytes are instead hashed in checks.json/provenance.json.
Existing discoveries/exclusions and counts3/30 additional,33/60 total retained.

Fresh Chern–Wang2601.19845v1 Theorem1.3, Lemma2.1 and Corollary2.2 have the
SQUARED denominator (q;q^2)_n^2 (or length n+1 squared); their positive
substitution-of-one identity and their summed F theorem do not give BBK's
individual G. Fresh Liu2605.28012v1 Theorem1 and Lemmas2.1–2.3 concern
C_(m,n)=[2m+1]![2n]!/([m+n+1]![m]![n]!), with ordinary consecutive q
factorials. I read the recurrences, not just the title. No identity transferring
those recurrences to G's odd-factorial ratio was established. These comparisons
are mismatches of the proposed direct applications, not universal impossibility.

Public search on29October for the exact identifier/5.4 and positivity found no
full proof in the returned primary results. MathDB372434 direct retrieval got403;
requests to mathdb.com stopped, no workaround/retry. Its indexed open label is
not novelty evidence. No GitHub API requests: reused29October04:39UTC complete
registry trees/head receipts from sol-fresh-analysis-discovery-r7, as instructed.
OpenAI head7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a;
trureturing head67b4fae085cf19003a33f8027410c383b49e5046.
Complete trureturing D5/Problems path screens return nearby two-color files;
actual cached Defs/result bodies in sol-bbk-full-refinement-r4 distinguish
C'/D' sign questions and eventual positivity from this full5.4. Complete
OpenAI preprints tree has no identifier/name hit. This is partial current-proof
coverage, not a complete live-body audit, a freshly verified head, or worldwide
novelty clearance. No major formal investment was made.

## Independent audit of the root reduction

Let d_j=2j+1, M=n(2k+n-2), D=M-(n+1)^2=2n(k-2)-1.
As q tends to positive infinity, G(q)~ -q^D. In any nonnegative-polynomial
numerator decomposition, a nonzero term is asymptotic to
-c_j q^(deg(z_j)-d_j), c_j>0. Largest-exponent terms have the same sign and
cannot cancel. Thus each deg(z_j)<=D+d_j. This remains valid for negative D;
a negative permitted bound forces that numerator to vanish.

Multiplication by Q=prod_j(1-q^d_j) gives an exact polynomial identity of
degree<=M. Its coefficients are linear in nonnegative variables x_(j,a),
0<=a<=D+d_j. Conversely such an identity is the desired decomposition.
The alternative progression equations through degree M are equivalent:
if the truncated series difference vanishes, its product with Q (Q(0)=1)
also vanishes through M; that product is a polynomial of degree<=M, so is zero.
This is an identity argument, not inference of an infinite theorem from a prefix.

Rational feasibility follows from real feasibility: restrict to the positive
support of any feasible real point. The rational linear equalities have a
rational particular solution and rational nullspace basis, so rational points
are dense in their affine solution space; choose one sufficiently close to
preserve positivity on that support and keep the other coordinates zero.
No integrality conclusion follows.

Reciprocity is G(1/q)=-q^(-D)G(q), by inverting every factor. Applying this to
a decomposition gives numerator q^(D+d_j) z_j(1/q); the degree bounds ensure
it is a polynomial with nonnegative coefficients. Averaging is therefore
legitimate, preserving the full identity. The rational Farkas alternative has
exactly the root's sign: A^T y>=0 and b^T y<0 for Ax=b,x>=0.
I found no error in these deductions. The independent checker verifies103 saved
whole identities,103 reciprocally averaged whole identities, and their entire
finite progression systems;130 nonzero saved coefficients are nonintegral.
It imports neither the root checker nor the solver and writes only here.

The other root identities checked algebraically are
G(k,n)=O_(k+n-1)/(O_(k-1)O_(n+1))=G(n+2,k-2) for k>=2,
and G(1,n)=1/(1-q^(2n+1)). For5.4 specifically, transposing a pair with
n>k-2 supplies denominators only through k-2<=n, hence embeds in the original
allowed list. Thus proving the triangular range k>=n+2 would suffice for5.4,
not just5.1. This is an elementary scope reduction, not discovery credit.

## Exact two-weight kernel criterion

For positive integers d,e,h, the rational function

    K=(1-q^h)/((1-q^d)(1-q^e))

has nonnegative coefficients if and only if h is in the additive semigroup
{ud+ve:u,v>=0 integers}. Necessity: if h is not representable, the coefficient
at q^h is 0-1=-1. Sufficiency: if h=ud+ve, the exact telescoping identity is

    K = (1+q^d+...+q^((u-1)d))/(1-q^e)
      + q^(ud)(1+q^e+...+q^((v-1)e))/(1-q^d),

with empty sums zero. This also supplies nonnegative polynomial numerators.
It is a classical elementary coin identity, not claimed novel.

The adjacent-k recurrence, derived by subtracting the two numerator blocks, is

 G(k+1,n)-G(k,n)
 = q^(2k-1) (1-q^(2n))/(1-q^(2n+1)) G(k+1,n-1).

Multiplication of an arbitrary positive basis term1/(1-q^d) on the right is
positive precisely when d divides n, since d<=2n-1 and2n<2n+1. For instance,
n=4,d=7 gives coefficient-1 at degree8. The full residual's coefficient there
before the monomial shift is5 for k=6: other terms can repair this defect.
Therefore the recurrence is not a positive operator on the entire allowed
cone. This does NOT exclude specially chosen z_j that repair it. In particular,
a negative basis kernel cannot be lifted into a Farkas counterexample for G.

## Broader additive factor-cancellation route: exact infinite-family obstruction

This was investigated as a possible uniform partition construction, extending
the predecessor's divisibility matching. Define the route precisely. A state
has remaining numerator factors1-q^h, denominator factors1-q^d, and a nonzero
nonnegative polynomial multiplier. Choose one numerator exponent h and any
representation h=sum_i u_i d_i in the remaining denominator weights.
Expand by telescoping in any order:

 (1-q^h)/prod_i(1-q^d_i)
 = sum_(i:u_i>0) q^(sum_(l<i)u_l d_l)
       (sum_(t=0..u_i-1)q^(t d_i)) / prod_(l!=i)(1-q^d_l).

Every nonzero branch consumes that numerator factor and removes one participating
denominator. Reorder numerator factors or choose representations adaptively
in different branches; both are permitted. A successful finite tree reaches
states with no numerator factors, giving positive polynomial numerators over
single allowed denominators. Direct divisibility cancellation is the special
case of a one-weight representation. This is a sufficient scheme, not an
equivalence with arbitrary5.4 decompositions.

No such tree succeeds on G(m+1,m-1), for ANY integer m>=4.
Here denominator weights are1,3,...,2m-1 and numerator exponents are
2m+1,2m+3,...,4m-3. Protect the two denominator weights

    d=2m-3, e=2m-1.

No numerator exponent h belongs to the semigroup generated by d,e:
using one part gives h<=e<2m+1; using exactly two parts gives an even number,
whereas h is odd; using at least three parts gives h>=3d=6m-9>4m-3,
since m>=4. Zero parts also cannot give h.

Follow any purported cancellation tree. As long as d,e remain, a representation
of the chosen remaining h must use some other denominator weight. Its
corresponding telescoping summand is nonzero and removes such a weight,
preserving d,e; select that branch. Nonnegative polynomial multipliers stay
nonzero, so this branch cannot disappear by cancellation. There are m-2
unprotected denominators and m-1 numerator factors. After at most m-2 steps,
either the algorithm has already failed or one reaches a branch with only
d,e and one remaining numerator h. There is no representation of that h in
d,e, so no final step is available. Contradiction.

This is an exact obstruction to the entire specified adaptive additive tree,
not merely to one matching, one choice of factor order, one small instance,
or a memory-limited search. It subsumes the old divisibility obstruction for
this proof scheme. It resembles the old coordinate-plane complete-intersection
obstruction, and receives NO independent discovery credit. In particular,
m=4 is G(5,3), for which the root has an exact valid5.4 witness: the obstruction
cannot be mistaken for a source counterexample. More complicated positive
recurrences, simultaneous multi-factor transformations and arbitrary positive
LP identities remain outside the excluded scheme.

## Outcome and next missing step

A uniform polynomial construction or exact legitimate interior Farkas separator
for5.4 is still absent. No claimed resolution of5.1/5.2, no eligible candidate,
no formal endpoint. The strongest new structural conclusion is the failure of
adaptive additive single-factor cancellation on an infinite interior family.
A next attack must genuinely combine numerator factors or exploit relations
between positive summands; changing factor order or replacing divisibility by
coin representations alone cannot fix this route. This does not certify that
any larger class of constructions is impossible.

Run `python checks.py` here. It hard-caps address space512MiB and CPU100seconds,
sets BLAS/OMP1, uses exact rational/integer arithmetic, and has bounded polynomial
loops. No exponential tree enumeration, LP enlargement, HiGHS invocation, Lean,
children, git operations or writes outside this lane were used.19,440 bounded
kernel checks and97 invariant examples are diagnostics of the proofs above,
not source-conjecture evidence. No PROOF.md is appropriate without a complete
ordinary source candidate.
