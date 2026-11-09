# W003 Lens A — independent review of the positive-binomial quadratic selector

2026-10-08. **NEW independent review; recommendations and additional arguments
remain UNACCEPTED until coordinator disposition.** Verified COMPLETE classical
factoring complexity improvement: **NONE**.

I recommend closing this specific mixed-target realization as a speedup. The
negative real embedding makes both targets impossible, and the submitted
finite algorithm, exact early-success laws, and stated bit-cost bounds survive
independent audit. This includes equations (7.2), (7.3), (7.4), the all-input
complete-factorization upper bounds, and success-preserving pruning. One local
terminology correction is necessary: at submitted line 425, replace “a root
of unity” by “a square root of unity.” The unqualified phrase is false; the
proof below establishes exactly the required kernel-of-squaring statement.
No algorithm change or change to a displayed quantitative formula is needed.

The arguments below supply independent derivations, including an elementary
trace proof of the order multiplier, an ordered CRT count, a sequential bit-cost
schedule, and recursive accounting. They do not certify an implementation,
Lean theorem, numerical experiment, or machine refinement. In particular,
this is not acceptance on the coordinator's behalf.

## 1. Exact scope, evidence identities, and complete read coverage

The assessed program is precisely the submitted selector

    u=R+2N, D_1=u^2+N, D_2=u^2+3N,
    K_i=Q(alpha_i), alpha_i^2=D_i,

with the ordered rows (j,1), 1<=j<=n=bit_length(N), the specified early gcd/root
returns, all binary subset masks, and both mixed-target orientations. The
pruned variant retains the same early stopping rule and omits the provably
unsuccessful subset phase. The sign argument has the explicitly stated broader
scope of rational nonzero pairs and integer exponents in fields with a
negative real conjugate of the chosen alpha. It does not cover arbitrary
root-dependent polynomial selection, arbitrary elements, all totally positive
generators, complex fields, all two-field NFS constructions, or factoring in
general. A field being totally real is not the same as its generator being
totally positive: these particular generators each have a negative conjugate.

The exact original brief is frozen, without rewriting, at
[the review's brief snapshot](W003-twisted-review-evidence/inputs/research/hypotheses/W003.md).
Its SHA-256 is
`fc8f5cf42a34b020833832a56994421c183e22a8fd2e951a6cb9c6cee14ab629`.
Both the working submission and submitted draft were byte-identical, with
511 lines and SHA-256
`7197a3de72f354d762ae6a12a089602275d3d435a01e033cae45a5b6b1f529d3`.
The frozen intake has SHA-256
`0dbecfe045be07b1533ce61271bce7f7a5fadb774347e7f28d9770a6b504e88e`.

All 29 constructor input snapshots and all 32 original delivery entries
verified before this audit. The review independently preserves those complete
bytes, the original input inventory, source notes, delivery manifest, submitted
draft, intake, original brief, and current dependency records. The 66 snapshot
identities are in
[the separate review input inventory](W003-twisted-review-evidence/input-inventory.json).
[The intake verification record](W003-twisted-review-evidence/intake-verification.json)
records identity checks, not mathematical tests. The final
[review delivery manifest](W003-twisted-review-delivery.sha256)
covers this report and its supporting evidence, excluding only itself.

I read AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md, the current STATE checkpoint and W001 synthesis; the current
W002 dispositions; H027's corrected section 6, disposition and root-entropy
prior-art note; H028/H031 dispositions and the original report passages used
for common maps, actual squares and localization; and W002 B's original
all-cap failure argument with its governing corrections. These inherited
results provide boundaries, not supply theorems for W003. Historical live-task
wording does not override the user's statement that both constructors are
completed and this is a new review with no author responses or prior rounds.

All submitted lines were read and audited against the frozen 511-line copy:

- Lines 1–23: executive claims, scoped failure, and power-cost summary; covered
  by sections 2–8 below. “Typical” is justified as a positive-constant raw-word
  branch probability and expected cost, not probability tending to one over
  all raw words, which include range rejections.
- Lines 24–57: evidence, dependencies and status; checked against the frozen
  records. Constructor activity declarations are preserved as declarations;
  hashes alone cannot prove a historical negative about actions.
- Lines 58–116: preprocessing and every field-selection assertion; section 2.
- Lines 117–180: ordered rows, exhaustive target search, and the complete
  rational-coordinate root test; sections 3 and 6.
- Lines 181–234: integrality, localization, both recoveries and signs; section 4.
- Lines 235–292: signature, square-class, ideal/unit and norm obstructions,
  inverses and shared scalars; section 5.
- Lines 293–314: actual norm sizes and distributional limits; section 5.
- Lines 315–345: pathwise time, space, widths and early exits; section 6.
- Lines 346–389: both exact success laws and the balanced-family lower bound;
  sections 7–8.
- Lines 390–419: all-input restarts, factor tree, pruning and finite tapes;
  section 8.
- Lines 420–452: root fibers and the failure-inclusive general law; section 7,
  with the terminology correction identified above.
- Lines 453–511: primary comparisons, rejected claim, scope, next-test choice
  and delivery declarations; sections 9–10 and the source notes.

No other W003 review draft was read. I did not read the Lens B research report
or assume its new deductions. I inspected two of its archived Rabin primary
source files directly as literature, preserving separate copies here. The
[source inspection notes](W003-twisted-review-source-notes.md) distinguish those
primary bytes from any research or review conclusions.

## 2. Domain, elementary cases, and paid selection

Inputs for complete factorization are positive integers N_0. Handle 1 and
primes, extract powers of 2, and detect perfect powers using exact kth roots
for 2<=k<=bit_length(N). Every residual cofactor is passed through the same
preprocessing before a split trial. In the perfect-power branch, factor the
base recursively and multiply its prime multiplicities by k. This makes
explicit the usual recursive interpretation of submitted lines 60–66 and
395–396; neither a residual prime nor a residual prime power enters a trial.

Binary search for a kth root uses O(n) integer comparisons. Repeated squaring
with powers truncated above N, or even exact intermediate powers of O(n^2)
bits for k<=n, has polynomial bit cost. There are only n-1 exponents. A fixed
deterministic polynomial-time primality algorithm and exact divisions complete
the paid preprocessing. Its uniform time and space are bounded by a fixed
polynomial P(n); no factoring oracle is part of it. An odd composite that
is not a perfect power has at least two distinct prime divisors, since a
composite with only one prime divisor is a prime power. Unequal repeated
prime exponents are allowed in the continuing domain.

For a unit input to the inner routine, 1<=R<=N-1 and gcd(R,N)=1. Hence

    2N+1 <= u <= 3N-1,
    3N < 2u+1.

Both D_i are strictly between the consecutive integer squares u^2 and
(u+1)^2. Thus D_i are positive nonsquares and T^2-D_i are irreducible over Q.
For s=u^2+2N, direct multiplication gives D_1 D_2=s^2-N^2, and

    2s-1-N^2 > 8N^2+4N-1-N^2 > 0.

Consequently (s-1)^2<D_1 D_2<s^2. If the two quadratic fields were equal,
write sqrt(D_2)=a+b sqrt(D_1) with a,b rational. Irrationality and squaring
force a=0 and b!=0, whence D_2/D_1=b^2 and D_1 D_2=(bD_1)^2. An integer
that is a rational square is an integer square (reduce the square root's
fraction). This contradicts the second square gap. The fields are distinct,
including when either D_i has a nontrivial square factor.

The height bounds are also uniform:

    D_i > (2N)^2,
    D_i <= (3N-1)^2+3N = 9N^2-3N+1 < 10N^2.

All defining coefficients have O(n) bits and both degrees are exactly two.
Reducing u modulo N gives D_i=R^2 modulo N, so f_i(R)=0, gcd(D_i,N)=1 and
f_i'(R)=2R is a unit because N is odd. The three integer nonsquare tests and
the congruence/gcd validations use only O(n)-bit quantities and polynomial
work. They never reject on this domain. No squarefree-part factorization,
discriminant factorization, maximal-order computation or selection retries
are hidden in the construction.

The warning about reducible polynomials under a different selector is sound:
a reducible quotient cannot be treated as a number field. Evaluation gcds
could be 1, proper, or N. This alternative is not executed here and contributes
neither success nor cost to the present law.

## 3. Finite target search and exact field-root test

For each j in the prescribed increasing order, compute gcd(j^2-R,N). A proper
gcd is checked and returned. A full gcd supplies y=j mod N; since R is a
unit, j is a unit as well. Verify its square and return it immediately. If
the outer comparison is trivial, the trial fails; it does not resume the row
scan. This stopping rule is essential to the exact law. Only gcd 1 retains
a row. Therefore every subset-search branch has h=n; h<n refers only to a
prefix that exits before enumeration. Each retained j^2-alpha_i is nonzero
because alpha_i is irrational, and each image is a unit. Empty products equal 1.

Every subset is examined exactly once. On a twisted side, testing
alpha_i Q_i is equivalent to testing Q_i=alpha_i z_i^2: if w_i^2=alpha_i Q_i,
then z_i=w_i/alpha_i; conversely w_i=alpha_i z_i. The divisor alpha_i is
nonzero. The second, untwisted test is made only after the twisted test
succeeds. Reversing which field is twisted gives exactly the second target.
This is a finite exhaustive decision procedure for the specified list, not
an assumption that its target lies in a known square-class span.

Independently, for U=A+B alpha and w=a+b alpha, uniqueness of coordinates
in Q+Q alpha gives

    a^2+D b^2=A,  2ab=B.

If B=0, the second equation forces a=0 or b=0. Thus the only possible
nonzero-root types are the rational root of A and alpha times a rational
root of A/D. Negative quantities are rejected; zero is handled separately.
The two candidate tests and exact verification are exhaustive. The positive
coefficient convention deterministically selects a sign.

If B!=0, every root has a!=0, and

    E=A^2-D B^2=(a^2-D b^2)^2,
    a^2=(A+s)/2 or (A-s)/2,  s=sqrt(E).

Since E is an integer, its rational square root, if one exists, is an integer.
Negative E and nonsquare E are therefore valid immediate rejections. For
both listed t values, require t>0 and a rational square, select its positive
root a, set b=B/(2a), and check both coordinate identities. No zero divisor
or zero denominator is admitted. If a root exists, changing its global sign
makes a positive, so one of these branches finds it. If neither verifies,
there is no root. Extraneous candidates cannot pass the final exact check.
This also covers zero/negative A, zero E and all B=0 cases without an oracle.

Let L bound the signed bit lengths of A and B and set W=L+ceil(log_2 D)+2.
E and every candidate rational numerator/denominator have O(W) bits. Fraction
reduction is a gcd and exact divisions. There are a constant number of rational
square tests, each reducing a fraction and square-testing numerator and
denominator. Integer square root by binary search costs O(W) schoolbook
squarings/comparisons of O(W)-bit integers, hence O(W^3) bit operations.
The remaining rational arithmetic, verification and coordinate reduction fit
that bound. Root output sizes are O(W), not merely an unspecified oracle
output bound. Scratch space is polynomial, and the test terminates on
nonsquares as well as squares. This proves the submitted root-test envelope.

## 4. Integral clearing, modular maps, and the two recoveries

Reduction alpha_i -> R defines a homomorphism on Z[alpha_i], since f_i(R)=0.
It extends to the localization at alpha_i and delta_i=2alpha_i because their
images R and 2R are units. It cannot extend as a unital map from all of K_i
to Z/NZ: the nonzero rational integer N is invertible in K_i but maps to zero.
Thus an arbitrary displayed rational denominator is not a modular inverse.

The multiplier can be proved directly here, without computing an integral
basis. If w^2=U=A+B alpha with A,B integers, then w satisfies the monic
integer polynomial

    X^4-2A X^2+(A^2-D B^2).

It is therefore an algebraic integer. Writing w=a+b alpha, both w and
alpha w are integral. Their rational traces are integers:

    Tr(w)=2a in Z,  Tr(alpha w)=2Db in Z.

It follows immediately that

    delta w=2alpha(a+b alpha)=2Db+(2a)alpha in Z[alpha].

This independently proves the exact special case of the submitted derivative
order multiplier, for every positive nonsquare integer D, without factoring
D. It justifies exact cancellation and the integral-coordinate checks before
any reduction. Computing those coordinates and verifying h^2=delta^2 U use
the widths and polynomial costs of section 3.

On the twisted side U=alpha Q, reduction of h^2=delta^2 U gives
h(R)^2=4R^3 q, where q=Q(R). Hence

    zbar=h(R)/(2R^2),  R zbar^2=q.

On the untwisted side U=Q it gives h(R)^2=4R^2 q and

    zbar=h(R)/(2R),  zbar^2=q.

All denominators have verified inverses. The retained rows make q a unit;
if zbar^2 or R zbar^2 is a unit, zbar is a unit in Z/NZ. Thus a verified
recovery on this domain cannot secretly encounter a zero/nonunit image.
The stated proper/full gcd rules remain the correct fail-safe checks.

In the original orientation R zbar_1^2=zbar_2^2=q, so
(zbar_2/zbar_1)^2=R. In the opposite orientation zbar_1^2=R zbar_2^2=q,
so (zbar_1/zbar_2)^2=R. Final congruence verification and both gcd(x-y,N)
and gcd(x+y,N) give only checked proper factors. A nonzero field element
has exactly two square roots, differing by a global sign; changing either
root sign changes y only by a global sign. The real embeddings used next
are feasibility tests, not freely selectable local CRT signs of a reduction.

## 5. Obstruction, square-class scope, and norm geometry

At a real embedding sigma with sigma(alpha)<0, a rational pair (a,b)!=(0,0)
satisfies

    sigma(a^2-b^2 alpha)=a^2+|sigma(alpha)|b^2>0.

Every finite product with arbitrary integer exponents is positive: each
factor and its inverse are positive. A nonzero square has positive image,
whereas sigma(alpha z^2)<0. Equality is impossible. Nonzeroness prevents
z=0 from evading the contradiction. “Enlarged without bound” means any
finite enlarged list or finite product, not an undefined infinite product.
Both selected alpha_i have the negative embedding -sqrt(D_i). Therefore
both targets, on every subset including the empty subset, are impossible.
In particular alpha_i Q_i has negative image there and its exact root test
must return NONSQUARE. No untwisted test or field recovery is reached in the
literal execution.

This is an explicit character separating the targets from the subgroup
generated by the rows. Real sign descends to K_i^*/K_i^{*2}. Each ordinary
row has sign +1 at the negative embedding in each field; a mixed target
has sign pair (-1,+1) or (+1,-1). Its required sign equation is inconsistent.
No full square-class basis is needed for this certificate. The exhaustive
root tests, independently, decide actual element squareness and therefore
include every ideal-class, unit and nonmaximal-order obstruction. Even
prime-ideal exponents only produce a square ideal; its square-root ideal
can be nonprincipal, and a principal generator can retain a nonsquare unit.
None of those weaker conditions rescues an inconsistent real signature.

For the proposed extension by common nonzero rational scalars, a scalar c
has the same sign in the two fields. A product of scalar-augmented rows
therefore has sign pair (s,s), s in {+1,-1}. The mixed target still has
opposite signs. This proves the simultaneous obstruction even though a
negative scalar destroys the individual positivity of that one row. It
requires the scalar to be common to both coordinates; separately chosen
scalars or unpaired elements would be a different interface.

Since alpha has a negative real conjugate, it is not a square in K.
K(sqrt(alpha))/K is a quadratic extension, and the relative norm of
a+b sqrt(alpha) is a^2-b^2 alpha. At the chosen real place it is a complex
norm, hence positive. This is the same obstruction expressed as an elementary
norm identity; it grants no norm equation solver and claims no novelty.

Finally, conjugating alpha to -alpha gives exactly

    Norm(a^2-b^2 alpha)=a^4-D b^4.

For the actual rows, j^4<=n^4=o(N^2) uniformly, while 4N^2<D_i<10N^2.
Thus |j^4-D_i| is bounded above and below by fixed positive multiples of
N^2 for all sufficiently large N, uniformly in R and j. In a box of size
H, the triangle inequality gives (1+D_i)H^4. This latter bound does not
exclude cancellation for a different row law. Nor does a large norm prove
a smoothness probability for a structured sequence. The R distribution on
unit squares, proved next, supplies no coupling to NFS polynomial selection.
These conclusions concern this deliberately padded selector only.

## 6. Sequential finite execution and complete bit costs

Use a fixed finite multitape bit program with ordinary binary integers,
schoolbook arithmetic, Euclidean gcd/extended gcd, and binary-search exact
roots. This suffices for the conservative bounds; no unit-cost unbounded
integer operation or indexed-memory oracle is needed. Uniform loop bounds
are computed from N. Only the outer n-bit word is random; the inner tape
length is zero. Every outer branch pays for drawing all n bits, its comparison,
and whichever gcd, squaring, verification and later work it actually reaches.

For a product A+B alpha, multiplication by j^2-alpha gives

    A'=j^2 A-D B,  B'=j^2 B-A.

If M=max(|A|,|B|), then the new maximum is at most
(D+n^2+1)M. Starting from (1,0), h factors have O(hn+1)-bit coordinates;
multiplication by alpha adds only O(n) bits. Write W_h=O((h+1)n) for a
common bound. Storing two current field products takes O(W_h) bits. Keeping
all retained indices and residues takes polynomial space (even O(n^2)
is sufficient), and the binary mask has h bits.

For each mask, scan the saved rows sequentially with its mask bits, updating
the two products when selected. Schoolbook multiplication with O(W_h)-bit
operands gives O((h+1)W_h^2) for that scan, including comparisons, copying
and rewinds. The root test costs O(W_h^3) by section 3. A constant number
of exact root tests, identity checks, integral clearing, modular reductions,
extended gcds and output checks also fits O((h+1)^3 n^3). For instance,
reducing a W_h-bit coefficient modulo N and modularly inverting an n-bit
unit are polynomial operations bounded by this envelope. Subset-counter
increments and complete tape scans are smaller charges. Empty masks are
processed with the same valid envelope. Discard the products and root scratch
before the next mask; never store the exponential collection of masks.

Selection, its validations, and the at-most-n signed row gcds use polynomial
time and space. Consequently, allowing P(n) for fixed elementary work,

    T_trial <= P(n)+O(2^h (h+1)^3 n^3) <= 2^n poly(n),
    S_trial <= poly(n).

If there is no early return, h=n and there are exactly 2^n masks and exactly
two failed twisted-root calls per mask. The count 2^(n+1) is exact for this
literal program, because each first test fails and the program next tries
the other orientation. It is not a count of four actual root calls per mask:
neither untwisted test is reached. The full field-recovery costs are legitimate
upper-bound charges but contribute no executed success branch here.

This proves a finite pathwise upper bound, inclusive of failed square tests,
raw rejects, full gcds, operand growth and all nonempty/empty search paths.
It also explains why the literal exponential factor is real work on a
search-reaching branch. It supplies no lower bound on every algorithm for
inhomogeneous square classes; section 5 already gives a polynomial rejection
certificate for this instance.

## 7. Independent probability audit, including ordered early branches

**Fiber statement and the wording repair.** For an odd prime power p^e,
the solutions of t^2=1 are exactly +1 and -1. Indeed p^e divides
(t-1)(t+1), and the two factors have no common odd prime divisor, so all
of p^e divides one factor. This is a statement about square roots of unity,
not about all roots of unity as the literal phrase at line 425 would say.
CRT gives 2^r solutions of t^2=1 for N=product p_i^{e_i}.
Multiplication by any one unit root of R bijects this kernel with the roots
of R. Each unit square therefore has precisely 2^r preimages in [0,N-1].

Each admissible raw word has probability 2^(-n). Conditional on the outer
unit branch, x is uniform on the unit group and R is uniform on its square
subgroup, since the fibers have equal size. Given R, x is uniform on its
fiber. An inner transcript or completion event determined only by N,R and
independent random bits has the same likelihood for every x in that fiber.
Conditioning on any such event of positive probability thus preserves that
uniformity, including conditioning on the verified root it returns.

For a verified unit root y, exactly x=y and x=-y are globally trivial; they
are distinct because N is odd and y is a unit. All other roots choose a
nonempty proper subset of prime-power components where x=y. On those
components gcd(x-y,N) contains the whole p_i^{e_i}; on the other components,
x-y=-2y is a unit. Thus the gcd is precisely a nontrivial proper product of
whole prime powers. The complementary gcd behaves oppositely. This proves
useful conditional probability 1-2^(1-r), with repeated exponents included.
The r=1 case has zero useful probability and belongs to paid preprocessing.

For any finite independent inner tape, let a_R and b_R be the disjoint
proper-factor and verified-root probabilities. Partition the raw words into
out-of-range, zero, proper nonunits, and the equal unit fibers. Their success
mass is exactly

    (N-1-phi(N))/2^n
      +(2^r/2^n) sum_R [a_R+b_R(1-2^(1-r))],

where R ranges over unit squares. Rejected words number 2^n-N; x=0 is the
unique full outer gcd; all N-1-phi(N) other nonunits give proper gcds. This
establishes (8.1) without knowing the prime factorization in the algorithm.
The factorization is used only in the proof.

**The actual ordered scan.** In this program a_R and b_R are indicators.
The preimages of the proper-gcd branch comprise U_N. The root-return residues
comprise J_N, each corresponding to its first full-gcd j; no residue counted
there has an earlier proper-gcd return. Distinct j can in general give the
same R, so only |J_N|<=n is asserted. On each such fiber exactly 2^r-2 words
succeed after the returned root, regardless of the returned root's sign.
No subset supplies any additional factor or root. These disjoint events give

    sigma_N=(N-1-phi(N)+|U_N|+(2^r-2)|J_N|)/2^n,

exactly (7.2). U_N counts words, J_N counts residues; substituting n for
|J_N| or treating both as word counts on general N would be wrong.

**Distinct semiprimes with p,q>2n.** At each prime, the labels +j and -j,
1<=j<=n, are all nonzero and distinct: equality between opposite signs would
require that prime to divide an integer in [2,2n], and equality between same
signs forces the same j. Each component has a unique matching index or none.
The ordered execution is therefore classified exhaustively as follows.

1. Neither component has an index. Every row gcd is 1, so the subset search
   is reached and fails. CRT gives (p-1-2n)(q-1-2n) such unit words.
2. Exactly one component has an index. Its row is the first matching row,
   and gives exactly p or q as a proper gcd.
3. Both components have different indices. At the earlier index only one
   component vanishes, so the program returns a proper factor. No subsequent
   row or alternative stopping interpretation is needed.
4. Both components have the same index j. Every earlier row is a unit;
   that row has gcd N and returns j. Of its four independent CRT sign
   assignments, (+,+) and (-,-) are x=+j and x=-j modulo N and fail;
   (+,-) and (-,+) split N. There are n such residues, 4n preimages,
   2n successes and 2n failures.

Thus unit failures number (p-1-2n)(q-1-2n)+2n. Of all N-1 nonzero residues,
the rest succeed, since nonunits already succeed at the outer gcd. Algebra
now gives the numerator, without a probability-independence approximation:

    N-1-[(p-1-2n)(q-1-2n)+2n]
      =(2n+1)(p+q-2-2n).

Dividing by 2^n proves (7.3). The two primes need not be 3 modulo 4 and
need no average-over-primes model. This formula is not asserted for repeated
prime factors or when a prime is <=2n; (7.2) still governs those cases.

## 8. Cold restarts, balanced lower bound, full factorization, and pruning

Here “balanced” means distinct primes with p/q bounded above and below by
fixed positive constants as N=pq tends to infinity. Then p,q=Theta(sqrt(N)),
n=Theta(log N), and p,q>2n eventually. Since N<2^n<=2N on these odd inputs,
(7.3) implies sigma_N=Theta(n/sqrt(N)). The probability of reaching the
subset phase is exactly

    eta_N=(p-1-2n)(q-1-2n)/2^n
         =(N/2^n)(1-o(1)).

It is bounded below by a positive constant. The pathwise count in section 6
therefore implies E[T_trial]=Omega(2^n)=Omega(N), whereas the upper bound
is N poly(n). Equivalently the expected trial cost is N^(1+o(1)); the
submission's informal “typical” wording should not conceal the raw rejects.

For a fixed continuing N, let C_i be the cost of iid cold trial i and S_i
its success event. The event that trial i is reached depends only on prior
trials and is independent of C_i. Nonnegative summation gives

    E[sum_(i<=first success) C_i]
      =sum_(i>=1) (1-sigma_N)^(i-1) E[C_i]
      =E[T_trial]/sigma_N.

Thus the identity needs independence between trials, not between cost and
success within a trial. If a deterministic preliminary computation is done
only once, its cost is added once outside this equality; charging it cold
on every trial is also a valid, conservative convention. All displayed upper
bounds survive either convention. Applying the identity to the balanced
family proves the claimed local-program lower and upper bounds

    Omega(N^(3/2)/n) <= E[T_split] <= N^(3/2) poly(n).

This is a lower bound for the stated literal execution, not for target search
in general or for factoring. Distinct balanced semiprimes survive the stated
preprocessing. No small-factor screen beyond the specified elementary cases
has been silently inserted into this lower-bound family.

For arbitrary continuing N, take its smallest prime divisor p only in the
analysis. All N/p-1 nonzero multiples of p below N have gcd strictly between
1 and N. Hence, since p<=sqrt(N) and N>=4,

    sigma_N >= (N/p-1)/2^n
             >= (sqrt(N)-1)/(2N)
             >= 1/(4sqrt(N)).

This does not depend on an inner root or even reaching the field phase.
Together with the pathwise trial envelope it gives the all-input expected
split bound N^(3/2) poly(n) and almost-sure termination. Invalid factors are
never output. No uniform positive mixed-target completion probability is
being smuggled into this bound: that probability is zero.

To pass to complete factorization, use depth-first recursion after every
verified proper split and apply the preprocessing anew at each node. Let
n_0=bit_length(N_0). The number of prime leaves counted with multiplicity is
at most log_2 N_0. An expanded factor tree, allowing multiple copies in a
perfect-power step or extraction of repeated 2s, has at most twice that many
nodes up to an additive constant. Factoring a repeated base just once can
only reduce this count. Every node value M is <=N_0 and its bit length is
<=n_0. Conditional on reaching any node, its local preprocessing and expected
split work are at most N_0^(3/2) times a fixed polynomial in n_0. The deterministic node cap
and conditional expectation therefore give

    E[T_complete(N_0)] <= N_0^(3/2) poly(log N_0).

This argument tolerates a random tree shape; it does not multiply an average
cost under one input distribution by an unrelated tree size. Perfect-power
multiplicities, primality proofs/tests, exact cofactor divisions and output
verification have polynomial overhead. Depth-first traversal keeps only a
polynomial number of n_0-bit numbers and one active trial workspace. Discarding
trial tapes after use and not storing the count of every past failure gives
polynomial working space even though there is no finite worst-case restart
count. The output itself has polynomial length.

Pruning preserves the entire early scan, including stopping at the first
full-gcd root even when the outer comparison subsequently fails. On exactly
the branch where enumeration would start, return FAIL using the sign
certificate instead. That replaces only a branch whose output was always
FAIL; it preserves sigma_N exactly, word by word. Selection checks also
always pass and can subsequently be removed. The remaining routine consists
of the outer gcd, the ordered gcd(j^2-x^2,N) scan and verified comparison to
its directly recognized root, with modular reductions as desired. Its trial
work is polynomial. The same lower bound sigma_N>=1/(4sqrt(N)) and the same
factor-tree argument yield

    E[T_complete,pruned(N_0)] <= N_0^(1/2) poly(log N_0),
    S_complete,pruned <= poly(log N_0).

On the balanced family its expected number of trials remains
Theta(sqrt(N)/n), so the submitted Omega(sqrt(N)/n) cost lower bound is
valid even if one charges only one operation per trial. Actual random-bit
reads and all arithmetic are charged in the polynomial upper bound. The
conservative lower bound already has N^(1/2-o(1)) scale and rules out a
uniform subexponential expected-time claim for this pruned program.

For fixed N and k independent trials, a kn-bit tape gives success exactly
1-(1-sigma_N)^k; an execution stopping early leaves an unused suffix. Its
worst-case time is at most k times the pathwise trial bound, and its working
space can be reused. This is a split probability, not a claim that k trials
complete an arbitrary factor tree. Unlimited restarts use an unbounded stream
with almost-sure finite consumption and finite expected cost, not a polynomial
worst-case runtime or a polynomial-length tape. Holding R fixed and rerunning
this deterministic inner routine adds no successful outcomes.

## 9. Matched baselines and primary-source boundary

The literature comparison was checked from primary statements and algorithm
passages, not from the other review or the Lens B report. Detailed read
locations and retrieval scope are recorded in the source notes.

**Finite N,R-only inversion.** Enumerating y from 0 through N-1 and checking
y^2=R modulo N terminates on every unit square in O(N poly(n)) bit time and
polynomial working space. Its root selection depends only on N,R. Ordered
distinct primes satisfy p_i>=i+1, so

    phi(N)/N=product_i(1-1/p_i)
       >=product_(i=1)^r i/(i+1)=1/(r+1)>=1/(n+1).

The outer raw-word unit probability is therefore at least 1/(2(n+1)), and
conditional useful-root probability is at least 1/2 on the continuing domain.
This proves an additional polynomial expected restart factor, including
rejections, without assuming unit sampling is free. Recursive factorization
retains an O(N_0 poly(log N_0)) upper envelope and polynomial space. This is
a valid inversion construction and a comparison, not a hidden fallback in A.
Rabin's Theorems 1–2 already give the inversion-to-factoring reduction for
his stated setting; section 7 above supplies the exact present raw-word and
multiplicity accounting rather than importing his operation convention.
[MIT primary record](https://dspace.mit.edu/entities/publication/15016449-ca26-4d45-82ea-7c200d82d777).

**Rigorous complete time.** Dixon's algorithm and theorem for odd integers
with at least two distinct prime divisors give a proved expected
exp(O(sqrt(log N log log N))) splitting bound. Polynomial bit charges for
its specified arithmetic and ordinary preprocessing/recursion preserve the
subexponential complete-time class. His Lemma 3 explicitly conditions on the
squared list and uses the remaining root-fiber choices. This is established
prior art, not W003's new generation theorem. It is asymptotically faster
in time than A on the balanced family, where A has proved power-scale lower
bounds. Dixon's stored relation data are not being claimed to use polynomial
space, so this comparison does not assert domination in both time and space.
[Dixon, sections 2–3](https://pages.cs.wisc.edu/~cs812-1/dixon.pdf).

**Deterministic power and space.** Ordinary trial division, with primality
and recursion, supplies a deterministic sqrt(N_0) poly(log N_0) complete upper
bound using polynomial space. This matches the pruned program's stated power
and space envelope while avoiding random restarts. It is a deliberately weak
but sufficient baseline, not a claim about the best deterministic factoring
exponent. No practical timing, constant-factor improvement or special-family
advantage is established here.

**NFS reconstruction and heuristic time.** Coppersmith's many-field method
has separate ideal/character blocks and takes actual roots separately before
combining their common modular images. The near-1.902 constant concerns that
optimized many-field cold heuristic, not a theorem for exactly two quadratic
fields, not a rigorous complete-factoring guarantee, and not the amortized
factorization-factory constant. Its homogeneous reconstruction does not make
A's prescribed inhomogeneous target reachable. Stevenhagen sections 6–10
explicitly distinguish ideal parity, principality, units, nonmaximal orders
and actual extraction, including the derivative multiplier in section 7.
A's quadratic test handles those square tests directly; it does not inherit
NFS relation supply or useful-root probability.
[Coppersmith](https://link.springer.com/content/pdf/10.1007/BF00198464.pdf),
[Stevenhagen](https://pub.math.leidenuniv.nl/~stevenhagenp/ANTproc/04psh.pdf).

**Rigorous square congruences versus useful congruences.** Lee–Venkatesan v1
Theorem 2.1 concerns their randomized NFS square-congruence generator;
Theorem 2.3 obtains useful congruences on distinct Blum semiprimes conditional
on Conjecture 7.82. Section 7 and Remark 7.85 cover the productive character
and multiple polynomials. None supplies a theorem for A's arbitrary-square
input R, positive binomials, quadratic heights or short ordered list. A
shared reduction map and similar matrix terminology are not a distributional
coupling. The submission respects this boundary.
[Primary v1, Theorems 2.1/2.3 and section 7](https://arxiv.org/html/1805.08873v1).

## 10. Recommended disposition, repair, and next action

For coordinator consideration, retain the finite on-paper construction,
scoped sign obstruction, exact laws (7.2), (7.3), (8.1), finite bit/space
bounds, balanced literal-program lower bound, and both all-input complete
expected upper bounds. The expanded proofs in this review fill the relevant
verification obligations; they remain unaccepted until disposition.

Make the local wording repair at submitted line 425 in any later corrected
working report: “modulo each odd prime power, a square root of unity is
exactly +1 or -1.” Preserve the original submission and manifest. No displayed
equation requires correction. The raw-word meaning of “typical,” recursive
reprocessing of cofactors, fixed-N scope of the k-trial law, and time/space
baseline distinctions are explicit above and should accompany any reuse.

Reject the positive claim that this selector attains a mixed target with
adequate probability at an inherited NFS cost. Its mixed-target completion
probability is exactly zero for every admissible N,R. All surviving factoring
success comes from separately paid elementary cases and early gcd/recognized-
root branches. The power bounds are properties of these local programs, not
lower bounds for modular inversion, arbitrary-root field selection, totally
positive/complex alternatives, or classical factoring.

**Next proof/test: none.** Increasing the cap, accumulating more homogeneous
nullity or testing more finite inputs cannot change the real-sign identity.
A changed field/element generation law would be a separate proposal needing
its own paid construction, target attainability and success proof. This review
does not select or begin that work.

Only this assigned report and paths beginning W003-twisted-review- were
written. Work was restricted to reading, primary-source inspection, symbolic
reasoning, archival copying/hashing and report authoring. No recursive
delegation, mathematical execution, numerical examples/searches, experiments,
solver implementation, Lean work, packages, outside-project writes, commits,
publication or scheduler was used. Shared records, original reports, intakes,
source notes and manifests remain under coordinator ownership.
