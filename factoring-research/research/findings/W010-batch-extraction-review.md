# W010 batch extraction — independent review

2026-10-08 UTC. Disposition: **accept the conditional detector and equations
(1)–(5), with explicit implementation and probability-cost qualifications below.**
Retain (6) as a scale comparison for the specified sequential evaluator.
Verified new factoring complexity improvement: **NONE**.

The strongest survivor is a duplicate-safe, factor-advice-free extraction
procedure at a fixed map: if both local collision masses are at most 1/2,
its expected extraction work is

    (k+1)/sqrt(rho) * poly(log N),

under the fast integer multiplication and exact sampling conventions stated
below. This is a conditional consumer of an acquired law. It supplies neither
a cheap favorable map nor an improved generic factoring bound. Its identity-map
specialization is the existing sqrt(p) control, with p the smaller prime.

No flaw was found in the proposed algebra or moment coefficients. Two details
need to accompany a complete cost claim: exact uniform residues have expected
rejection-sampling cost unless a failure budget is imposed; and geometric setup
cost alone does not prove expected stopping cost for a doubling schedule. The
same second-moment estimate supplies the missing tail proof, without changing
the detector or the concentration target. A balanced product tree is required
for the claimed linear recovery work.

## 1. Scope and frozen evidence

This review owns only W010-batch-extraction-review* files. The historical cubic
brief is superseded by the current batch-extraction assignment. The accepted
cubic disposition is context; its positive expected drift is not re-audited.
The live norm-envelope B and Jacobi C audits are neither read nor duplicated.
No conclusion here depends on either pending result.

The [input manifest](W010-batch-extraction-review-inputs-manifest.json) identifies
byte-for-byte copies of all local inputs, including the proposal, required
project instructions, hypothesis, parent disposition, and W008 control review.
Each input was read once for capture; later parent changes are outside this
review. The checkpoint snapshot contains no W010 entry, so the explicit current
assignment governs. The [scope record](W010-batch-extraction-review-brief.txt)
records that assignment and its prohibitions.

The [exact certificate](W010-batch-extraction-review-certificate.json) contains
formal coefficient identities and one fixed tiny-list witness. There were no
candidate runs, sampled training trajectories, prime/weight searches, sweeps,
package installations, shared code/Lean/state edits, commits, or publication.
No executable candidate or repository source was changed. Project experiment
and Lean suites were therefore not run. This is an algebraic review, not a
formal Lean proof or a benchmark.

## 2. Duplicate-safe extraction over Z/NZ

Let N=pq for distinct primes, and let c_1,...,c_L be the distinct canonical
residues obtained from the 2M original outputs. Work throughout in R=Z/NZ.
The formal product rule, valid in every commutative ring, gives

    F'(T) = sum_i product_(j != i) (T-c_j),
    F'(c_i) = product_(j != i) (c_i-c_j).

This uses only addition and multiplication. The derivative coefficient j is
multiplied into the coefficient of T^j, never inverted. A degree or derivative
leading coefficient that vanishes modulo one prime causes no correctness
problem. Formal differentiation requires neither factorial division nor
separability. The input polynomials in the product/remainder trees stay monic
over R even when many of their roots coincide over F_p or F_q.

Every nonzero difference between distinct canonical residues has gcd 1, p,
or q with N, never N. Thus a derivative value is a nonunit if and only if that
sample has a useful partner in the distinct union. A proper derivative gcd
immediately solves. A full derivative gcd means the product accumulated both
prime divisors, and can be split to expose a proper gcd.

Exact global deduplication preserves the existence of every useful pair: a
pair with proper gcd has distinct residues, so representatives of both values
survive. Multiplicity and list labels need not survive. The probability proof
continues to count pairs in the original two lists; it only transfers the
existence event to the distinct union. It must not replace that original law
with a fictitious independent law on deduplicated entries. If L<2, the paid
batch fails. Conversely, with the specified recovery, success is equivalent
to the existence of a useful pair anywhere in the original union.

For full-gcd recovery, fix a detected index i. The sibling nodes along c_i's
path in a balanced binary product tree partition the other L-1 leaves.
Their degrees sum to L-1. Evaluate those sibling polynomials at c_i by Horner's
rule until finding a nonunit value; one exists because their product is
F'(c_i). If its gcd is proper, finish. If full, evaluate its children. At
least one child is nonunit; a unit child can be discarded, a proper child
finishes, and a full child can be followed. A nonunit leaf must have a proper
gcd because there are no exact duplicates. The path therefore terminates
successfully. Following an arbitrary nonunit branch is justified here only
after deduplication.

Finding the sibling branch costs O(L) ring operations in aggregate. Below
a chosen node of degree d, evaluating both children costs O(d), and the
degrees along the continuing balanced path shrink geometrically, giving
O(d) further ring operations. There are O(log(L+1)) recovery gcd calls.
Only one detected nonunit derivative needs this recovery; the algorithm
stops once it has a proper factor. Repeating a full descent for every index
would be an unnecessary different cost model. An unbalanced comb-shaped tree
would not justify this O(L) evaluation bound.

The fixed certificate uses the raw list (0,0,5,7) modulo 35. After deduplication,

    F(T)=T(T-5)(T-7),       F'(T)=3T^2-24T+35,
    F'(0),F'(5),F'(7) mod 35 = 0,25,14.

The derivative gcds are 35,5,7. At the full value F'(0), the omitted factors
-5 and -7 give proper gcds 5 and 7. Before deduplication an omitted duplicate
would contribute a zero leaf with full gcd, illustrating precisely why the
old unrestricted single-branch argument would fail. This is an exact
arithmetic certificate, not a factoring experiment or performance evidence.

## 3. Fixed-map CRT law and exact moments

Condition on the realized map P (or the entire pre-extraction history).
Each fresh uniform input modulo N has independent uniform p and q coordinates.
Since polynomial reduction acts coordinatewise, each fresh output has law
mu_p times mu_q, and distinct fresh outputs are independent. This remains
true after an adaptive training history is fixed. It does not imply that
the two trained maps are independent when histories are averaged, and it
must not be carried through conditioning on extraction failures as an
unconditional law of the already seen samples. New batches remain fresh.

Let w_r=sum mu_r^2 and t_r=sum mu_r^3, including zero atoms. Equality of two
outputs at prime r has probability w_r. Useful means equality at exactly
one prime, so

    rho = w_p(1-w_q) + w_q(1-w_p).

For a fixed sampled output A, put x=mu_p(A_p), y=mu_q(A_q). Its useful-partner
probability is d(A)=x+y-2xy, with 0<=d(A)<=x+y. Moreover E[x]=w_p,
E[x^2]=t_p, and similarly at q; x and y are independent under the fixed-map
law. Expanding

    (x+y-2xy)^2 = x^2+y^2+4x^2y^2+2xy-4x^2y-4xy^2

gives exactly proposal (1):

    kappa = t_p+t_q+4t_p*t_q+2w_p*w_q-4t_p*w_q-4w_p*t_q.

For Y=sum_(i,j) I_ij over two independent M-lists, E[Y]=M^2*rho. In the
ordered expansion of Y^2, the event-pair counts are:

- M^2 identical pairs of events, contributing rho each;
- M^2(M-1) distinct events sharing the first-list endpoint and the same
  number sharing the second-list endpoint, contributing kappa each;
- M^2(M-1)^2 disjoint pairs of events, contributing rho^2 each.

Sharing one endpoint gives kappa by conditioning on that endpoint: the two
partners are then independent and their joint conditional probability is
d(A)^2. Events with four distinct input indices are independent even when
some output values happen to be equal. The counts sum to M^4, so there is
no missing overlap type and the coefficient 2 is necessary. Thus (2) is exact:

    E[Y^2]=M^2*rho+2M^2(M-1)*kappa+M^2(M-1)^2*rho^2.

Cauchy–Schwarz applied to Y times 1_(Y>0), equivalently Paley–Zygmund at
zero, yields (3) for rho>0 and integer M>=1:

    Pr(Y>0) >= M^2*rho^2 /
               [rho+2(M-1)*kappa+(M-1)^2*rho^2].

The detector also tests pairs internal to each list, so this is a lower
bound on its success. For M=1 the expression equals rho, as it should.
If rho=0, Y=0 almost surely and the displayed ratio is not used. In the
finite probability-law setting here, rho=0 forces both local laws to be
point masses. All outputs are then globally identical and this detector
has no useful pair.

## 4. The weighted birthday constant

For any probability law, each atom is at most sqrt(w), so

    t=sum_a mu(a)^3 <= sqrt(w)*sum_a mu(a)^2 = w^(3/2).

No flatness or additional maximum-atom promise is used. Assume w_p,w_q<=1/2
and set T=w_p+w_q<=1. Since 2w_p*w_q<=T^2/2,

    T/2 <= T-T^2/2 <= rho <= T.

Nonnegativity and d<=x+y imply

    kappa <= t_p+t_q+2w_p*w_q
           <= T^(3/2)+T^2/2
           <= (3/2)*T^(3/2)
           <= 3*sqrt(2)*rho^(3/2) < 5*rho^(3/2).

This proves (4). For M>=rho^(-1/2), dividing the exact second moment by
(E[Y])^2 bounds its three terms respectively by 1, 10, and 1:

    1/(M^2*rho) <= 1,
    2(M-1)*kappa/(M^2*rho^2) <= 10/(M*sqrt(rho)) <= 10,
    (M-1)^2/M^2 <= 1.

Consequently proposal (5), success probability at least 1/12, is valid.
The unrounded constant 1/(2+6*sqrt(2)) would also suffice; improving this
constant has no bearing on the concentration target.

The restriction is a sufficient regime, not a necessary condition for every
individual law to have a birthday bound. It cannot simply be dropped in a
uniform theorem. For example, take each local symmetric law to have masses
1-epsilon at zero and epsilon/2 at each of +1,-1. Then

    w=1-2epsilon+(3/2)epsilon^2,
    rho=2w(1-w)=4epsilon+O(epsilon^2).

For 2M sampled global outputs, the probability of seeing any nonzero local
coordinate is at most 4M*epsilon. A useful pair requires such a coordinate.
At M=ceil(rho^(-1/2)), this upper bound tends to zero. This is a symbolic
probability-law counterexample to an unrestricted claim; no reachability
claim for a trained cubic is made. The same obstruction is compatible with
finite-field atom counts by using local epsilon_r=2/r along comparable
distinct primes. It does not contradict (3).

## 5. Scheduling without rho or factor advice

Use fresh batches at widths M_j=2^j, stopping on a verified proper factor.
Let j_* be the first analysis index with M_j>=rho^(-1/2); the algorithm
does not compute j_*. Then M_(j_*)<2*rho^(-1/2), and the sum of all widths
through j_* is less than twice M_(j_*). The corresponding work is geometric
up to the specified polynomial logarithmic factors. The success probability
by the end of that stage is at least 1/12. Repeating a fixed number of
independent batches at each width amplifies this bounded-work statement;
R>=ceil(log(1/delta)/log(12/11)) gives failure at most delta by j_*.

Do not deduce expected O(M_(j_*)) work merely from the constant success
bound and one trial per doubling: 2*(11/12)>1. There is nevertheless a
direct tail proof for the proposed single-batch schedule. From (2),

    Var(Y)/(E[Y])^2 <= 1/(M^2*rho)+10/(M*sqrt(rho)).

Chebyshev bounds Pr(Y=0) by this quantity, hence it also bounds detector
failure. At width M_(j_*+s), it is at most 4^(-s)+10*2^(-s). For s>=5 this
is at most 321/1024<1/2. Fresh batches are independent at the frozen map,
so the probability of reaching successively doubled widths after that
point decays with ratio at most 321/1024. Multiplying by the doubled work
gives ratio 321/512<1. Additional fixed powers of the stage index from
logarithmic overhead remain summable. The first five overshoot stages
cost only an absolute constant times the critical-width work. Thus the
single-batch schedule has expected work of the same asymptotic order.

For an N-only cap, double only up to M=N and then repeat fresh batches at
that width. This avoids widths larger than N. The cap is sufficient in
the stated regime: w_r>=1/r and rho>=T/2 imply, with p=min(p,q),

    rho>=1/(2p),       rho^(-1/2)<=sqrt(2p)<=N.

If the cap is reached before the fifth overshoot stage, its width is at
most a constant times the critical width and repetitions have expected
count at most 12. Otherwise the preceding tail argument applies, and
repeating at the cap also converges. Neither p, q, rho, nor verification
of w_r<=1/2 is an algorithmic input. These are conditions of the theorem.
A globally constant map will not terminate successfully under an unlimited
schedule; a complete research protocol can impose a paid extraction budget
and restart training. Such bad states must remain in its success denominator.

## 6. Bit cost, monic division, and random bits

Let n be the bit length of N. Let R(n) bound a residue operation and G(n)
bound an n-bit gcd. Ordinary algorithms make both polynomial in n. Let
I(b) be the bit cost of multiplying b-bit integers. For polynomial coefficient
arrays of length at most d, choose a radix 2^b with

    b=2n+ceil(log2(d+1))+2.

Canonical nonnegative coefficients give integer convolution coefficients
less than d*N^2<2^b. Packing coefficients in this radix, multiplying the
two integers, unpacking, and reducing each coefficient modulo N yields

    B(d,n)=O(I(O(d*(n+log(d+1)))) + d*poly(n+log(d+1)))

for multiplication over Z/NZ. Reduce coefficients after every polynomial
operation. This does not construct an unreduced integer product of all
pair differences or assume roots of unity in Z/NZ.

Fast monic division is safe over this ring. Reverse the monic divisor;
the resulting power series g has constant coefficient 1. Starting with
u=1, the update u <- u*(2-g*u), truncated to doubled precision, squares
the error 1-g*u. It uses only additions and multiplications and inverts
no unknown residue. Reversal then recovers the quotient and remainder.
Apply this at the balanced remainder-tree nodes to evaluate F' at all
c_i. It is evaluation, not interpolation; no c_i-c_j is divided by.

With a regular fast multiplication bound, the product and remainder trees
cost O(B(O(M),n)*log(M+1)); the reciprocal computations fit the same bound.
Differentiation costs O(M*poly(n+log(M+1))). Sorting the 2M n-bit outputs
costs O(M*n*log(M+1)); deduplication then costs O(M*n). The gcd pass uses
O(M*G(n)). The single recovery adds O(M*R(n)+log(M+1)*G(n)). Evaluation
of 2M fresh inputs through the prescribed k-stage circuit costs
O(M*(k+1)*R(n)). Input samples and coefficients are n-bit residues, and
tree coefficients remain reduced. A fully stored tree requires
O(M*n*log(M+1)) bits, apart from multiplication workspace and the
O(k*n)-bit stored circuit.

A conservative overall bit bound is therefore

    O(M*(k+1)*R(n) + B(O(M),n)*log(M+1)
      + M*G(n) + M*poly(n+log(M+1))),

plus the explicitly described sampling convention. With quasilinear integer
multiplication this implies the parent's

    (M*(k+1) + M*polylog(M,N))*polylog(N).

For M<=N it simplifies to M*(k+1)*poly(n), with logarithmic factors retained
or absorbed in the specified polynomial. Fast integer multiplication is a
bit-machine primitive with a proved implementation, not an unbounded integer
unit operation. The publisher abstract of Harvey and van der Hoeven's
[Integer multiplication in time O(n log n)](https://annals.math.princeton.edu/2021/193-2/p04)
states such a bit bound in the multitape Turing model. Only that abstract
and metadata were inspected and frozen; no claim is made to have audited
the full multiplication proof. A weaker standard quasilinear integer
multiplier also suffices. Schoolbook polynomial arithmetic instead gives
a quadratic-in-M cost envelope and does not justify the displayed fast bound.

Exact uniform residues from unbiased bits require care. Drawing n bits and
rejecting values at least N has acceptance probability greater than 1/2,
and expected O(n) random-bit and comparison work per accepted residue.
This establishes the stated expected-work convention; it has no fixed
worst-case rejection count. For a bounded alternative, allow

    h=ceil(log2(2M/delta_s))

draws per input and abort the batch on a cap failure. Its total cap-failure
probability is at most delta_s by a union bound, with O(M*n*h) bit work.
Conditional on successful sampling, outputs are exactly independent uniform
samples: acceptance counts do not bias accepted values. The batch success
bound then becomes at least (1-delta_s)/12, rather than an unqualified
1/12 for every capped implementation. All cap failures are paid failures.
This is a constant or logarithmic accounting change, not an exponent gain
or loss. Reducing a fixed n-bit word modulo N would instead bias the law.

The monic tree and series-inversion argument above is self-contained and
matches the frozen W008 control. No novelty claim or broad prior-art search
is attached to these standard primitives. The
[primary-source manifest](W010-batch-extraction-review-sources-manifest.json)
records the one used publisher source and two unsuccessful web opens, neither
of which is used as evidence.

## 7. What the concentration target does and does not require

For a trained odd law, w_r=m_r^2+v_r. It is the full w_r, not v_r alone,
that enters the useful-pair probability. In the regime used above,

    (w_p+w_q)/2 <= rho <= w_p+w_q.

With the sequential evaluator and birthday-scale extraction, a successful
fixed-state cost comparison pays training A_k as well as approximately
(k+1)/sqrt(rho), with the bit/log factors of section 6. Against the matched
identity-map sqrt(p) control, an asymptotic saving in that arithmetic scale
requires

    A_k=o(sqrt(p)),       p*rho/(k+1)^2 -> infinity.

For k>=1 this is precisely the intent of (6). A fixed exponent saving epsilon
would require the stronger scale rho at least (k+1)^2*p^(-1+2epsilon),
and a corresponding acquisition bound, before logarithmic and success-tail
penalties are included. Merely an unbounded logarithmic improvement in the
ratio would not establish an exponent change.

The width scale has a simple detector-specific check: the union bound over
all unordered pairs in 2M independent samples gives

    Pr(detector succeeds) <= binom(2M,2)*rho.

So fixed-state constant success needs M=Omega(rho^(-1/2)) for this pair
detector. Charging a constant amount of work at every stage of the specified
sequential circuit then gives the stated evaluation comparison. An O(k)
upper bound alone would not prove a lower bound for all representations of
P; a cheaper evaluator or a different extraction mechanism is outside this
comparison. This is not a lower bound on factoring algorithms.

In particular, rho of order k/p gives evaluation cost of order sqrt(p*k),
whereas rho of order k^2/p only returns the sqrt(p) scale. These statements
are conditional scaling calculations, not established reachable-law growth
rates. The primary unresolved cost is obtaining the right law with a useful
probability. A favorable mean of v across histories cannot be substituted
for that probability, especially after survival conditioning.

For a concrete sufficient acquisition statement, a bounded training protocol
could prove that an event G of full-tape probability at least eta produces a
state with w_p,w_q<=1/2, rho>=rho_0, and depth at most k, within paid work A.
An implementable, budgeted extraction schedule that reaches the required
width would then succeed with probability at least eta/12 on those states;
failed charts, bad states, and earlier stops remain charged. With a per-trial
expected work bound A+C that includes sampling, independent identically
distributed restarts cost at most 12*(A+C)/eta in expectation. This renewal
bound allows trial cost and trial success to be correlated. Here rho_0 and the hidden
primes are analysis parameters, never free runtime advice; the actual width
budget must be selected from allowed inputs or reached by an N-only schedule.
Small eta can erase any apparent savings. Earlier factors found during
training can only add success, but cannot justify discarding failed tapes.

## 8. Disposition and next mathematical gate

Accept duplicate-safe extraction, exact moment formulas (1)–(3), weighted
birthday inequalities (4)–(5), and the specified linear recovery cost.
Retain the detector as an already priced control for cubic acquisition.
Record the balanced-tree, fast-multiplication, exact-sampling, and scheduling
qualifications when using its cost. The strengthened dyadic tail proof
repairs any attempt to infer expected cost from setup cost alone.

The next question is a quantitative reachable-family theorem: can a paid
cubic training protocol attain the concentration threshold while keeping
both its acquisition cost and the probability penalty under control? An
alternative is an explicitly cheaper evaluator or a different extraction
primitive that changes that threshold. No depth sweep is selected by this
review, and positive drift alone supplies no reason to select one. The B
envelope and C selector have their own reviewers; neither is settled here.

All delivery files and hashes are listed in
[the delivery manifest](W010-batch-extraction-review-manifest.json).
