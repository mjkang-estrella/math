# W032 joint-lift coordinates: independent symbolic review

**Disposition: accept the known-branch coordinate, fiber bijections, joint
uniformity, and exact squarefree-semiprime digit-gcd probability, with the
precision and accounting qualifications below. Verified complete factoring
improvement: NONE.** The proofs work over composite moduli, including prime
powers. They apply to uniform sampling of the entire lift fiber, not to the
canonical interval used by the completed assay.

Two literal wording repairs are needed in the frozen target. Its increment
laws at lines 46–54 must use **1 <= s < L** when W and Phi are defined only
modulo N^L. Its assertion at lines 20–21 that every G_k is divisible by x
means **k >= 1**; G_0=1 is the exception. Neither repair changes the joint
distribution theorem. The cost and comparison at lines 38–41 and 65–85
are valid with the explicit scope in sections 6–8 below: fresh full lifts,
individual digit gcds, charged acquisition and randomness, and no free
inverse-coordinate oracle or general adaptive-consumer simulation.

The review concerns the complete frozen
[joint-lift note](W032-joint-lift-review-evidence/inputs/research/findings/W032-joint-lift-coordinates.md),
SHA-256 `7387efff33ab67ceaea3f46afc67fd4a5450d96b139acac1fde68973abd45d46`.
The [full brief](W032-joint-lift-review-evidence/brief.txt) and
[23-file input manifest](W032-joint-lift-review-evidence/input-manifest.json)
were frozen before target analysis. The scalar and single-top-digit reviews
are completed, accepted imports through the frozen symbolic parent
disposition; the target's references to those reviews as live are historical.
This is their new, separate extension, not a continuation of either review.

No numerical experiments, sample evaluations, symbolic computation program,
Lean proof, assay rerun, or project checks were performed. The mathematical
evidence is the general symbolic proof below. Prior assay counts have no role
in it. File copying, JSON processing, and SHA-256 checks are administrative
integrity work. W033's live separating-cover audit was neither read nor
duplicated. No novelty claim or external technical source is used.

## 1. Large representatives, coefficient ring, and exact precision

Let N>1, R>=1, leastprime(N)>2R+1, and gcd(a,N)=1. Set

    L=2R-1,  M=N^(L+2)=N^(2R+1),  M_big=N^(L+4)=N^(2R+3),
    D=4^R(2R+1)!,  S=Z[1/D],  n=(N-1)/2,  C=(-4)^n.

All rational polynomial congruences in this review take place in S. The
map from S to Z/N^h Z exists at every needed h, because gcd(D,N)=1. It
interprets a rational coefficient by inverting its denominator at the
specified precision; it does not round a rational number or invert N.
In particular 2, 12 and 24 are units. At R=1 the hypothesis is
leastprime(N)>3 and D=24: a prime factor 5 is allowed. The stronger 5-unit
condition for the old canonical d_2 formula is unnecessary for R=1.

The accepted integer identity, with J_N(X)=sum_j b_j X^j and b_0=NC, is

    A_exact=Na J_N(N^2 a^2)
           =N^2 aC + sum_(j>=1) b_j N^(2j+1) a^(2j+1).

It is a polynomial identity for every integer a, including large and
negative representatives. Every displayed term is divisible by N^2. Pair
powering modulo M_big therefore gives a canonical A_bar divisible by N^2,
and A_bar/N^2 agrees with A_exact/N^2 modulo M. Multiplication by
(aC)^(-1) modulo M is legal. This produces the same canonical V_R as the
original construction, with no dependence on an assumed bound a<N.

After cancellation, the normalized polynomial over Z[1/2] is

    1 + sum_(j>=1) N^(2j-1) b_j C^(-1) a^(2j).

For j>R the explicit N-power is at least N^(2R+1); those terms vanish
modulo M for every integer a. This uses integral b_j, not the false general
assertion N|b_j. For j<=R the accepted coefficient formula has unit
denominators and gives

    V_R(a) = 1 + sum_(k=1..R) N^(2k) G_k(a^2)  (mod M),
    G_k(x)=sum_(j=ceil(k/2)..k) c_(j,k-j) x^j,
    G_1(x)=x/24.

The collection and truncation are formal in S[a]. Evaluating at a larger
integer cannot remove a factor of N from a discarded term. This establishes
the required extension; finite canonical-input checks would not establish it.

Since canonical V_R is congruent to 1 modulo N^2, the ordinary integer

    U(a)=(V_R(a)-1)/N^2

lies in [0,N^L). Exact division loses two N-adic digits: from precision
N^(L+2) for V_R we obtain exactly precision N^L for U. Combined with the
earlier A division, the acquisition uses M_big=N^(L+4). It would be wrong
to obtain A only modulo N^L and then retain that precision after dividing.

Define F(a)=sum_(k=1..R) N^(2k-2)G_k(a^2) in S[a]. Then U=F(a) modulo
N^L. Polynomial congruence preservation shows that this U, and hence V_R
modulo M, depend only on a modulo N^L. Use the canonical representative
a=a0+Nt, with 1<=a0<N and 0<=t<N^(L-1), for the width bound. It has
O(R log N) bits. Arbitrarily long supplied integer representatives require
their own input-reading and reduction cost. Reducing a all the way modulo
N would discard the very lift digits under study.

## 2. The square coordinate is a polynomial, not a rational-function trick

For k>=1 every exponent j in G_k satisfies j>=ceil(k/2)>=1. Thus x divides
G_k(x) in S[x]. With an empty sum interpreted as zero, define

    T(x)=24 sum_(k=2..R) N^(2k-4) (G_k(x)/x) in S[x].

Here G_k/x is polynomial division by its known factor, not evaluation of
an inverse variable. At R=1, T=0. Therefore the polynomial

    W_tilde(a)=24 F(a)=a^2[1+N^2 T(a^2)]

reduces to the proposed W=24U modulo N^L. Its formal derivative satisfies
W_tilde'(a)=2a modulo N. One need not generate the G_k table or T to
evaluate W: the scalar computation and exact divisions above suffice.

For any polynomial H over S there is a polynomial E with

    H(a+h)-H(a)=h H'(a)+h^2 E(a,h).

This follows from binomial expansion and uses no factorial inverses from
Taylor's theorem. For h=N^s t and s>=1, 2s>=s+1, so

    W_tilde(a+N^s t)-W_tilde(a)=2a N^s t  (mod N^(s+1)).       (A)

For the residue-valued W modulo N^L, (A) is available when 1<=s<L.
At s=L, for example, the two arguments are the same class modulo N^L,
whereas 2a N^L t need not vanish modulo N^(L+1). Thus the unrestricted
statement is not a congruence of the stated finite-precision objects.
One could instead extend W_tilde to higher precisions, but no such
extension is needed for this theorem. R=1 has no incremental steps.

## 3. Composite-modulus Newton lifting and uniqueness of the fixed branch

Fix a and let w be any integer representative of W(a) modulo N^L. Start
with y=a modulo N. It is a unit and y^2=w modulo N. If a current unit y
satisfies y^2=w modulo N^s, set k=min(2s,L) and compute

    y_new=(y+w*y^(-1))*2^(-1) modulo N^k.

The inverses are taken modulo N^k. Using rational notation in the
localization at all integers coprime to N gives the exact identities

    y_new-y=-(y^2-w)/(2y),
    y_new^2-w=(y^2-w)^2/(4y^2).

Consequently the branch is unchanged modulo N^s and the error vanishes
modulo N^k. Iteration reaches N^L in ceil(log2 L) updates when L>1.
All subsequent y remain congruent to the unit a modulo N. Extended gcd
computes the inverses without factorization. This proof uses ideal
divisibility, not a field assumption or a prime-modulus Hensel oracle.

Existence follows from this algorithm. For uniqueness, if y and z are two
roots with y=z=a modulo N, then

    (y-z)(y+z)=0 modulo N^L,  y+z=2a modulo N.

The second factor is a unit, even when N is composite or a prime power.
Multiplying by its inverse gives y=z modulo N^L. The same argument at
lower precisions shows that roots reduce compatibly. Define this unique
root to be Phi(a).

It is a root in the already specified residue branch a modulo N. For
squarefree N=pq, that fixes the root sign at both prime components;
Newton's iteration cannot independently change one of those signs. In
particular gcd(Phi(a)-a,N)=N and gcd(Phi(a)+a,N)=1. There is no new
independent root for the standard square-congruence splitting step, and
no procedure here for choosing a branch of an arbitrary unseeded radicand.

## 4. Fiber bijections and the exact Phi increment

Fix a unit a0 modulo N. At precision s=1 the source fiber contains only
a0 and the W-target fiber contains only a0^2. Suppose there is a unique
preimage a_s modulo N^s of a prescribed target modulo N^s. All extensions
are a_s+N^s t, with t in Z/NZ. Equation (A) says their next output digits
differ by (2a0)t, plus the fixed digit determined by a_s. Since 2a0 is
a unit modulo N, every next output digit has exactly one preimage.
Induction up to s=L-1 proves

    W: {a mod N^L: a=a0 mod N}
       -> {w mod N^L: w=a0^2 mod N}

is a bijection. There are N^(L-1) elements on each side. No unproved
mixing or independence assumption is used.

For 1<=s<L put a'=a+N^s t, y=Phi(a), and y'=Phi(a'). Reduction
compatibility and uniqueness give y'=y modulo N^s. Subtract the squares:

    (y'-y)(y'+y)=W(a')-W(a)=2a N^s t modulo N^(s+1).

Since y'+y=2a modulo N is a unit, divide by it and obtain

    Phi(a+N^s t)-Phi(a)=N^s t modulo N^(s+1).              (B)

This proves, by the same digit induction, that Phi is a bijection of
the a0-fiber to itself. The coefficient 1 in (B) is the response of the
next digit when lower digits are fixed; it does not say Phi(a)=a modulo
N^L. Offsets depending on the lower digits remain. Both bijections and
(B) are valid for nonsquarefree N under the same unit guard.

## 5. Canonical carries, indices, and joint uniformity

Multiplication by 24^(-1) permutes Z/N^L Z and maps the W-target fiber
bijectively onto the fiber with fixed residue

    u0=[a0^2*24^(-1)]_N.

Although this multiplication can create carries, its bijectivity on the
whole fiber is what is needed. For uniform a in the full source fiber,
the canonical U is uniform on

    {u0+u1 N+...+u_(L-1) N^(L-1): 0<=ui<N for i>=1}.

Each high-digit tuple has exactly one preimage. Thus u1,...,u_(L-1)
are jointly independent uniform residues. This counts the full tuple;
separate uniform marginal statements would not suffice.

There is also an exact equality of canonical integers

    V_R=1+N^2 U,  0<=U<N^L,  1+N^2 U<N^(L+2).

The bottom two base-N digits of V_R are respectively 1 and 0. For
1<=r<=R, ordinary integer division gives

    d_r = floor(V_R/N^(2r)) mod N
        = floor(U/N^(2r-2)) mod N
        = u_(2r-2).                                      (C)

To verify the floor, write U=N^(2r-2)q+b with 0<=b<N^(2r-2).
The discarded lower block N^2 b+1 is strictly less than N^(2r).
The case r=1 has b=0 and is included. Thus no carry from the leading
1 was suppressed in (C).

The indices are precisely 0,2,4,...,2R-2=L-1. Hence d_1=u0 is fixed
and a unit; d_2,...,d_R select the R-1 distinct coordinates
u2,u4,...,u_(L-1) and are independent uniform. There are another R-1
independent high coordinates at odd indices of U, which this algorithm
does not test. Testing them as well would give more ordinary random gcd
arguments, not more information per tested uniform argument.

For R=1, L=1, both fibers have one element, U=u0, Phi=a0 modulo N,
and the selected high-digit list is empty. Uniformity of that empty
list is vacuous and the digit-split probability is zero. There is no
root iteration or lift randomness in this case.

## 6. Exact success probability and the adaptive boundary

Let N=pq with distinct primes on the guarded branch. A uniform residue
c modulo N has a proper gcd with N exactly when it is a nonzero multiple
of p or a nonzero multiple of q. These disjoint sets have q-1 and p-1
elements. Thus, writing sigma_N=(p+q-2)/(pq), (C) gives exactly

    Pr[at least one proper gcd among d_2,...,d_R]
      =1-(1-sigma_N)^(R-1) <= (R-1)*sigma_N.               (D)

This is the probability of the displayed event, not merely a lower bound
on that event. An algorithm that also performs other factor-producing
operations can have a different total success probability. Initial
gcd(a0,N) successes, denominator-guard splits, other scalar observations,
and additional consumers must be accounted for separately. A zero digit
has gcd N and is not a successful split.

For general N, the same joint-uniformity proof holds but the single-gcd
probability is (N-phi(N)-1)/N. For N=p^e it is 1/p-1/p^e, not the
distinct-semiprime formula. These are counting descriptions, not an
instruction to compute phi(N) or use the unknown factors in an algorithm.

Conditional on any history that fixes N,R and a unit a0 *before* fresh
independent lift randomness is drawn, the same high-digit product law
holds. Adaptive selection of a0 from previous information therefore
does not bias these fresh coordinates. The original selection cost and
any information in the history remain present. For a fixed number of
fresh digit tests, ordinary early stopping on a proper gcd preserves
the corresponding success-within-that-budget event.

The law does not justify replacing selected or reused lifts, correlated
randomness, sampling without replacement, output-dependent rejection, or
a random stopping count by an independent fixed-size experiment. In
particular one may not insert an observed adaptive number of tests into
(D) as though it had been fixed in advance. If R is chosen from prior
history, (D) holds conditionally for that batch; averaging must use that
conditional law.

Directly sampling R-1 independent uniform public gcd arguments has
exactly the same digit-gcd transcript and stopping distribution for a
consumer observing those digits and their gcds, conditional on the same
prior history. It avoids scalar acquisition and the extra unused lift
randomness. This is the precise no-amplification comparison.

It is not a cheap simulation of every computation observing the sampled
a, the full quadratic pair, or relationships between input and output.
Those can be correlated with the digits. Nor does it remove acquired
base information, constrain a different selector, or lower-bound a batch
consumer. A product gcd of N can collect p and q from different leaves
even when neither leaf is zero modulo N; any localization must be paid.
Keeping those distinctions preserves the qualifications accepted in the
earlier single-top-digit review.

## 7. Acquisition, known-root computation, digits, gcds, and randomness

Let b=bitlen(N), B=(2R+3)b, and let F(k) bound the chosen finite-width
modular multiplication/reduction, integer division, gcd, and inversion
routines at k-bit size. Use fast arithmetic only when specializing this
primitive-cost envelope; a count of arithmetic stages is not a bit bound.

The denominator guard can be checked by a modular product of the small
integers through 2R+1 and a gcd, or by individual gcds. It costs
O(R F(b)) on the accepted branch, where R<N. A full product gcd N
requires localization if a factor is desired; a failed guard is outside
this theorem. Choosing a0=1 requires no random unit search. Other base
selection and failed samples retain their actual cost and outcomes.

Construct the moduli, form reduced z=Na and Delta=z^2-4, execute O(b)
pair-powering stages, compute C=(-4)^n modulo M, invert aC, perform the
two exact divisions at their stated precisions, and multiply by 24.
A conservative bound for this acquisition, with the branch check, is

    C_acq=O((b+log(R+1)) F(B) + R F(b)).                   (E)

It includes modulus construction, input reduction at the promised width,
unit checks, and normalization. It needs no G_k table. The initial base
strategy's cost is additional when not covered by the supplied-base
contract. Exact enormous A_exact is never materialized.

Given W, known-branch root computation adds

    O(sum_(j=1..ceil(log2 L)) F(b*min(2^j,L)))              (F)

for L>1, and zero updates for L=1, plus small initial reduction. Each
term includes the inversion at that precision and the Newton arithmetic.
Root computation is optional for the digit-gcd algorithm: the probability
proof and digit extraction only need U. There is no hidden root oracle.

A fast divide-and-conquer radix conversion extracts the O(R) base-N
digits with an upper bound O(F(B) log(R+1)) under the usual superadditive
fast-arithmetic bound. It retains both parities before selecting (C).
A literal repeated-division implementation instead has its own, possibly
larger, cost; O(R F(B)) is a safe coarse bound for that method. The
selected R-1 tests add O(R F(b)), including checking a returned divisor.
Early stopping can save some of these tests but is not assumed in the
worst-case acquisition bound.

With quasi-linear multiplication/division and fast gcd, (E), (F), fast
radix conversion, and the individual gcds fit soft O((R+1)b^2), plus
the separately charged base strategy and sampling. This substantiates
the target's less explicit soft O(R poly(log N)) on its guarded branch.
It is a conditional arithmetic upper bound, not a newly certified
implementation or a factoring-time theorem. It is polynomial in the
original input length only when R and the rest of the strategy are
polynomially bounded in b.

Exact full-fiber sampling can choose t uniformly from [0,N^(L-1)) and
return a0+Nt. Rejection of bit strings outside this interval has acceptance
probability greater than 1/2 and uses O((L-1)b)=O(Rb) random bits in
expectation for L>1. Generating and comparing the sampled bit blocks
costs O(Rb) expected bit work. Constructing the range and forming a0+Nt
use the charged modulus setup and arithmetic in (E). Alternatively sample
L-1 independent base-N digits; their assembly needs a charged radix
conversion. Neither method grants a finite worst-case rejection count.
For R=1, choose t=0 with no random bits.

For example, capping the single-block rejection sampler after K attempts
gives a failure probability less than 2^(-K). Conditional on sampling
success, the sampled lift remains exactly uniform; if sampling failure
returns no factor, its unconditional digit success is

    Pr[sampling succeeds] * [1-(1-sigma_N)^(R-1)].

Any bounded-randomness or bounded-time claim must retain that failure
term and the worst-case K-times sampling cost. Expected randomness is
not the bounded-random-tape contract in docs/SPECIFICATION.md.

Scalar and Newton registers have O(Rb) bits each; fast arithmetic's
workspace, random buffers, saved digits, and any product trees are
additional. Explicitly retaining all output digits costs O(Rb) bits.
Neither that width nor the compact mathematical coordinate map implies
free materialization of the N^(L-1)-element family.

## 8. Inverting the coordinate is a separate, paid task

The target's final paragraph about forcing a square target is valid as
a constructive existence claim, not as a free consequence of the root
cost (F). Given any w_star modulo N^L with w_star=a0^2 modulo N, start
with a_1=a0. At stage 1<=s<L, evaluate W(a_s) modulo N^(s+1) and choose

    t = ((w_star-W(a_s))/N^s) * (2a0)^(-1) modulo N,
    a_(s+1)=a_s+N^s t.

The quotient is exact after choosing representatives agreeing modulo
N^s; changing representatives by N^(s+1) does not change t modulo N.
Equation (A) proves the next congruence. This acquires the unique input
for w_star without factors. To prescribe Phi(a)=y_star in the a0 branch,
take w_star=y_star^2 and use root uniqueness.

This simple implementation uses up to L-1 scalar evaluations, not just
the O(log L) arithmetic updates used for a root of an already supplied W.
Using full precision every time gives the conservative bound
O(L*C_acq+L*F(B)); at fast arithmetic this is at most soft
O((R+1)^2 b^2), in addition to target construction. Lower-precision or
more sophisticated inverse evaluation may improve it, but none is
provided or needed here. The map's bijectivity alone is not a near-linear
cost proof for inversion.

Likewise prescribing U (and hence desired output digits) is possible
after setting w_star=24U with the required base residue. It transports
already chosen public gcd arguments; a residue already having a proper
gcd does not acquire a new factor-selective property by this transport.
Finding useful targets or consuming many targets still requires its own
algorithm and complete cost and success analysis.

## 9. Disposition, remaining question, and evidence closure

The failed improvement premise is that the tested higher digits from a
fresh fully randomized lift obtain greater separating yield than the
same number of ordinary random gcd arguments. They have exactly the
same joint law, by a finite symbolic bijection. One scalar evaluation
does acquire all those digits, but direct random arguments avoid that
acquisition. This says nothing against all algorithms for selecting or
batching public arguments.

The original canonical a<N distribution selects one specific lift in
each residue fiber. Conditioning a full-fiber theorem on that singleton
does not leave the higher digits uniform. The canonical floor problem
therefore remains open at the scope stated by the prior reviews. A
result that changes its disposition must prove a useful separating law
for those actual representatives or a different explicitly priced input
selection/consumer. This review neither launches another assay nor
duplicates the separate live W033 cover audit.

The [read-scope record](W032-joint-lift-review-evidence/read-scope.json)
distinguishes mathematical imports, complete reads, context excerpts,
and frozen provenance files. The
[integrity record](W032-joint-lift-review-evidence/integrity-preflight.json)
checks all frozen bytes, the two imported review reports against their
prior sealed manifests, and live-source drift. It does not certify the
proofs or re-audit every payload of the earlier deliveries.
At preflight, the live STATE and W032-lift-control note had changed;
the frozen target and other frozen inputs still matched their live
sources. This review retains the frozen versions and the supplied brief.

The [full delivery manifest](W032-joint-lift-review-evidence/delivery-manifest.json)
contains the report and every evidence payload's path, size, and SHA-256.
It excludes itself and the
[terminal anchor](W032-joint-lift-review-evidence/terminal-manifest.sha256)
to avoid circular hashing. The anchor hashes the final manifest bytes,
and the same hash is returned externally in the terminal handoff. The
report and payloads are sealed before that manifest is generated.

Only this report and W032-joint-lift-review-evidence/ were written. There
were no installs, commits, delegation, shared source or Lean changes,
STATE or task-registry changes, numerical experiments, or project checks.
This is a reviewed prose theorem for the specified input distribution,
not formal machine verification, a general factoring lower bound, or a
verified complete complexity improvement.
