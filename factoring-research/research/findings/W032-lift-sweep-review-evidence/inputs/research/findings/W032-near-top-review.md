# W032 near-top difference: independent symbolic review

**Disposition: ACCEPT the linear residual identity, integer/unit coefficient,
strict carry bound, unconditional interval counts, and guarded uniform-start
trial bound. Adopt the narrow selector-wording repair in section 7. The added
globally small-signal obstruction also holds. Retaining the linear trend does
not remove the acquisition/yield gate for this sampler. Verified complete
factoring improvement: NONE.**

This is a theorem about the specified final filtered gcd and initial input
nonunit exits. It is not a theorem about individual digit gcds, conditional
unit resampling, adaptive or nonuniform input selection, all batch consumers,
or factoring in general. No numerical experiment or assay replay occurred.

## 1. Frozen target and accepted interfaces

The full reviewed target is the 112-line
[near-top proposal](W032-near-top-review-evidence/inputs/research/findings/W032-near-top-difference.md),
SHA-256 `26a8430756d06b881f9702b45a208ab625432573d7f6742a794b688ff072dd36`.
The [complete brief](W032-near-top-review-evidence/brief.txt) and
[15-input manifest](W032-near-top-review-evidence/input-manifest.json) were
frozen before the substantive proof audit. All five governing documents,
the full target, original W032 hypothesis, scalar/carry review, symbolic
parent disposition, high-order proposal/review, and joint-lift review were
read. STATE was frozen in full; only its first 215 lines were used for
coordination. Exact read coverage is in
[read-scope.json](W032-near-top-review-evidence/read-scope.json).

Sections 5, 7, and 8 of the accepted scalar/carry review supply the exact
floor interface and scalar acquisition cost. Its parent disposition accepts
those interfaces. The completed high-order review covers order 2R+1 and
explicitly excludes the present lower order. Its frozen delivery manifest
matches the supplied external SHA-256
`34e2cd3a26f5fc96558e2ab99d536a93923becd97030668b2529eb349025dacd`;
its report matches that manifest's report entry. This limited provenance
check does not duplicate the parent's intake of the other prior payloads.
The joint-lift result concerns the entire high-lift fiber and supplies no
uniform-digit law for the canonical starts here. Its proofs are not rerun.
The target's descriptions of an earlier review as live are historical.

All new mathematical evidence below is symbolic prose. File inspection,
copying, JSON processing, and cryptographic hashing are the only executed
computations. No candidate evaluation, formal-polynomial program, numerical
experiment, assay-source/result read, or Lean/project test was performed.
Existing assay descriptions in the required inputs are context only. No
novelty or fresh literature claim is made; the accepted local interfaces
and the elementary derivations below suffice.

## 2. Exact surviving polynomial and strict residual

Let R>=1 be integral, N>1 with leastprime(N)>2R+1, and define

    s=2R-1,  D=4^R(2R+1)!,  L0=N-sD>0,
    a_i=a0+iD,  0<=i<=s,  a0 in {0,...,L0-1}.

The full filter is defined only when every a_i is a unit modulo N. Initial
nonunit outcomes are handled separately. These bounds put every point in
[0,N); they do not guarantee unit points. Since D is a multiple of every
required coefficient denominator and coprime to N, the accepted interface
uses integer polynomials C_k=D G_k and

    F(N,a)=sum_(k=0..R) N^(2k) C_k(a^2),  M=N^(2R+1),
    e=[C_R(a^2)]_D,  h=[-F(N,a) M^(-1)]_D.

The inverse in h is modulo D. Polynomial congruence preservation makes e
and h constant on each D-spaced stencil, even though both may change with
a0. Write

    J(i)=G_R((a0+iD)^2)-e/D,
    Q(i)=e/D+hN/D+sum_(k<R) N^(2k-2R)G_k((a0+iD)^2).

J has integer values at integer i, and the exact imported floor identity is

    d_R(a_i)=J(i)+floor(Q(i))  (mod N).

The negative powers of N in Q are rational numbers inside a real floor;
N is not inverted modulo N. Here deg_i Q<=2R-2<s. The underlying polynomial
G_R(a^2) has only even powers of a, with leading coefficient

    P_R=product_(j=1..R)(2j-1)^2,  g=P_R/D.

This even-power assertion is in the variable a, not the translated variable
i. Substitution a=a0+iD generally creates odd powers of i. Every lower
power of a has degree at most 2R-2 and is therefore annihilated by the
order-s difference. Only g*a^(2R) remains.

For d=s+1, the ordinary forward difference identity is

    Delta_D^s x^(s+1)=(s+1)! D^s (x+sD/2).

For completeness, in the formal series ring Q[x,D][[t]],
Delta_D^s exp(tx)=exp(tx)(exp(tD)-1)^s. Since
(exp(tD)-1)^s=(tD)^s(1+sDt/2+O(t^2)), its coefficient of t^(s+1),
multiplied by (s+1)!, is exactly the displayed expression. This is a
formal coefficient identity, with no numerical approximation or substitution.
It proves the needed identity over Q before any modular interpretation.
Consequently

    Delta^s J(0)=A*u,
    A=g*(2R)!*D^(2R-1)=P_R*(2R)!*D^(2R-2),
    u=a0+sD/2.                                             (2.1)

This second expression proves A is an integer for every R>=1. Each prime
divisor of A is at most 2R+1, so gcd(A,N)=1. D is even, so u is an integer.
No factorial inverse or rational denominator remains in (2.1).

Set w_i=(-1)^(s-i)binom(s,i) and

    c=Delta^s floor(Q)(0)=-Delta^s {Q}(0) in Z,
    B=2^(s-1)=4^(R-1).

The equality uses Delta^s Q=0. The signed weights sum to zero, their
absolute sum is 2^s=2B, and their positive and negative total magnitudes
are each B. Each fractional part lies in [0,1), including for negative
Q(i). Each weighted positive or negative fractional-part sum is therefore
in [0,B), strictly at its upper endpoint. Their difference gives

    |c|<B,  c in {-B+1,...,B-1},
    Z=sum_(i=0..s) w_i d_R(a_i)=A*u+c  (mod N).             (2.2)

Canonicalizing the digit representatives changes this integer sum by a
multiple of N. Thus gcd(Z,N)=gcd(A*u+c,N), without requiring the latter
integer to be small. No carry independence or distribution is assumed.

For R=1, s=1, D=24, B=1, and Q is constant. Hence c=0 exactly,
A=2, and Z=2(a0+12) modulo N. This also follows symbolically from the
accepted d_1(a)=a^2/24. Only leastprime(N)>3 is required. Although each
individual first digit on a unit point is a unit, the difference need not
be a unit. The high-order filter's identically full gcd at R=1 does not
transfer to this two-point filter. No exception excluding R=1 is needed.

## 3. Counts over the entire start interval

Fix a prime p dividing N. By (2.2), every valid stencil with p|Z satisfies

    a0=-sD/2-c*A^(-1)  (mod p)

for some integer c with |c|<B. A and sD/2 do not vary with a0. Thus these
starts lie in at most min(p,2B-1) residue classes modulo p, even though
the actual c depends on all of a0 and on its changing small labels.
There is no additional factor D in this count: the same containing set
of possible c values applies across every label class.

Every residue class modulo p contains at most ceil(L0/p) integers in
{0,...,L0-1}. Defining E_p to include only valid unit stencils, we get

    |E_p| <= min(L0, min(p,2B-1)*ceil(L0/p))
          <= min(L0, (2B-1)*ceil(L0/p)).                   (3.1)

This is a containing-set bound, not a claim that the actual event E_p is
periodic modulo p or that every possible root is attained. It remains
valid for repeated prime factors in N. It is unconditional over the entire
start interval; invalid stencils simply do not belong to E_p.

Now let N=pq for distinct primes, p<=q. For a start uniform over all L0
integers, the proper FILTER event is E_p symmetric-difference E_q.
Their intersection produces gcd N. Using (3.1) and
ceil(L0/p)/L0<=1/p+1/L0 gives

    Pr[proper FILTER]
      <= min(1,(2B-1)*(1/p+1/q+2/L0)).                    (3.2)

For the initial checks, p|a0+iD specifies just one residue class of a0
modulo p for each i. A union bound over the 2R=s+1 points and both primes
gives

    Pr[any initial nonunit]
      <= min(1,(s+1)*(1/p+1/q+2/L0)).                    (3.3)

An initial gcd N is not a split, so (3.3) also upper-bounds proper initial
exits. Checking points sequentially and stopping early can only reduce the
visited event set. No independence between points or prime components is
used. Combining the two accepted output channels gives

    mu:=Pr[any proper output in one stated trial]
      <= min(1,(2B-1+2R)*(1/p+1/q+2/L0)).                (3.4)

The trial retains invalid starts and full-gcd outcomes in its denominator.
If starts were resampled until all points were units, the conditional
filtered probability would have denominator equal to the number of unit
stencils, not L0. That conditional algorithm and its rejected-start costs
are not being analyzed by (3.2). Likewise (3.4) excludes individual digit
gcds, cross-trial gcd combinations, and any other added output channel.

## 4. Uniform asymptotics and the actual trial requirement

The finite bounds above need only L0>0. For the claimed asymptotics assume
sD<=N/2, so L0>=N/2. Put ell=log N. The last R+1 factors of (2R+1)! are
at least R+1, giving

    (R+1)log(R+1)<=log D<ell.

This implies R=O(ell/log ell) uniformly, including bounded or oscillating
choices of R. One elementary check splits at R=sqrt(ell): below it,
R<=2ell/log ell for large ell; above it, log(R+1)>(log ell)/2 and the
same bound follows from the displayed inequality. Hence

    log B=O(ell/log ell),
    2B-1+2R=exp(O(ell/log ell))=N^o(1).                  (4.1)

In particular the initial-gcd multiplier 2R, as well as B, is included.
For p<=q and L0>=N/2, (3.4) implies

    mu <= (2B-1+2R)*(2/p+4/N)
        <= 6*(2B-1+2R)/p.

On any family with fixed epsilon>0 and p>=N^epsilon, log N<=log p/epsilon.
The uniform error term in (4.1) therefore gives

    mu <= p^(-1+O_epsilon(1/log log N))=p^(-1+o(1)).       (4.2)

The width margin is essential to this inference: L0>0 by itself permits
a very short start interval, and the 2/L0 boundary term need not be small.
A varying epsilon(N) also needs its own comparison. The hypotheses for
large-factor semiprime families are meaningful only when such families
exist; no all-composite claim follows.

For K fresh uniform trials of this specified filter at fixed N,R, a union
bound gives success within K attempts at most K*mu. Early termination on
a success is covered by viewing the remaining random starts as unused.
Thus achieving any fixed success level delta>0 requires

    K >= delta*p/[6*(2B-1+2R)] = p^(1-o(1)).              (4.3)

This is a necessary number of attempts, not a sufficient number or a
positive success guarantee. The actual probability may be zero. Independence
of the carry values is never needed. The repeated-trial statement concerns
fresh uniform starts and these output events, not an adaptive nonuniform
algorithm or a batch algorithm consuming additional relations among trials.

Every such literal trial has positive bit cost. Relative to the already
accepted soft sqrt(p) small-factor-search comparator named in the brief,
(4.3) rules out an improvement by this sampling model on the stated family;
its poly(log N) factors are p^o(1) under p>=N^epsilon. The comparator is an
import, not a new literature or implementation claim. The scalar upper cost
below must not be multiplied by (4.3) and relabeled as a lower bound on all
possible evaluators. The attempt count alone settles this scoped comparison.

## 5. Acquisition, weights, preprocessing, and sampling costs

Let b=bitlen(N), H=bitlen(N^(2R+3))=Theta((R+1)b). Use the accepted
single-top-digit scalar bound, including its initial unit check,

    C_scalar=O((b+log(R+1))*(M_int(H)+Div(H))
               + Gcd(H)+Gcd(b)).                         (5.1)

M_int, Div, and Gcd denote paid finite-width multiplication, division,
and extended-gcd bounds. This covers the moduli, O(b) quadratic-pair
powering stages, normalizing inverse, exact N^2 division, and top-digit
extraction. The carry computation uses no inverse of N. Common N,R data
may be reused, but each point-dependent power or alternative evaluation
still costs work. With the imported quasi-linear arithmetic model,
C_scalar is soft O((R+1)b^2) on this legal-width branch.

The described complete valid trial makes **exactly s+1=2R scalar top-digit
acquisitions**, followed by one weighted combination and one final gcd.
It does not make 2R separate acquisitions for every lower digit. There
are 2R initial point-unit checks; these are already included in 2R times
(5.1), not a second required set of gcds. One may perform all initial checks
first and skip scalar evaluation on an invalid stencil. Early exits reduce
actual work; they stay in the probability denominator.

The remaining ledger is explicit:

- Construct (2R+1)! using O(R) integer multiplications and apply the 2R-bit
  shift for 4^R. D and sD have O(b) bits when the width guard passes. Check
  the guard and gcd(D,N)=1. This gcd certifies exactly the needed absence
  of prime divisors <=2R+1. A failed check is outside the theorem; gcd N
  is not a split, and localizing a small factor takes paid work, for
  example O(R) small-integer gcds. On the hypothesized branch it cannot
  yield a factor. Generate the 2R canonical points with O(R) b-bit steps.
- Generate the 2R binomial magnitudes by v_0=1 and
  v_(i+1)=v_i*(s-i)/(i+1), for 0<=i<s. The divisions are exact integer
  divisions. Every coefficient has at most s+1=2R bits; there are 2R-1
  recurrence steps and O(R^2) total coefficient bits if all are saved.
  Their construction is soft O((R+1)^2) with fast integer arithmetic.
- Combine the 2R signed summands modulo N using O(R) modular product/addition
  operations on O(b+R)-bit integers. Endpoint coefficients of magnitude
  one can use signed additions. Finish with one b-bit gcd and proper-factor
  validation. The absolute weight sum is exactly 2^s=2B, not B; B is
  each sign's total. No individual-digit gcds are part of this output rule.
- A itself is not needed to form the binomial sum. If the signal is computed
  for the optional screen, use A=P_R*(2R)!*D^(2R-2) modulo N. This needs
  O(R+log(R+1)) modular multiplications, plus paid reduction of the supplied
  u. A modular inverse, if requested, costs a further b-bit extended gcd.
  There is no need to materialize the much wider exact A or enumerate
  its possible residue roots at unknown primes.
- Exact uniform a0 can be drawn with ceil(log2 L0) random bits and rejection
  of strings outside [0,L0). For L0=1 take a0=0. Otherwise acceptance is
  greater than one half, giving O(b) expected random bits and sampling work.
  This bit-string rejection is distinct from discarding nonunit stencils.
  Capping after k draws retains sampling failures, costs O(kb), and leaves
  the conditional successful draw uniform; it cannot increase (3.4).
  Uncapped rejection has no finite worst-case draw bound.

Thus setup, selection, the 2R acquisitions, weights, checks, and final gcd
fit the conservative per-trial bound

    soft O((R+1)^2*b^2)                                  (5.2)

under the specified fast-arithmetic model, with expected sampling or a
separately priced finite cap. This is an upper bound for the specified
implementation, not a successful factoring-time bound. R=O(b/log b) from
the width guard ensures this per-trial work is polynomial in b. Resident
scalar registers have O((R+1)b) bits; weights and accumulated results can
be streamed. Fast-arithmetic workspace and any saved O(Rb) digit list or
O(R^2) coefficient list are additional storage.

The alternative exact floor evaluator inherits its paid growing-R coefficient
setup and wide Horner work from the scalar review; fixed-R shortcuts do not
supply a free growing-R implementation. All retries, rejected inputs, parameter
or label enumeration, batch construction, and localization retain their actual
costs. In particular an optional product over 2B-1 possible arguments A*u+c
is a different consumer with its own construction/localization cost. The
uncertainty-set notation is not a free interval product or a useful selector.

## 6. Globally small signals cannot produce a selective factor

Since N is odd, let r be the centered integer representative of A*u modulo
N in [-(N-1)/2,(N-1)/2]. Suppose a selected valid stencil has |r|<=T for
some T>=0. Equation (2.2) supplies an ordinary integer

    z=r+c,  Z=z (mod N),  |z|<T+B.

If leastprime(N)>T+B, then z=0 gives gcd N. For nonzero z, any prime
dividing gcd(z,N) would be at most |z|<T+B, a contradiction. The gcd is
therefore 1. The added consequence is valid for every such selected stencil,
including adaptively or nonuniformly selected ones satisfying this pointwise
hypothesis, and for nonsquarefree N. This pointwise obstruction does not
extend the separate uniform-sampling law to those selectors.

Moreover sD/2<=u<=N-1-sD/2, so 0<u<N. Since A is a unit, A*u=0 modulo
N would require u=0 modulo N, which is impossible for a canonical stencil.
Wrapping points generally changes their residues modulo D and breaks this
fixed-label polynomial argument. Even where some changed construction admits
an analogous bounded residual, setting its linear part to zero would leave
only that residual and would need its own proof.

This proves the requested sufficient threshold, without claiming that the
threshold is necessary or cheaply decidable. Globally small signal targeting
cannot split on this branch. A residue near an unknown nonzero multiple of
p can be large in centered absolute value modulo N; no obstruction to finding
such residues follows here. No procedure for selecting them has been supplied.

## 7. Scope repair, disposition, and the remaining obligation

No algebraic formula, numerical constant, denominator condition, root count,
or asymptotic exponent in the frozen target requires correction. Its final
paragraph does, however, say a next selector **must** exploit a proved
correlation between c and u. That necessity does not follow from a bound
for uniformly sampled starts. A different consumer, covering argument, or
changed representation can have different obligations.

Replace that sentence, at the parent's discretion, with the following scoped
research obligation (the target itself was not edited):

> One possible next route is an explicitly priced selector using a proved
> useful dependence between c and u. Any changed selector or consumer needs
> its own actual-input proper-split guarantee and full cost analysis; the
> uniform-start upper bound supplies neither that guarantee nor a theorem
> that such a correlation is the only possible route.

The saved work is explicit: order 2R-1 removes all lower even polynomial
terms and leaves one linear term plus an integer from a bounded set. Unlike
the high-order residual-only filter, that linear term permits nontrivial
gcds even when the factors exceed B. It does not enlarge the uniformly
sampled successful-start set beyond at most 2B-1 possible classes at each
prime, and canonical width makes this multiplicity N^o(1). That is the
precise failed amplification premise.

A conclusion-changing follow-up would supply a concrete N-only computation
with a proved proper-split yield or deterministic cover on its claimed input
family, including selection, all acquisition, failures, precision, and
consumer/localization costs. A changed representation or residue period would
also require rederiving its floor and width laws. The present proof does not
invent any such computation, declare novelty, or call for another copy of the
frozen assay. Accept the scoped negative result and the small-signal lemma;
close this stated uniform near-top sampler as an asymptotic improvement under
the guards. **Verified complete factoring improvement remains NONE.**

## Delivery integrity

[validation.json](W032-near-top-review-evidence/validation.json) records frozen
input and brief integrity, the limited prior-manifest check, live-source drift,
and the symbolic-only action scope. The
[delivery manifest](W032-near-top-review-evidence/delivery-manifest.json) lists
this report and every evidence payload with byte lengths and SHA-256 hashes.
The manifest and
[terminal-manifest.sha256](W032-near-top-review-evidence/terminal-manifest.sha256)
are its two explicit inventory exclusions, preventing circular hashing. These
two inventory files and the listed payloads are the complete delivery. The
exact finalized manifest hash is returned independently in the terminal
handoff. No report or payload is changed after sealing. Hashes establish byte
identity relative to the external anchor, not mathematical correctness.

Only this report and its assigned evidence directory were written. No recursive
delegation, installs, commits, shared code, Lean, STATE, task-registry edits,
project checks, or numerical runs were made.
