# W015 independent review: composite factorial routing

2026-10-08. Independent review of the complete W015 brief and frozen certificate.
Disposition: **accepted with implementation clarifications; the literal router
does not certify a power saving. Verified new end-to-end improvement: NONE.**
The parent remains principal researcher. This review changes no shared source,
hypothesis, checkpoint, certificate, or Lean file.

The mathematical identities and fragmentation argument survive review. The
claimed evaluator exists at the stated scale over an arbitrary odd composite;
the apparent extra `sqrt(R sqrt(H))` is absorbed, not omitted. The required
clarifications are exact dyadic block choices, an explicit stopped-product
nonunit branch, a finite routing cap, and bit-cost accounting. None supplies the
missing small-record routing guarantee.

**Accepted claims.**

- Equation (1), the multiplicity-preserving invariant (2), and pointwise gcd
  preservation hold for every odd modulus in their stated domains.
- Simultaneous unequal-length interval products cost
  `O~(number of records + sqrt(total length))`; overlap and repeated intervals
  cause no algebraic problem when occurrences are charged.
- Requested prefix factorials, including arbitrary repeated endpoints, cost
  `O~(sqrt(H)+R)`. Monic operations suffice for polynomial evaluation.
- With the nonunit handling below, the full evaluation/recovery envelope is
  `O~(C_route + 1 + R + sqrt(H) + sqrt(U))` bit operations, with the logarithmic
  qualifications below. Prime powers cause no recovery failure.
- For `n=isqrt(N)>=5`, `1<=H<=n/4`, and `s=ceil(log2 n)`, the specified ordinary
  interval router either stops before `s` with `U>=n/4`, or reaches a depth
  requiring at least `n/4` active records. For `H>n/4`, its prefix cost formula
  already has a `sqrt(n)` term.
- The proposed `N^(1/6)` substitution is a correct conditional calculation,
  without a construction achieving its premises.
- Tal's cited prime and supplied-arithmetic-data results do not give an
  unknown-factor composite factoring bound.

**Repaired/clarified claims.** Use power-of-two block widths dividing each
dyadic piece; do not leave an unpaid tail in every equal-length group. Explicitly
handle a nonunit stopped numerator/product as well as a nonunit denominator;
the single `gcd(H!,N)` precheck below simplifies every such branch. Charge
record traffic at intermediate depths, all endpoint arithmetic and multiplicity
handling, and exponent bit length. Specify a finite depth `t`: waiting for all
branches to enter the prefix need not terminate. These are completions of the
algorithmic description, not counterexamples to its cost scale.

**Rejected inferences.** Neither successful finite certificates, the prime
theorem, compressed AP syntax, nor a lower bound on the numerical value of an
upper-bound recipe establishes a new factoring improvement. This review rejects
an all-algorithm lower-bound reading of fragmentation. It also rejects treating
an uncut modular-AP product as a cheap new primitive: that product is an
explicit unit multiple of `n!`.

**Source and evidence scope.** The exact reviewed input is
[the frozen hypothesis](W015-routing-review-evidence/inputs/research/findings/W015-routing-certificate-evidence/hypothesis-frozen.md).
Its bytes equal the snapshotted live W015 file. The
[input manifest](W015-routing-review-evidence/input-manifest.json) freezes all
13 input files with SHA-256 and byte length. The frozen PDF is Yann Tal,
*Computing Modular Factorials Below the Square-Root Barrier*, September 2026,
ECCC TR26-211, from
<https://eccc.weizmann.ac.il/report/2026/211/download>. Its 1,309,585 bytes have
SHA-256 `c57d1e54cd67d2f7430d220f5454884c15800e04487081edd122eb3b0057621c`,
matching the supplied source manifest. No current web version was substituted.

The substantive PDF read covers the abstract; Theorems 1.1--1.3 and their setup
qualifications (pp. 5--7); the reconstruction overview and Theorem 1.5 (pp. 7--9);
section 1.4 (p. 18); Lemma 2.6 and its polynomial-product proof (pp. 26--27);
Proposition 4.3 and equation (20) (p. 35); and all Appendix H (pp. 66--69).
Printed page numbers equal PDF page numbers. The
[retained text extraction](W015-routing-review-evidence/tal-2026-factorials-layout.txt)
and [read-scope record](W015-routing-review-evidence/read-scope.json) distinguish
full-file preservation from passages actually reviewed. This is not a proof
audit of the whole paper, its references, or its algebraic reconstruction.

Theorem 1.1 supplies the prime `p` and `q|(p-1)`; Theorem 1.2 likewise supplies
`p` for modulus `p^2`. Theorem 1.3 fixes an odd prime-power cyclotomic index `r`
and supplies `p`, `q|Phi_r(p)`, a finite-field representation, and a compatible
order-`q` character. Its setup discussion permits Las Vegas construction with
the stated acquisition costs. Theorem 1.5 also specifies the character and
prime ideal needed for reconstruction and reduction. These are substantive
inputs, not objects obtained free from `N` alone. Section 1.4 describes CRT
evaluation for a **given** prime-power factorization of `N`.

Proposition 4.3 is a separate logarithmic refinement for a supplied prime `p`,
modulo `p` or `p^2`; Appendix H fixes `p` to be prime throughout. Its Lemma H.1
uses a selected-term theorem with invertibility conditions, a requested-index
limit `H^(3/8)`, and `2 sqrt(H)+1<p`. These conditions cannot simply be presumed
for an unknown-factor composite. The argument below avoids that theorem.
Lemma H.2's monic product/remainder-tree construction is the relevant algebraic
template; the necessary composite extension is proved directly below. This
review accepts no transferred logarithmic refinement or exponent saving.

**Exact routing and multiplicities.** Put `A=Z/NZ`, with odd `N>=25`, and
`n=isqrt(N)`. For `0<=a<=b<N`, even integers `j` in `(a,b]` map under `j/2`
bijectively onto `(floor(a/2),floor(b/2)]`. Odd integers map under `(j+N)/2`
bijectively onto `(floor((a+N)/2),floor((b+N)/2)]`. Multiplication of their
congruences `j=2T(j) (mod N)` proves (1), with exponent precisely `b-a`.
The two image ranges are separated by parity's lower/upper-half split. Empty
intervals have product one. The endpoints allow `a=0` and `a=b`; every
nonempty image consists of integers between 1 and `N-1`.

Because 2 is a unit, `T` is a permutation of all nonzero residue
representatives, including nonunits, and `gcd(T(j),N)=gcd(j,N)`. No field
argument is involved. Label each initial factor by its original `x in [1,n]`.
At every depth each label occurs exactly once, either in one stopped interval
at its stopping depth or in the current active set. Replacing an active
interval adds its length to `E` and preserves its product by (1); cutting at
`H` merely partitions it. Induction gives (2).

Active images at one depth are injective, hence disjoint. Stopped values from
different depths can coincide; their labelled occurrences must all remain.
In particular the sum of all final interval lengths **with multiplicity** is
`n`, so `R<=n` and `U<=n`. A repeated interval can be evaluated repeatedly or
cached, but its product must be used with its actual multiplicity. Caching is
optional, not a prerequisite for the bound. The identity `E<=nt` is valid;
its storage is `O(log(n+1)+log(t+1))` bits, with the zero case included.

For any sequence of injective current-index maps, at most `H` original labels
can newly stop at one depth. Therefore `(t+1)H>=n-U` is valid, including depth
zero. Also, if a label is divisible by a prime divisor `p>H` of `N`, its
images cannot enter `[1,H]`. This latter observation prevents an unconditional
"route until empty" termination rule; it does not itself give a large residual.

**Simultaneous interval evaluation over a composite ring.** Consider a list
of `k` nonempty intervals, total length `V`, allowing overlaps and repetitions.
Lengths count occurrences. Split each interval into consecutive pieces whose
lengths are powers of two, at most `1+floor(log2 N)` pieces per interval.
The pieces need not be aligned with a common integer grid. Group them by
length. There are `O(log N)` groups, `O(k log N)` piece records, and total
length still `V`.

For one group with `v` pieces of common length `ell=2^j`, choose a power of
two `w<=ell` as follows. If `v<=ell`, take the largest power of two at most
`sqrt(v ell)`. Then `sqrt(v ell)/2 < w <= sqrt(v ell)`. If `v>ell`, set
`w=ell`. In either case `w` divides `ell`, so **there are no short block
tails**. Build

    F_w(Z) = product_{j=1}^w (Z+j) in A[Z].

Evaluate it at each of the `Q=v ell/w` block starts, then multiply the values
belonging to each input piece. Fast product/remainder trees cost
`O~(w+Q+v)=O~(v+sqrt(v ell))`. In the capped case, `w=ell<v` and `Q=v`,
so the bound remains valid. All starts and block endpoints are explicitly
constructed and charged. They are `O(log N)`-bit integers.

Summing over the dyadic groups and applying Cauchy--Schwarz to their lengths
gives `O~(k+sqrt(V))`. This proves the unequal-length claim, including the
active evaluation `O~(R+sqrt(U))`. It does not charge the sum of the separate
square roots of each original interval.

No interpolation is used. At repeated starts the evaluation tree may contain
repeated linear factors; its remainder operations are still valid. Every
polynomial divisor is monic. Reversing a monic polynomial gives constant term
one, whose formal series inverse is constructed by ring operations (for
example Newton inversion), without inverting point differences or arbitrary
coefficients. Thus zero divisors in `A` cause no failure in these steps.
Scalar factorial quotients require a separate unit test; monicity does not
justify those quotients.

**Prefix factorials and the purported hidden term.** Let `b=ceil(sqrt(H))`.
Construct `F_b`, evaluate it at starts `0,b,2b,...` for the complete blocks
contained in `[1,H]`, and cumulatively multiply their values. This supplies
every block-boundary factorial in `O~(b+H/b)=O~(sqrt(H))` time. There is no
need to store every factorial up to `H`.

For each requested `m<=H`, write `m=qb+r`, `0<=r<b`. Multiply the computed
`(qb)!` by the interval product `(qb,m]`. With `K<=2R+1` endpoint requests
(the extra endpoint is `H` for the unit precheck), these residual intervals
have total occurrence length at most `Kb`. Apply the just-proved batched
interval routine to obtain them all in `O~(K+sqrt(Kb))`. Zero-length residuals
cost constant bookkeeping. Repeated endpoints need no special assumption.

The absorption is the elementary inequality

    2 sqrt(Kb) <= K+b.

Consequently the complete prefix cost is `O~(sqrt(H)+R+1)`. The term
`sqrt(R sqrt(H))` really occurs in this construction, but never exceeds the
claimed sum by more than a constant (and the admitted logarithms). This is
not a selected-term oracle and imposes no `H^(3/8)` endpoint restriction.

**Units, full gcds, and arbitrary prime powers.** A complete implementation
may follow the brief's denominator checks, but must also test a nonunit
stopped numerator/product after a unit denominator is established. A proper
gcd returns a factor; a full gcd requires localization. Omitting this case
would leave the sentence "if all stopped products are units" without a
specified alternative.

A simpler sufficient completion is to include `H!` among the prefix requests
and compute `g=gcd(H!,N)` before any quotient. If `1<g<N`, return `g`. If
`g=N`, localize in `[1,H]` as described next and return a proper factor. If
`g=1`, every integer in `[1,H]`, hence every endpoint factorial and stopped
product, is a unit. All required factorial quotients are then legal; extended
gcd obtains each inverse in polynomial bit cost. This precheck is covered by
the extra endpoint above and applies even with repeated stopped intervals.

For localization, suppose an interval product has gcd `N`. Bisect the
interval and compute the product of the left half by the proved single-
interval routine. A proper left gcd is already an answer. A left gcd `N`
directs recursion to the left half. A left gcd one directs recursion to the
right half: multiplication by the left unit cannot have created the parent's
full gcd. No nonunit division is used. The interval length halves at each
step, and the sum of its square-root evaluation costs is `O~(sqrt(m))` for
initial length `m`. A leaf is a positive integer `j<N`; `gcd(j,N)` can never
equal `N`, so the recursion must produce a proper factor. The same proof
works starting from any nonunit product, returning a proper gcd immediately
when available.

After the unit precheck, multiply the already computed active-interval
products and take their gcd with `N`. If `N` is composite, its smallest prime
factor is at most `n`, so `n!` is nonunit. Equation (2) and the unit stopped
products imply that this active product is nonunit. A proper gcd finishes.
For gcd `N`, scan the at most `R` already available interval values for a
nonunit one (or descend an aggregate product tree), then localize that
interval. The additional work is `O~(R+sqrt(U))`. Only one localization is
needed, since its success terminates the splitter.

This reasoning uses neither squarefreeness nor distinct prime factors.
For instance, symbolically `N=p^4`, odd prime `p`, has `n=p^2` and
`v_p(n!)=p+1>=4`: a full factorial gcd can indeed equal `N`. Nevertheless
each nonunit leaf remains below `N` and supplies a proper gcd. This is a
proof illustration, not an additional executed certificate or tuned case.
Prime inputs may return no factor. Even inputs and the finitely many odd
composites below 25 can be handled by constant-size preprocessing if one
wants the full splitter domain; the audited routing statement starts at 25.

**Complete bit-operation scope.** Let `L=ceil(log2 N)` and let `C_route,bit`
be the actual bit work producing and retaining the interval records, including
every discarded/intermediate record, endpoint arithmetic, comparisons,
sorting if used, multiplicities, loop control, and updating `E`. Let

    D = 1+R+sqrt(H)+sqrt(U).

All endpoint, residue, gcd, and inverse operands have `O(L)` bits. Polynomial
coefficients are reduced modulo `N` after operations. For degree `d`,
Kronecker packing uses digits of `O(L+log(d+1))` bits, sufficient to prevent
carries between convolution coefficients; it does not construct the exact
integer factorial. Standard deterministic quasi-linear integer multiplication
and division then give polynomial multiplication in `O~(d L)` bits. All
polynomial degrees and list counts here are polynomially bounded in `N`, so
their index logarithms are `O(L)`. Product/remainder-tree levels, the dyadic
groups, sorting, endpoint gcds and unit inverses add only polynomial factors
in `L`. Building the block polynomials and evaluation trees is included.

For an explicit deliberately loose bound, these constructions fit within

    O(C_route,bit + D (L+1)^6
      + (L+log(t+1)+1)(L+1)^2).

The last term pays for binary modular exponentiation of `2^E`, using even
schoolbook modular multiplication; the zero exponent is immediate. It also
comfortably includes ordinary integer-square-root and input/output overhead.
If `t<=N^O(1)`, the last term is absorbed in `D (L+1)^6`. For arbitrary
finite `t`, retain the shown `log(t+1)` term and the actual routing cost.
Thus the original soft bound is sound with polynomial logarithms interpreted
honestly. If `C_route` instead counts record/word operations, its conversion
to bit work must also multiply by the corresponding polynomial logarithms.
A splitter interested only in the gcd may omit the unit `2^E`, but the bound
above pays for the advertised full product.

The exponent 6 is a conservative accounting envelope, not a claimed sharp
logarithmic refinement. It follows, for example, from `O((w+Q+1)L^3)` bit
cost per product/remainder-tree batch under fast integer multiplication,
`O(L)` dyadic groups, and the piece counts proved above; the remaining gcd,
sorting, recovery and bookkeeping costs fit within the extra slack. No
factorization, character acquisition, generic field division, or uncharged
preprocessing is hidden in this envelope. It is an existence/cost argument
for standard polynomial arithmetic, not a running-time claim about the
parent's point-enumerating certificate program. The corresponding evaluator
needs only polynomial-logarithmic overhead beyond its working polynomial
and interval lists in space; the router's retained representation is charged
separately. No machine-refinement or Lean cost theorem is claimed.

Substituting `H,U=O~(n^(2/3))` and `R,C_route=O~(n^(1/3))` gives
`O~(n^(1/3))=O~(N^(1/6))`, provided the stated routing work includes bit-cost
conversion. W015 does not construct these quantities for its literal router.

**Fragmentation, constants, and scope of the obstruction.** Assume
`n>=5`, integer `1<=H<=n/4`, and `s=ceil(log2 n)`. For any original odd
`x in (H,n]` and `1<=r<=s`, there is a unique `k` in `[0,2^r-1]` such that

    T^r(x) = (x+kN)/2^r.

Indeed choose `kN=-x (mod 2^r)`; odd `N` is invertible modulo `2^r`, and
this expression is in `[1,N-1]`. Since `x` and `N` are odd, `k` is odd,
hence `k>=1`. Therefore

    T^r(x) > N/2^r >= N/2^s > N/(2n) >= n/2 > H.

Every such original label survives all rounds through `s`; this argument
also shows why retaining only a final-time inequality would have been
insufficient without checking the earlier depths. The exact number of odd
labels is `ceil(n/2)-ceil(H/2)`, at least

    floor((n-H)/2) >= (n-H-1)/2 >= 3n/8-1/2 >= n/4.

The last inequality already holds for `n>=4`. In particular the smallest
allowed value `n=5` has `H=1` and two guaranteed odd survivors. If a finite
run stops at `0<=t<s`, it therefore has `U>=n/4`, so the displayed
`sqrt(U)` term is at least `sqrt(n)/2`.

Put `d=2^s`, so `n<=d<2n`. If two distinct full images
`T^s(x),T^s(y)`, `x,y in [1,n]`, were adjacent as ordinary integers, then
`x-y` would be congruent to `d` or `-d` modulo `N`. But `|x-y|<=n-1`, while

    d>=n,
    N-d > n^2-2n > n-1  (n>=5).

No representative of either congruence lies in `[-(n-1),n-1]`. Thus the
entire full image has no adjacent elements, including when `n` is a power
of two (`d=n`). The active set is a subset of this full image. Every
nonempty ordinary consecutive interval in an exact positive interval-list
representation of it must be a singleton. A run actually reaching `s`
therefore materializes at least `n/4` active records. This cost belongs to
`C_route` even if later intervals merge or the final `R` is smaller.

For `H>n/4`, the displayed prefix term exceeds `sqrt(n)/2`. These cases
exhaust integer `1<=H<n` and finite stopping depths. They show that the
**numerical cost recipe cannot certify a smaller power of `n`** with this
explicit router. The early-stop case is a lower bound on a term in an upper
bound, not a lower bound on actual multiplication cost. The record-writing
claim applies only when those records are actually materialized. Early
factor discovery can terminate before that depth. An implicit representation,
a different evaluator, or a different computation is outside this obstruction.
Nothing here proves a general factoring lower bound or rules out logarithmic
improvements.

**A constructive escape with an actual computation.** Let
`b=ceil(sqrt(n))`. Skip halving entirely. Build `F_b(Z)=product_{j=1}^b(Z+j)`
and evaluate it at `0,b,...,(q-1)b`, `q=floor(n/b)`, by monic trees over
`Z/NZ`. Multiply these complete-block values and the final tail of fewer
than `b` integers. This computes `n! mod N` in `O~(sqrt(n))` bit operations.
The tail may be multiplied directly; its cost is already at most `b`.
Apply the same gcd localization to the block values, and then within one
block. All leaves lie in `[1,n]`, so recovery is valid for arbitrary odd
composites. No known prime, supplied character, or cheap-product oracle is
required. This changes actual work: no fragmented images, stopped endpoints,
or depth-`s` singleton list is constructed. It returns to the established
deterministic `O~(N^(1/4))` product method, which is a concrete escape from
the representation cost, **not a new improvement** or a claim to match the
best general factoring bounds.

For contrast, if `a=2^(-s) mod N`, the uncut compressed progression has

    product_{x=1}^n [a x]_N = a^n n! (mod N).

Since `a^n` is a known unit, this is the same computational target up to
cheap unit multiplication. Naming that progression does not evaluate its
product. Cut progression products additionally require computing the
exclusion set, multiplicities, and nonunit localization. No fast cut-product
recurrence is supplied or assumed in this review. A future improvement must
give an explicit paid computation for that operation or otherwise replace
the long product; merely rewriting the set will not change this disposition.

**Finite evidence and final disposition.** The retained parent output has
exactly the preregistered six cases `{25,35,77,101,143,21311}`, 1,236
assertions, 5,140 recorded point visits against the 20,000 limit, and zero
recorded failures. The complete rounds, code, and output are preserved in
the review input snapshots. The source-manifest PDF hash and both frozen
code/hypothesis hashes verify; live/frozen hypothesis snapshots are identical.
[verification.json](W015-routing-review-evidence/verification.json) records
these byte checks. The brief reports exit 0; no separate persisted process
exit artifact was supplied, so I do not claim to have independently observed
that process exit.

The certificate checks finite interval identities, active-image agreement,
gcd preservation, odd survival, nonadjacency, and singleton counts. Its prime
101 case is an algebra control. It does not implement or test the fast
prefix evaluator, polynomial batching, inverse safety, full-gcd recovery,
universal fragmentation proof, or asymptotic complexity. Zero failures have
only that finite scope. No parent code/output was rerun or overwritten; no
additional algebra certificate, parameter search, performance experiment,
install, recursive delegation, shared-file change, or commit was made.
The parent's reported `scripts/check.sh` success (12 Python tests and
Lean/audit) is acknowledged and was not rerun for this proof-only review.

Accept the scoped identities, completed evaluator/recovery analysis, and
fragmentation proof. Close the literal-router `N^(1/6)` recipe as unsupported
by this mechanism. The next result that could change the conclusion is a
noncircular cut-product algorithm with paid construction/evaluation/recovery,
or another computation bypassing this router. The concrete block method
above is available now but establishes no new end-to-end improvement.

All read inputs and delivery artifacts are covered by
[input-manifest.json](W015-routing-review-evidence/input-manifest.json) and
[delivery-manifest.json](W015-routing-review-evidence/delivery-manifest.json).
The delivery manifest excludes itself to avoid self-reference; its own
SHA-256 is returned with the delivery. Snapshotting and manifest verification
are evidence bookkeeping, not new mathematical experiments.
