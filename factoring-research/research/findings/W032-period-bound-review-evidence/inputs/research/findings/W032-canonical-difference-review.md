# W032 canonical-difference filter: independent symbolic review

**Disposition: ACCEPT the stated filter identity, strict residual bound,
conditional failure to split, and uniform canonical-width consequence. No
mathematical correction is required. Reject this particular filter as a
large-factor amplifier in the stated regime. Verified complete factoring
improvement: NONE.**

The acquisition bound is for one supplied or publicly selected stencil, with
all attempted stencils and any residue-class enumeration charged separately.
The proof concerns the final filtered gcd. It does not dispose of initial
nonunit exits, individual digit gcds, or other computations using those digits.

## 1. Scope, imports, and full reads

The reviewed construction is the exact frozen 109-line
[canonical-difference proposal](W032-canonical-difference-review-evidence/inputs/research/findings/W032-canonical-difference-filter.md),
SHA-256 `9448c1be825257cd7385d41e9ca273684170c5077721d5d64e805b6b9ea4c552`.
The full assignment is preserved in
[brief.txt](W032-canonical-difference-review-evidence/brief.txt).
Ten complete inputs, including all five governing documents and the
coordination-only STATE snapshot, are preserved with byte lengths and hashes in
[input-manifest.json](W032-canonical-difference-review-evidence/input-manifest.json).
All ten were read in full; exact line coverage and use are recorded in
[read-scope.json](W032-canonical-difference-review-evidence/read-scope.json).

The accepted interface is sections 5 and 7 of the complete 555-line
[scalar/carry review](W032-canonical-difference-review-evidence/inputs/research/findings/W032-scalar-carry-review.md),
as accepted by the complete 69-line
[parent disposition](W032-canonical-difference-review-evidence/inputs/research/findings/W032-symbolic-parent-disposition.md).
The complete 153-line
[W032 hypothesis](W032-canonical-difference-review-evidence/inputs/research/hypotheses/W032.md)
and section 8 of that review supply the scalar acquisition/cost contract.
This review checks the new finite-difference consumer, rather than repeating
the accepted scalar derivation or auditing the earlier evidence package.

No candidate evaluation, numerical experiment, parameter sweep, assay replay,
or new formal-polynomial computation was performed. The arguments below are
symbolic prose proofs, not Lean proofs. Computation was limited to file
inspection, evidence preservation, and integrity checking. No external
technical source is needed: the imported interfaces and elementary proofs
below suffice, and no novelty or current-baseline claim is made.

The separate joint-lift review and W033 separating-cover branch were not
reviewed or duplicated. Their source/evidence packages and the frozen scalar
assay were not opened. Existing summaries and assay specifications occur in
the required inputs; reading those is not an assay rerun. No delegation,
install, commit, shared code/Lean/STATE/task-registry edit, or project test run
occurred. Only this report and its assigned evidence directory were written.

## 2. Denominators, fixed labels, and exact floors

Take an integer R>=1 and an integer N>1 with leastprime(N)>2R+1. In the
factoring application N is composite; the algebra does not require
squarefreeness. Define

    m = 2R+1,                 D = 4^R (2R+1)!,
    M = N^(2R+1),             C_k(x) = D G_k(x),
    F(N,a) = sum_(k=0..R) N^(2k) C_k(a^2).

Choose an integer a0 such that a_i=a0+iD is in [0,N) and gcd(a_i,N)=1
for every integer i from 0 through m. All subsequent filter conclusions
refer to this entire unit stencil.

Every denominator D_j=4^j(2j+1)! for j<=R divides D. Thus C_k belongs to
Z[x], deg C_k<=k, and F(N,a) belongs to Z[a]. All prime divisors of D
are at most 2R+1, so gcd(D,N)=gcd(D,M)=1. In particular both D inverse
modulo M and M inverse modulo D exist. There is **no missing denominator
unit** and no inverse of N modulo N. The scalar normalization also uses
the separately stipulated unit a; the least-prime hypothesis ensures 4
is a unit.

For any permitted a define canonical residues

    e(a) = [C_R(a^2)]_D,
    h(a) = [-F(N,a) M^(-1)]_D,          0<=e(a),h(a)<D.

The inverse in h is modulo D. For a_i=a0+iD, integer-polynomial
congruence gives C_k(a_i^2)=C_k(a0^2) modulo D for every k. Consequently
F(N,a_i)=F(N,a0) modulo D, and both e and h are fixed across the entire
stencil. This conclusion needs no smallness estimate for any coefficient.

The accepted scalar interface says V_R(a)=[F(N,a)D^(-1)]_M. To check all
representative and sign issues directly, put

    T = (F(N,a)+hM)/D,        T in Z,
    t = floor(T/M),           V_R(a) = T-tM in [0,M).

For positive N^(2R), translation of a floor by the integer tN gives

    floor(V_R(a)/N^(2R)) = floor(T/N^(2R))-tN.

This holds for every integer t, including when T is negative. Reduction
modulo N therefore gives

    d_R(a) = floor(F(N,a)/(D N^(2R)) + hN/D)  (mod N).

On the chosen class set

    J(i) = (C_R((a0+iD)^2)-e)/D,
    Q(i) = e/D + hN/D
           + sum_(k=0..R-1) N^(2k-2R) G_k((a0+iD)^2).

J is a rational polynomial of degree at most 2R, with integer values
at every integer i. Integer coefficients of J are not required. Q is
a rational polynomial of degree at most 2R-2, with Q constant when R=1.
The negative exponents of N in Q are ordinary rational denominators
inside an exact real floor; they are never treated as modular inverses.
Using floor(J(i)+Q(i))=J(i)+floor(Q(i)) now proves

    d_R(a_i) = J(i)+floor(Q(i))  (mod N).                 (2.1)

An implementation must use exact rational arithmetic or a common integer
numerator with mathematical floor division. Truncation toward zero for
negative inputs or floating-point approximation would not implement (2.1).

## 3. An integer residual with the strict bound

For an arbitrary sequence f, define the forward difference by

    Delta f(i)=f(i+1)-f(i),
    Delta^m f(0)=sum_(i=0..m) (-1)^(m-i) binom(m,i) f(i).

The displayed formula follows by expanding (E-1)^m, where E shifts i
to i+1. For a rational monomial of positive degree d, (i+1)^d-i^d has
degree d-1; a constant has zero difference. Hence Delta^m annihilates
every rational polynomial of degree less than m. In particular
Delta^m J=Delta^m Q=0. This is an identity over Q, requiring neither
division by m! modulo N nor a finite-field degree argument.

Applying the stencil to (2.1) gives exactly

    Z = c  (mod N),
    c = Delta^m floor(Q)(0) in Z
      = -Delta^m {Q}(0),          {x}=x-floor(x) in [0,1). (3.1)

The fractional-part range also holds for negative x. Set
w_i=(-1)^(m-i)binom(m,i). The sum of all absolute weights is 2^m and
the signed sum is zero, by the binomial identities at 1+1 and 1-1.
Therefore the positive and negative weights each have total magnitude

    S = 2^(m-1) = 4^R.

Both sign sets are nonempty. With f_i={Q(i)}, put

    P = sum_(w_i>0) w_i f_i,
    H = sum_(w_i<0) (-w_i) f_i.

Since every f_i<1 and every magnitude is positive, 0<=P<S and
0<=H<S, strictly at the upper endpoints. Thus c=H-P satisfies

    -4^R < c < 4^R,
    equivalently |c| <= 4^R-1 because c is integral.      (3.2)

This proves the exact strict bound, not merely |c|<=4^R or the looser
sum-of-absolute-weights bound 2^m. It uses no independence, randomness,
equidistribution, or assertion that the bound is attained.

If canonical digits are used in the actual sum, each differs from the
integer lift in (2.1) by an integer multiple of N. Their integer weighted
sum differs from c by another multiple of N. Consequently

    gcd(Z,N) = gcd(c,N),                                (3.3)

even if c is negative or Z is reduced to its canonical residue.

## 4. Exact gcd consequence and the R=1 boundary

If c=0, (3.3) returns N. If c is nonzero, any prime dividing gcd(c,N)
divides |c|<4^R. Hence leastprime(N)>4^R implies gcd(c,N)=1. The filter
has no proper output on that branch, for arbitrary prime powers and
arbitrary multiplicities as well as squarefree semiprimes.

There is a slightly stronger description on all admitted canonical
stencils: since 4^R<N by the width condition below, every nonzero-c gcd
is at most |c|<4^R and is strictly smaller than N. Thus any proper
filtered output is itself below 4^R, not merely composed of primes below
4^R. The c=0 case is always the full gcd and must not be called a small
factor exposure. The proposal's sufficient strict least-prime condition
is correct; no threshold repair is needed.

For R=1, D=24 and m=3. Here G_0=1 and

    Q(i)=e/24+hN/24+N^(-2)

is constant, while J has degree at most two. Therefore c=0 exactly
and the four-point filtered gcd is N. This uses only leastprime(N)>3,
not the stronger unnecessary 5-unit condition from the two-digit
discussion. It agrees with the imported formula d_1(a)=a^2/24 modulo N,
whose individual gcd is 1 on units. The boundary is valid and stronger
than the general |c|<4 estimate.

An initial proper gcd(a_i,N) is a distinct success, before scalar
normalization. A full initial gcd at the canonical value a_i=0 is not a
factor and invalidates that unit stencil. Individual gcd(d_R(a_i),N),
other digits, and other combinations of the acquired data are likewise
outside the negative conclusion about (3.3).

## 5. Canonical width and a uniform asymptotic proof

Canonical inputs satisfy 0<=a0 and a0+mD<=N-1. Thus mD<N is necessary.
On the unit branch actually a0>=1, so the allowed starting range is

    1 <= a0 <= N-1-mD.                                  (5.1)

Even a nonempty range in (5.1) does not ensure every point is a unit.
The proposal only claims necessity of mD<N, not existence or cheap
acquisition of a unit stencil, so its wording is valid.

Use natural logarithms and put L=log N. The last R+1 factors in
(2R+1)! are all at least R+1; bounding every factor above by 2R+1 gives

    (R+1) log(R+1) <= log D
       <= R log 4+(2R+1) log(2R+1).

For R>=1 this proves log D=Theta(R log(R+1)) with absolute constants.
Admissibility implies log D<L, so R log(R+1)<L. This yields a uniform
bound rather than one that silently fixes R. For L>1, split into:

- R<=sqrt(L): then R<=2L/log L, since log L<=2sqrt(L).
- R>sqrt(L): then log(R+1)>(log L)/2, so R<2L/log L.

The auxiliary inequality follows, for example, from log x<=x for x>0
applied to x=sqrt(L). Therefore for every sufficiently large N and
every admissible R simultaneously,

    R <= 2 log N/log log N,
    (log(4^R))/(log N) <= 2 log 4/log log N -> 0.         (5.2)

This proves 4^R=N^o(1) uniformly over the admissible choices, including
bounded, unbounded, or oscillating R and any choice of a0. For each
fixed epsilon>0 choose N_epsilon so large that
2 log 4/log log N<epsilon whenever N>=N_epsilon. Then every such
stencil has 4^R<N^epsilon. If leastprime(N)>=N^epsilon, it follows that
leastprime(N)>4^R and section 4 applies. The threshold depends on epsilon,
not on R, a0, or the prime factorization. No statement for a vanishing
epsilon(N) is obtained by this argument without an additional comparison.

Wrapping the input progression modulo N changes its mathematical form:
write a_i'=a0+iD-k_iN with a_i' canonical. Modulo D this is
a0-k_iN. Since N is invertible modulo D, these residues stay in the
same D-class only if the k_i stay congruent modulo D. Wrapping does not
guarantee that; even accidental constant labels would not by themselves
justify the original polynomial-in-i representation. Thus substituting wrapped
inputs is not a valid way to bypass (5.1). This is a failure of the
proposed argument for that changed computation, not a theorem that all
wrapped filters fail. Full higher-lift distributions remain with their
separate reviewer.

## 6. Complete cost of the specified filter

Let b=bitlen(N) and B=Theta((R+1)b). The accepted scalar contract gives
one supplied-point cost

    C_scalar = O((b+log(R+1))*(M_int(B)+Div(B))
                 + Gcd(B)+Gcd(b)).

M_int, Div, and Gcd name the paid bit costs of integer multiplication,
division, and extended gcd at the indicated width. Under the imported
quasi-linear arithmetic model this is soft O((R+1)b^2). There are
m+1=2R+2 points, so the scalar part costs soft O((R+1)^2 b^2).
Here a single top digit is extracted at each point; no repeated extraction
of all lower digits is required by this filter.

The remaining concrete work fits this envelope on the legal-width branch:

- D has O(R log(R+1))=O(b) bits. Sequential factorial multiplication
  constructs it with O(R) multiplications of at most O(b)-bit integers,
  followed by the 2R-bit shift for 4^R. The width guard is checked before
  selecting a valid a0 and generating the O(R) canonical points.
- gcd(D,N)=1 certifies precisely the denominator-unit branch, since D
  contains every prime at most 2R+1. A nonunit exit needs ordinary factor
  handling: gcd(D,N)=N alone is not a split. Localization among integers
  2,...,2R+1 uses O(R) paid gcds if required; these integers are less than
  N on the width-legal branch. The O(R) initial input gcds are also paid.
- Generate binomial coefficients by b_0=1 and
  b_(i+1)=b_i*(m-i)/(i+1), using exact integer division. Each coefficient
  has at most m+1=O(R) bits because binom(m,i)<=2^m. There are O(R)
  coefficients and O(R^2) total bits if all are retained. No modular
  inverse for the recurrence's division is needed. Under fast arithmetic
  their construction costs soft O((R+1)^2).
- Stream signed products modulo N, with O(R) multiplications on
  O(b+R)-bit operands, followed by the final b-bit gcd and any witness
  validation. Since R=O(b) on this branch, this is within the stated
  scalar envelope. Weights and scalar outputs need not all be stored;
  arithmetic workspace is additional to the resident residues.

Thus the proposal's conservative soft O((R+1)^2 poly(log N)) per-stencil
cost is valid; the accepted arithmetic model supports the more specific
soft O((R+1)^2 b^2). This is an upper bound for the described evaluation,
not a lower bound for all ways to form Z and not a successful factoring
time bound. No fast-arithmetic implementation was benchmarked here.

The exact-floor evaluator is also legitimate, but its growing-R coefficient
setup and wide Horner operations must be paid as in the scalar review.
For fixed R they are bounded-degree operations. One must not transfer the
scalar bound to an unspecified growing-R coefficient implementation for free.

D residue classes are not O(log D) objects. The displayed one-stencil
algorithm does not enumerate them. Any selector that does enumerate all
classes pays that enumeration, and every rejected or attempted starting
point/stencil is included in its total work. No bound on finding a unit
stencil or a useful starting class is asserted. Similarly,
leastprime(N)>4^R is a condition of the negative theorem, not a free
algorithmic test supplied by gcd(D,N)=1.

## 7. Disposition and what could change it

All requested checks pass: denominator units, fixed h/e, integer-valued J,
both degree bounds, exact negative-floor handling, canonical output
representatives, the strict 4^R bound, R=1, prime-power scope, uniformity
in R, and paid per-stencil work. The width/existence, enumeration, and
nonzero-output qualifications above make the original scope explicit;
they do not repair an incorrect identity or asymptotic conclusion.

The intended saved work was cancellation of the complicated polynomial
part of the carry signal. The cancellation succeeds, but the final gcd
then sees only an integer of absolute value below 4^R. The canonical
stencil's width makes that bound smaller than every fixed positive power
of N, uniformly. This is the exact failed assumption behind large-factor
amplification by this computation; it is not a probabilistic rarity claim.

A lower-order difference, or a genuinely smaller proved label period and
a changed admissible parameter range, would be a different computation.
Before any such route is accepted, its actual surviving polynomial/floor
expression, input acquisition, cost, and proper-factor yield need a new
proof. Merely asserting a smaller period or a useful selector supplies
none of those obligations. Those alternatives were not developed here,
and no additional numerical assay is recommended for the proved claim.

Accept the negative result only for the displayed filter under its stated
hypotheses. There is no all-algorithm lower bound, conclusion against
individual digits or arbitrary consumers, novelty claim, or new complete
factoring gain. **Verified complete factoring improvement remains NONE.**

## Delivery integrity

[validation.json](W032-canonical-difference-review-evidence/validation.json)
records input integrity, live-source drift, source-read coverage, and the
symbolic-only action scope. The
[complete delivery manifest](W032-canonical-difference-review-evidence/delivery-manifest.json)
lists every payload, including this report, with its path, byte length,
and SHA-256. The manifest and
[terminal-manifest.sha256](W032-canonical-difference-review-evidence/terminal-manifest.sha256)
are explicitly excluded from their own payload list to avoid circular
hashing; together with the listed payloads they are the full delivery.
The terminal anchor hashes the exact finalized manifest bytes and is also
returned outside the files in the terminal handoff. Nothing is appended
to the report after sealing. Hashes attest byte identity, not correctness
of the mathematics.
