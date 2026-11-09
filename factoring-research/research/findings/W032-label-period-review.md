# W032 exact carry-label period: independent symbolic review

**Disposition: ACCEPT the exact common function-period algorithm, its
minimality, its polynomial-in-(R, bitlen(N)) construction cost, and the
replacement of the canonical width guard by (2R+1)S_min<N. No mathematical
repair to the proposed algorithm is required. The exponential-period escape
remains INCONCLUSIVE: an exact 2-adic component is proved below, but neither
an exp(O(R)) upper bound nor factorial-scale growth of the full period is
proved. Verified complete factoring improvement: NONE.**

In particular, for every R>=1 and every permitted N, this review proves

    v_2(S_min) = v_2(D)-1-v_2(R)
               = 4R-s_2(2R+1)-v_2(R),                   (A)

where s_2 is the number of ones in the binary expansion. This is uniform
in N and gives S_min >= 2^(4R-O(log(R+1))). If ell=2R+1 is prime, it also
proves v_ell(S_min)=1. Neither assertion controls the aggregate contribution
of the other odd primes. These are symbolic prose theorems, not Lean results
or numerical observations.

## Scope and evidence

The complete 95-line target is frozen at
[W032-exact-label-period.md](W032-label-period-review-evidence/inputs/research/findings/W032-exact-label-period.md),
SHA-256 `64f3fb1c5257c74c7bdd9ef6e879ae70286b58977365fb9ee40a720774a3c177`.
The [full brief](W032-label-period-review-evidence/brief.txt) and
[input manifest](W032-label-period-review-evidence/input-manifest.json)
preserve the assignment and fifteen complete input files. Snapshots were
made after initial inspection and before report drafting. The five governing
documents, W032 hypothesis, scalar/carry review, canonical-difference proposal
and review, parent dispositions, parent intake and preceding delivery manifest
were read completely. Only the current coordination portion of STATE was
read; its entire file was preserved. Exact coverage and exclusions are in
[read-scope.json](W032-label-period-review-evidence/read-scope.json).

The scalar diagonal and canonical floor identity are accepted imports. The
preceding canonical-difference delivery was independently checked for byte
integrity against the brief's external manifest anchor
`34e2cd3a26f5fc96558e2ab99d536a93923becd97030668b2529eb349025dacd`;
all fifteen payloads match. This checks delivery, not the prior mathematics.
The full-lift joint law is imported only as scoped by the parent disposition;
it supplies no distributional claim for a<N. The live near-top audit, its
target, and its evidence were not read or duplicated.

No candidate was implemented or executed. There was no parameter sweep,
numerical experiment, formal-polynomial computation, assay rerun, external
source lookup, recursive delegation, installation, commit, shared-code or
Lean edit, STATE/task edit, or project-check run. Terminal computation was
limited to reading, copying, writing and hashing evidence. No novelty or
current-baseline claim is made; the proofs use the supplied formulas directly.

## 1. Exact coefficient setup and the relevant functions

Fix R>=1 and N>1 with leastprime(N)>2R+1. Set

    D_j = 4^j(2j+1)!,        D = D_R,
    U_j(Y) = product_(i=1..j)((2i-1)^2-Y)
           = sum_(h=0..j) u_(j,h) Y^h,
    q_j = D/D_j in Z,
    C_k(X) = sum_(j=ceil(k/2)..k) q_j u_(j,k-j) X^j.

Here U_0=1, D_0=1 and C_0=D. The imported diagonal C_k=D G_k follows
exactly, and all C_k belong to Z[X]. Define the integer polynomials

    E(A) = C_R(A^2),
    H(A) = sum_(k=0..R) N^(2k) C_k(A^2),
    M = N^(2R+1).

Both degrees are at most 2R (indeed exactly 2R before reduction).
Since gcd(N,D)=1, M is invertible modulo D. Thus the two canonical labels

    e(a) = [E(a)]_D,          h(a) = [-H(a) M^(-1)]_D

are simultaneously preserved exactly when the functions E,H modulo D are
preserved. Multiplication of H by this fixed unit does not change its period
group. No modulus-N inverse of N is used. The period algorithm itself works
for arbitrary integer N; the least-prime hypothesis is needed for these
labels and the imported factoring interpretation.

A streaming construction realizes the target's memory claim. Put
nu_k=[N^(2k)]_D for 0<=k<=R. Retain one row U_j, the nu array, and arrays
for the even coefficients of E,H. For a given j, their coefficients are

    [A^(2j)]E = q_j u_(j,R-j), if 0<=R-j<=j, else 0,
    [A^(2j)]H = q_j sum_(h=0..min(j,R-j)) u_(j,h) nu_(j+h)  (mod D). (1)

The recurrence U_j=((2j-1)^2-Y)U_(j-1) costs O(j) coefficient operations.
Construct q_j as exact integers; for example q_0=D and

    q_j = q_(j-1) / (4(2j)(2j+1))

is exact for 1<=j<=R. Only afterward reduce the product with u_(j,h)
modulo D. Reducing q_0 to zero first and then attempting division modulo D
would be wrong. The submitted requirement for exact multipliers avoids this.
Rows U_j themselves may be maintained modulo D. Formula (1) costs O(R^2)
operations in total without storing the O(R^2) coefficients of every C_k.

Even unreduced coefficients have polynomial width: the sum of their absolute
values in U_j is product_i(1+(2i-1)^2) <= (1+4j^2)^j, and q_j<=D.
Their bit lengths are O(R log(R+1)); no hidden factorial-sized *bit count*
or N-dependent large power is required.

## 2. The finite-difference test is exact for functions

For any fixed integer t and either integer polynomial P above, put

    T(A)=P(A+t)-P(A),          d=2R-1.

For a monomial A^m with m>=1 the highest powers cancel, leaving degree
at most m-1. Constant terms cancel completely. Consequently deg T<=d
over Z, including when some coefficients vanish modulo D. Zero divisors
modulo D do not invalidate this upper bound. Reducing P's coefficients
before modular evaluation produces exactly the same values of T modulo D.

For any polynomial T in Q[A] of degree at most d, the rational-polynomial
Newton identity is

    T(A) = sum_(j=0..d) (Delta^j T)(0) binom(A,j).         (2)

One proof uses Delta binom(A,j)=binom(A,j-1) and the triangular evaluations
at A=0,...,d to identify the coefficients. The remainder has d+1 rational
roots and degree at most d, so is identically zero. This interpolation is
over Q, never over Z/DZ. If T has integer values, its differences are
integers. For every integer A, binom(A,j) is integral; for negative A=-u,
u>=1, it is (-1)^j binom(u+j-1,j). Therefore (2) implies

    T(A)=0 mod D for all A in Z
      iff Delta^j T(0)=0 mod D for 0<=j<=d.              (3)

The converse uses the integer linear combination of T(0),...,T(j) defining
each difference. Thus 2R values, at 0 through 2R-1, suffice for each P.
The differences may be computed modulo D throughout. No inverse of j!,
no modular Vandermonde inversion, and no enumeration of D residues occurs.

Indeed requiring all these leading differences to be zero is equivalent
to requiring all the 2R sampled values to be zero, by the same triangular
integer transformation. The explicit difference table is a correct
certificate format even though it is redundant for this zero-only decision.
Coefficientwise zero of T in (Z/DZ)[A] would be a stronger condition and
is neither tested nor assumed. The rational identity (2), with integral
values of binom(A,j), is exactly what bridges this distinction.

## 3. Greedy stripping returns the true minimum

Let K be the set of all integer translations preserving both functions on
all of Z. It contains zero, sums of its elements, and negatives: if t is
a period, evaluate P(A+t)=P(A) at A-t. Every integer-coefficient polynomial
has period D modulo D, so D Z is contained in K. Consequently

    K = S_min Z,             1<=S_min<=D, S_min divides D.

The exact test in (3) accepts t iff S_min divides t. Start with S=D and
maintain S_min|S. For a prime ell dividing S, write a=v_ell(S) and
b=v_ell(S_min). All other valuations already dominate those of S_min.
The trial S/ell passes iff a>b. If it fails then a=b, and subsequent
stripping of other primes cannot change this equality. If it passes,
decreasing a by one preserves the invariant. Processing every prime of
D therefore ends with equality of all valuations, so S=S_min.

There is at most one failed trial per prime, no need to revisit a failed
prime, and no dependence on prime order. The minimum is among **all positive
integer periods**, not merely among divisors preselected for convenience:
the subgroup proof first established that the actual minimum divides D.
Function periods restricted to a canonical interval or to selected unit
inputs are different questions, and no minimality for them is asserted.

## 4. Full costs of computing S_min

Let b=bitlen(N) and w=bitlen(D)=Theta(R log(R+1)). The following gives a
uniform algorithm with cost polynomial in R and b.

- Compute D and the primes through 2R+1 using paid elementary factorial
  arithmetic and a sieve. The prime factors of D need no factorization
  oracle; their exponents can be counted in the factorial, with the extra
  2R at prime 2. Prime acquisition has polynomial cost in R and can use
  O(R log(R+1)) bits even with a simple array implementation.
- Read all b input bits and compute N mod D. A streaming binary reduction
  takes O(bw) elementary bit operations and O(w) workspace, with the input
  tape separate. Generate nu_k recursively by modular multiplication using
  O(R) operations. Never materialize N^(2R).
- The setup in (1) costs O(R^2) coefficient operations plus O(R) exact
  multiplier divisions, all at O(w) width. Dense storage of every C_k is
  unnecessary. Keep O(R) residues and the current row, O(Rw) bits.
- For a trial t<=D, evaluate P(i+t) and P(i) modulo D by Horner for
  0<=i<2R, for both polynomials. Arguments have O(w) bits because D>2R.
  This is O(R^2) modular operations. An in-place difference row has O(Rw)
  bits and takes O(R^2) subtractions. Storing the whole triangle is not
  needed for the stated memory bound.
- Each successful strip reduces S by at least two, so there are at most
  floor(log_2 D) successes. There are at most pi(2R+1)=O(R) failures.
  Total period-test work is O(R^2(w+R)) modular operations.

Using schoolbook arithmetic, one conservative bit upper bound for these
steps is O(bw+R^2(w+R+1)w^2), with small-prime setup included within a
polynomial of that size. This is not an optimized arithmetic claim.
Residues have w bits; products and unreduced sums temporarily have O(w)
bits, with their reduction paid. Input storage, if resident, adds b bits;
the O(Rw) working-data bound is not a claim that reading N costs only w.

The construction is polynomial in the *value* R and b, not necessarily in
log R and b if R were an arbitrarily large binary-encoded external input.
For a polynomial-time factoring use, the N-only choice of R must itself
be bounded by poly(b). The proposed prospective choice R=Theta(b) has this
property, and would make w=Theta(b log(b+1)); w need not be O(b) after the
old D-width gate is removed. Denominator-unit certification, if desired,
also costs work, for example a gcd with D after reducing N. A nonunit
exit must be localized using the known small primes if it is to be counted
as a proper split.

This cost is for computing S_min, not acquiring a useful a0, evaluating
scalar digits, completing a stencil, or producing a factor. It does not
assert a same-cost replacement for scalar powering at growing R.

## 5. The smaller period validly changes the canonical filter

Take an actual unwrapped progression a_i=a0+i S_min for 0<=i<=m=2R+1,
with every a_i in [0,N) and a unit modulo N. Global period equality fixes
both labels e,h on this progression and at all its integer-indexed points.
Define rational polynomials in i by

    J(i) = (C_R((a0+i S_min)^2)-e)/D,
    Q(i) = e/D+hN/D
           + sum_(k<R) N^(2k-2R) G_k((a0+i S_min)^2).

J has integer values on every integer i, and degree at most 2R. Its
coefficients need not be integers: function periodicity is enough.
Q has degree at most 2R-2. The accepted canonical floor identity yields

    d_R(a_i) = J(i)+floor Q(i) mod N,
    Z = sum_(i=0..m) (-1)^(m-i) binom(m,i) d_R(a_i) = c mod N,
    c = Delta^m floor Q(0) = -Delta^m {Q}(0) in Z,
    |c|<2^(m-1)=4^R,              gcd(Z,N)=gcd(c,N).       (4)

The proof uses annihilation over Q and fractional parts in [0,1). It
requires neither every C_k to have period S_min nor their coefficientwise
invariance. Only the two actual labels are needed. For R=1, Q is constant
and c=0 exactly, for every admitted stencil, including with the smaller
period. Global small periods do not change that boundary case.

The necessary width inequality is now m S_min<N. In fact a canonical unit
start lies in 1<=a0<=N-1-m S_min, and even a nonempty such interval need
not supply a full unit stencil. Since S_min|D, gcd(S_min,N)=1, but that
does not ensure gcd(a0+i S_min,N)=1. All attempted starts and initial gcds
are paid separately. Wrapping modulo N does not preserve the displayed
polynomial-in-i argument and is not justified by this proof.

As before, leastprime(N)>4^R excludes a proper filtered gcd; c=0 gives
the full gcd. Individual digit gcds and initial nonunit exits are separate
consumers. Removing the old subpolynomial upper bound on 4^R would remove
one obstruction, without proving any useful nonzero residual or separating
law. The exact period routine does acquire a well-defined input parameter;
it does not acquire a productive stencil or a factor.

## 6. Symbolic structural result: the exact 2-primary component

This section proves (A) for the actual polynomials, independently of any
finite period computation. Set e_2=v_2(D) and r=v_2(R). Write either P=E
or P=H as

    P(A)=b_0+sum_(j=1..R) b_j A^(2j).

The leading coefficient of E is B_R=product_(i=1..R)(2i-1)^2, which is
odd. That of H is N^(2R)B_R, also odd since N is odd. Every lower b_j is
divisible by q_j, by (1). For 1<=j<R,

    v_2(b_j) >= v_2(q_j)
      = 2(R-j)+v_2((2R+1)!/(2j+1)!)
      >= 2(R-j)+1+r,                                    (5)

because the factorial quotient contains the even factor 2R. Zero
coefficients satisfy this inequality with infinite valuation. Constants
cancel from translations.

We use an elementary binomial fact. If t has v_2(t)=s>=2 and m>=1,

    v_2((A+t)^m-A^m) >= s+v_2(m) for every integer A,

with equality when A is odd. To prove it, use
k binom(m,k)=m binom(m-1,k-1), so
v_2(binom(m,k))>=v_2(m)-v_2(k). The kth expansion term has valuation at
least ks+v_2(m)-v_2(k). For k>=2, (k-1)s>v_2(k), whereas the first term
has exactly s+v_2(m) for odd A. This also proves the lower bound at even A.
No modular inversion is involved.

There are three translation cases.

1. If t is odd, reduction modulo 2 gives P(A)=b_0+A^(2R) as a function.
   At A=0 its difference is odd, so t is not a period modulo 2^e_2.
2. If v_2(t)=1, evaluate P(t)-P(0). The leading term has valuation 2R.
   By (5) every lower term has valuation at least 2R+1+r. Therefore the
   difference has valuation exactly 2R, less than e_2=2R+v_2((2R+1)!).
   Such a translation is not a period either.
3. If s=v_2(t)>=2, evaluate at A=1. The leading difference has valuation
   s+1+r. By (5), every lower difference has valuation at least
   2(R-j)+1+r+s+1+v_2(j), strictly larger. Thus

       v_2(P(1+t)-P(1))=s+1+r.                          (6)

   For every A the same expansion bounds give at least s+1+r for the
   full difference. Hence a translation of valuation s>=2 is a period
   modulo 2^e_2 iff s>=e_2-1-r.

Put s0=e_2-1-r. Since v_2((2R+1)!)>=R and v_2(R)<=R-1, s0>=2R>=2.
All cases therefore combine to show that the smallest positive function
period of **each** P modulo 2^e_2 is exactly 2^s0. This proof uses actual
function values for necessity, not coefficientwise translation equality.

To transfer the result to S_min modulo D, apply the period-subgroup argument
separately modulo each prime power ell^v_ell(D). Its minimum divides that
prime power and therefore is an ell-power. Chinese remaindering shows the
global common minimum is the least common multiple of these local minima.
The two polynomials have the same 2-primary minimum just proved, so
v_2(S_min)=s0, establishing the first equality in (A).

For completeness, counting multiples of powers of two in n! gives
v_2(n!)=sum_(k>=1) floor(n/2^k)=n-s_2(n); expand n in binary and sum each
bit's contribution. With n=2R+1 this proves the second equality in (A).
Since s_2(2R+1) and v_2(R) are O(log(R+1)), it follows uniformly that

    S_min >= 2^(4R-O(log(R+1))),        S_min >= 4^R.      (7)

The exact 2-primary result is independent of N for every odd N, thus in
particular for the entire permitted least-prime branch. It is compatible
with an exp(O(R)) *full* period; it does not prove such an upper bound.
One implementation could directly retain 2^s0 and strip only the other
prime powers, but no revised implementation or run was made here.

## 7. The top-prime obstruction and what remains unknown

Suppose ell=2R+1 is prime. For every j<R, ell divides q_j, since its
numerator D contains ell once and D_j does not. Thus

    E(A) = B_R A^(ell-1) mod ell,

where ell does not divide B_R: all its odd factors are smaller than ell.
If ell does not divide t, E(t)-E(0)=B_R t^(ell-1) is nonzero in the prime
field. This is already the zeroth Newton coefficient of the translation
test, and excludes t as a function period. Therefore ell|S_min. Since
v_ell(D)=1 and S_min|D, in fact v_ell(S_min)=1. H has the same reduction
times the unit N^(2R), although E alone suffices.

This proves the observation in the brief without mistaking a nonzero
polynomial for a nonzero function. It gives one prime at a particular R;
it does not multiply together top primes belonging to *different* R. Nor
does it produce a lower bound proportional to R log R in log S_min.

For fixed R, E and D are fixed and H modulo D depends only on N modulo D
(even N^2 modulo D suffices). Hence S_min(N,R) takes only finitely many
values dividing a fixed D. The 2-primary value in (A) and the top-prime
statement hold for every allowed N, while the remaining local periods can
be N-dependent. Increasing N at fixed R establishes no asymptotic law as
R grows. Conversely, the exact algorithm is valid at every supplied R
without needing any growth hypothesis.

The present uniform bounds leave the genuine gap

    (4 log 2)R-O(log(R+1)) <= log S_min
                          <= log D = O(R log(R+1)).      (8)

Thus a legal canonical stencil implies R=O(log N), more precisely
R <= (log N)/(4 log 2)+O(log log N) as N grows. This is compatible with
linear-in-log-N depth, but is only an upper restriction, not an existence
theorem for such stencils. It neither restores the old
O(log N/log log N) restriction nor proves that it has been escaped.

The next decisive proof concerns the odd-prime local periods for this
specific coefficient family: prove a uniform or explicitly scoped
N-dependent upper bound on their total logarithmic contribution, or prove
a matching factorial-scale lower bound. Inspecting selected Newton
coefficients is legitimate only with their actual valuation and function
meaning justified. The two results here are insufficient to choose between
those outcomes. No finite diagnostic or assumed small-period oracle can
replace that proof.

## Disposition and handoff

The new computation resolves the *acquisition* objection: the exact minimal
common period is uniformly computable in polynomial(R, bitlen(N)) time
from public inputs, with all setup and growing bit widths paid. It is a
materially different acquisition from blindly using D. The canonical
filter then obeys exactly the same strict residual bound with that period.

The unresolved gain is structural and probabilistic, not an omitted
algorithm for period finding. Even an exp(O(R)) upper bound would still
require a paid N-only selection of legal unit stencils and a proper-factor
yield theorem, charging zero residuals, unit/full gcds, retries and scalar
or exact-floor evaluations. The full-lift law supplies no canonical-input
substitute. No near-top conclusion or complete factoring bound follows.

The [validation record](W032-label-period-review-evidence/validation.json)
records all frozen-file checks, the anchored prior-delivery verification,
live-input drift, and the symbolic-only scope. The
[delivery manifest](W032-label-period-review-evidence/delivery-manifest.json)
lists every payload including this report, with byte length and SHA-256.
It and [terminal-manifest.sha256](W032-label-period-review-evidence/terminal-manifest.sha256)
are the two explicitly excluded inventory files, avoiding circular hashes.
They plus the listed payloads are the complete delivery. The finalized
manifest's hash is returned separately in the terminal handoff; nothing is
appended to sealed payloads afterward. Hashes establish byte identity, not
formal correctness. **Verified complete factoring improvement: NONE.**
