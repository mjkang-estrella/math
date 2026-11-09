# W002 Lens C — an explicit Ward norm tensor and its charged failure

2026-10-08. Constructive symbolic research, not an independent review.
**Verified COMPLETE classical factoring complexity improvement: NONE.**
**All new deductions in this report are UNACCEPTED pending independent review.**

The selected realization is a closed, division-safe tensor recurrence for the
batch product of division-polynomial values. It computes that product without
forming a univariate remainder at every scalar step. Its complete state has
`8^s` residues for `s` retained parameters; its explicit transition expands
`16^s` terms. Keeping the tensor in its known factored representation instead
gives ordinary `O(s log K)` scalar recurrence work. Neither implementation
provides the requested uniform improvement. This closes these implementations,
not all norm algorithms, all batch evaluators, or factoring.

The frozen brief is `research/hypotheses/W002.md`, SHA-256
`5f34c276110ba4ad79781b16b4a86d7ea3860671d168939aca9c399b0480f723`;
the on-disk bytes matched. H030 and H031 dispositions were read and treated as
completed. Their scoped acceptance does not establish a new factoring bound.
The older live-H031 wording in STATE and W001 synthesis is superseded by the
user handoff and current disposition. No sibling W002 draft was opened.

## 1. Prior art and selection of the realization

Read the required project instructions, W001 synthesis, W001-dynamics Card 4,
the complete H009 finding, and the Li source note. H009's finite coefficient
density screen is not a universal modular lower bound. Its separate
characteristic-zero derivation is not used as an accepted theorem here.

The underlying division-polynomial recurrence, parameter batching, polynomial
evaluation, and product splitting are existing work. Li's dissertation gives
the recurrence in Definition 3.1.1, a short window of adjacent division
polynomials in section 3.3, and batch gcd/splitting in Algorithm 4.1.1. Sections
4.5–4.6 give ordinary evaluation bounds and the special-input cyclic reduction;
the latter retains curve-count times scalar-length work. The proof of Theorem
4.1.3 assumes an order-distribution model. These passages do not supply an
additive batch evaluator or justify that model for the fixed family here.
[Li, 2006, primary dissertation](https://www.cerias.purdue.edu/assets/pdf/bibtex_archive/2006-43.pdf).

Three concrete directions were considered within the final-output lens:

1. **Only scalar norms of adjacent Ward values.** Multiplication transports,
   but subtraction requires the cross terms displayed below. No closed
   recurrence on those scalar norms was obtained.
2. **Keep the polynomial `prod_i(U_i-z V_i)` at each subtraction.** Its `s+1`
   coefficients suffice for that one subtraction. Given the individual pairs,
   they can be constructed by multiplying linear polynomials. This does not
   explain how to obtain the next pairs or their joint correlations without
   evaluating the individual curves. No independently costed closed transition
   on just those coefficients was found.
3. **Retain a full labelled tensor of an adjacent Ward window.** Quartic
   homogeneity supplies an exact closed transition, with no factor/order/root
   oracle and no inversion of a division-polynomial value. This is the
   selected construction, developed completely below.

The tensor is a direct distributive expansion, not a novelty claim. The source
check was bounded, not an exhaustive search for every equivalent tensor
description. Cyclic domains and dense quotient-ring recurrence are not proposed
again as new mechanisms.

## 2. Input-only setup and a finite sampling law

The batch evaluator has explicit inputs `(N,K,a_1,...,a_s)`. To make it a
concrete N-only research trial, use the following fixed driver on composite
`N>1`, with `n=floor(log2 N)+1`:

1. Return 2 or 3 if it is a proper divisor. Thereafter `gcd(N,6)=1`.
2. Set `B=n^2` and `r=n`, and construct `K=lcm(1,...,B)`. The formulas below
   also price arbitrary public integer choices `B>=2,r>=1`; no such choice may
   depend on a supplied hidden factor. The fixed choice is a finite example,
   not a claimed good parameter optimization.
3. Draw exactly `r` independent `n`-bit words. A word `a>=N` is a rejected slot;
   do not resample it. For every other slot compute `g=gcd(4a^3+27,N)`.
   Return a verified factor if `1<g<N`; discard the slot if `g=N`; retain it
   if `g=1`. Preserve its original slot label. Duplicates are retained.
4. In the absence of an early factor, let the retained list have length `s<=r`.
   Compute the batch product by the selected tensor recurrence and run the
   complete extraction procedure in section 6. If it returns no factor, return
   `FAIL`. An empty retained list has product 1 and returns `FAIL`.

All random words may be sampled before screening, so the random-tape length is
exactly `rn` even when an early gcd succeeds. Conditional on `a<N`, each word
is uniform in `Z/NZ`; retention is the stated discriminant filter. There is
no assertion that a geometric orbit, torsion-selected family, or uniform
isomorphism class distribution has this law. No attempt is spent obtaining
exactly `r` good curves through unbounded rejection sampling.

For setup, generate composite marks `(j k)` for all integers `j,k>=2` with
`j k<=B`, sort and deduplicate them, and scan `[2,B]` to get the primes. There
are `O(B log B)` marks of `O(log B)` bits. This gives a sequential-access sieve
in `B polylog B` bit operations and space without pretending random table
access is free. For each prime construct its largest power at most B by
repeated multiplication. Multiply these powers by a balanced product tree.
Writing `M(t)` for an admissible t-bit integer multiplication/modular
multiplication upper bound, setup costs

`S(B) = O(B polylog B + M(B) log B)` bit operations,

with `B polylog B` bits of scratch under standard regularity for M. Here
`h=bitlength(K)=Theta(B)` by the usual Chebyshev bound for `log lcm(1,...,B)`.
Even the weaker `h<=B log2 B` suffices for a finite construction. K is stored
explicitly in h bits; it is never treated as a word-size scalar. The sieve's
temporary storage can be released before tensor construction.

Screening all slots costs `O(r(M(n)+G(n)+n))`, with G a gcd upper bound;
retained labels cost `O(r(n+log(r+1)))` bits. Trial division by 2 and 3 and
verifying any returned divisor are charged. The only inverse in the evaluator
is `u=2^(-1) mod N=(N+1)/2`, constructed in `O(n)` bit work.

## 3. A fixed eight-coordinate scalar state

In `R=Z/NZ`, put

`f_j(a)=psi_j(0,1;a,1)`.

The initial values are

`f_1=1,  f_2=2,  f_3=-a^2,  f_4=-4(a^3+8)`.

The needed identities are

`f_(2q+1) = f_(q+2) f_q^3 - f_(q-1) f_(q+1)^3`,

`f_(2q) = u f_q (f_(q+2) f_(q-1)^2 - f_(q-2) f_(q+1)^2)`.

These are the cited division-polynomial identities specialized at `(0,1)`;
only the constant 2 is divided out. In particular there is no division by
`f_q`, no division by a parameter difference, and no square-root extraction.

Let `J={-3,-2,-1,0,1,2,3,4}` and

`v_m(a)=(f_(m+j)(a))_(j in J)`.

For `h>=3`, take m to be the integer represented by the first three binary
digits of K, so `4<=m<=7`. Construct `f_1,...,f_11` in increasing index order
from the four base values and the displayed formulas. This uses a constant
number of ring operations per parameter. It initializes all eight entries
without negative indices or using a recurrence outside its stated base range.
When `h<3`, evaluate the few needed base values directly and multiply them.

For each remaining scalar bit `b in {0,1}`, send `m` to `2m+b`. For an output
coordinate `j in J`, define `delta=b+j` and these two ordered four-tuples:

- If `delta=2t+1`, set
  `A_(b,j,0)=(t+2,t,t,t)`,
  `A_(b,j,1)=(t-1,t+1,t+1,t+1)`, and `c_(b,j)=1`.
- If `delta=2t`, set
  `A_(b,j,0)=(t,t+2,t-1,t-1)`,
  `A_(b,j,1)=(t,t-2,t+1,t+1)`, and `c_(b,j)=u`.

Every component of these tuples lies in J: the odd t-range is contained in
`[-2,2]`, the even t-range in `[-1,2]`, with the endpoint restrictions given
by delta. For `m>=4`, the odd recurrence uses `q>=2`, the even one `q>=3`.
Thus the same finite table handles every subsequent bit. In coordinates,

`F_b(v)_j = c_(b,j) [prod_(l=1..4) v_(A_(b,j,0,l))`
`                         - prod_(l=1..4) v_(A_(b,j,1,l))]`.       (1)

This is a homogeneous quartic map on the eight coordinates. The four-factor
form, including the factor `f_q` in the even case, is what permits the next
construction. The prefix m need not be updated as a growing integer in the
program; it is the proof invariant while the program streams the bits of K.

## 4. All norm cross terms, and a transition that really computes them

For one odd Ward update, write

`U_i=f_(m+2)(a_i) f_m(a_i)^3`,
`V_i=f_(m-1)(a_i) f_(m+1)(a_i)^3`.

Then the next batch product is exactly

`sum_(S subset {1,...,s}) (-1)^|S|`
`        (prod_(i in S) V_i) (prod_(i notin S) U_i)`.             (2)

Products of individual adjacent norms determine the empty and full subset
terms, but do not in general determine the other terms. The formal two-row
calculation

`(x-u)(y-v) - (x-v)(y-u) = (x-y)(u-v)`

exhibits why the separate products `xy` and `uv` do not determine a difference
norm for arbitrary row data. This is a symbolic identity, not a numerical
experiment. It is also **not** a proof that two actual ECM parameter lists
share every proposed scalar statistic while their next norms differ: the
elliptic identities may impose additional restrictions. No universal
impossibility theorem for scalar statistics is asserted.

For an actual closed state, retain one residue for every labelled tuple
`alpha in J^s`:

`T_m(alpha) = prod_(i=1..s) f_(m+alpha_i)(a_i)`.                (3)

This is the full tensor `v_m(a_1) tensor ... tensor v_m(a_s)` in its explicit
coordinate representation. There are exactly `8^s` allocated entries. Build
`T_m` initially by successive tensor products of the initialized eight-vectors;
the total number of entries written is `sum_(i=1..s) 8^i=O(8^s)`.

For `j=(j_1,...,j_s) in J^s` and `epsilon in {0,1}^s`, form four old-state
addresses

`alpha^(l)(j,epsilon)_i = A_(b,j_i,epsilon_i,l)`,  `1<=l<=4`.

Let `e_b(j)` count the coordinates for which `b+j_i` is even. The transition is

`T_(2m+b)(j) = u^e_b(j) sum_(epsilon in {0,1}^s) (-1)^|epsilon|`
`                              prod_(l=1..4) T_m(alpha^(l)(j,epsilon))`.  (4)

This is an executable finite transition: enumerate the `8^s` output addresses,
enumerate all `2^s` binary choices for each address, read the four specified
old entries, multiply them modulo N, sum with the indicated sign, and scale
by the cached power of u. Cache `u^0,...,u^s` once in O(s) multiplications.
Coincident addresses, zero entries, duplicate curves and cancellation are all
allowed; they do not require a unit test or a change in (4).

Proof of the invariant is direct. Substitute (3) into each term of (4), exchange
the products over l and i, and then distribute the sum over the independent
choices `epsilon_i`. The result is `prod_i F_b(v_m(a_i))_(j_i)`, which is the
new instance of (3) by (1). At the last prefix `m=K`, read

`T_K(0,...,0)=prod_i psi_K(0,1;a_i,1) mod N`.                  (5)

Equations (1)–(5), the initialization, and the enumeration order supply the
algorithm; a norm or resultant symbol alone is not being used as a subroutine.
No quotient polynomial in the parameter is formed.

## 5. Time, widths, access and the compressed fallback

Every modular entry has n-bit fixed-width storage; pre-reduction products have
at most 2n bits. Addresses have `3s` bits, rather than unit-cost unbounded
indices. A literal transition has `8^s*2^s=16^s` summands and a constant number
of modular multiplications per summand, plus address formation and reductions.
Preprocessing the fixed tuple table of (1) has constant size independent of N,
K and s; the large state is constructed for this input and is not advice.

Here is an explicit sequential-access implementation, so the claimed upper
bound does not grant free random access to an exponential table. For each
summand emit four lookup requests labelled by its output address, branch
epsilon, and factor number l. A record has `O(n+s)` bits including its eventual
value. Sort requests by old-state address; merge against the sorted old tensor
to attach values; sort back by output address, epsilon and l. Stream groups of
four to multiply, then sum by output address and scale. Ordinary merge sorting
uses `O(s)` passes on `O(16^s)` records. Initial tensor construction can also
use sequential scans. One query therefore has the upper bound

`C(s,h,n) = O(h 16^s [M(n)+s(n+s)])`,                         (6)

for `s>=1`, including initialization, bit streaming, power caching and final
decoding. The bound is deliberately conservative for the few small h values,
where direct evaluation applies. Working storage, including sort scratch, is

`O(16^s(n+s) + h + s(n+log(r+1)) + W(n))` bits,              (7)

where W(n) is the workspace of the chosen multiplication, reduction, gcd and
verification routines; standard choices give `W(n)=n polylog n`. Their
workspace is reused across operations, not granted for free. The integer
product construction in S(B) likewise fits its `B polylog B` workspace.

The tensor itself requires `8^s` n-bit slots, and for `h>3` this specified
implementation writes all of them at each of `h-3` transitions. Consequently
it has a representation-specific lower bound

`Omega((h-3) 8^s n)` bit writes.                            (8)

This counts explicitly allocated fixed-width output, including zero entries;
it does not infer a nonzero-density theorem modulo N. In particular it does
not use H009's characteristic-zero density argument. Bound (8) alone defeats
an additive `(s+h) poly(n,log(s+h))` target uniformly as s and h grow in the
intended range. Constant s yields ordinary O(h) work up to s-dependent
constants; it supplies no many-curve speedup. Even `s=Theta(log h)` introduces
a polynomial factor in h through these explicit slots.

There is a much smaller representation already known at initialization:
retain the s eight-vectors whose tensor product is T. Applying (1) separately
preserves that factorization exactly and costs `O(sh M(n))`. Multiplying the
s final entries and forming their product tree adds `O(s M(n))`; all tree gcds
cost `O(s G(n))`. Live storage is `O(s(n+log(s+1))+h)` bits when final values
and the tree are retained, plus W(n) arithmetic workspace. This handles
arbitrary supplied parameters and
does not require recovering a tensor factorization over a composite ring.

Thus the strongest useful upper bound among the explicit realizations here
is the known scalar one, including setup and extraction:

`S(B) + O(r h M(n) + r G(n) + r(n+log(r+1)))`, with `h=Theta(B)`.  (9)

This is a fallback comparison, not the cost assigned to the explicit tensor.
Breaking s curves into fixed-size tensor blocks retains a number of blocks
proportional to s and h steps per block; it also gives no additive escape.
The first actual obstruction is the size of the selected closed cross-term
state and its explicit updates, not a theorem that norms cannot be useful.

## 6. Complete product-gcd recovery, including full-gcd leaves

Let `z_i=f_K(a_i)` for a supplied retained list. The product oracle used here
is the finite construction (3)–(5), freshly initialized on the requested
contiguous sublist. It never divides an old product by another product.

Query the whole list and compute `d=gcd(product,N)`:

- If `d=1`, return failure for that node.
- If `1<d<N`, verify `N mod d=0` and return d.
- If `d=N` and the node is a singleton, record an unproductive full-gcd leaf
  and return failure for that node. No factor is asserted.
- Otherwise split into two nearly equal contiguous sublists and recursively
  search the left, then the right if necessary. Preserve all original labels
  and multiplicities; do not deduplicate the inputs.

At most `2s-1` product queries and gcds occur, and at most s full-gcd leaves
fail. A gcd-1 node contains only unit leaves, so it cannot hide a proper-gcd
leaf. If any leaf has `1<gcd(z_i,N)<N`, this procedure returns a proper factor,
unless it has already returned one from an ancestor. Conversely, if every leaf
gcd is 1 or N, every node gcd is 1 or N. Hence, for every composite N, successful
extraction is equivalent to existence of a proper-gcd leaf. This statement
does not require N to be squarefree; products can saturate a prime power at a
parent, but the same descent still finds a proper leaf when one exists.

Let `s_v` be node lengths in the full balanced tree. The elementary induction

`sum_v 16^s_v <= 2*16^s`

follows from `16^s+2*16^floor(s/2)+2*16^ceil(s/2)<=2*16^s` for `s>=2`
and the singleton base case. Since `M(n)+t(n+t)` is nondecreasing in t,
**all** recomputed tensor queries together still obey the upper bound (6),
plus `O(s G(n))` for the gcds and a final exact-division verification. Initial
states are recomputed and charged at every visited node. Depth-first execution
releases each query's tensor and sorting scratch before descending; its peak
is bounded by (7), a logarithmic-depth index stack, and the stored parameter
list. Reading the requested lists costs at most `O(s log(s+1)(n+log(r+1)))`
bits of scans, absorbed by this tensor bound.

For the scalar fallback in (9), retain all z_i and the ordinary binary product
tree. This avoids scalar reevaluation during descent; the `O(s)` products,
gcds, failed leaves and storage are already charged there.

Combining setup, all rejected slots, the tensor queries and extraction gives
the actual trial upper bound

`S(B) + O(r(M(n)+G(n)+n+log(r+1))) + C(s,h,n)`,

with `C(0,h,n)=0` and `s<=r`; a uniform worst-case bound replaces s by r.
Peak workspace is the larger of the setup workspace and (7), together with
the stored raw words/labels `O(r(n+log(r+1)))`. No once-per-input preparation,
rejected data, fresh subquery initialization, or unsuccessful leaf is omitted.

The exponential tensor query dominates all its subqueries, which is why its
recovery stays within the same bad envelope. That observation would not
transfer to a hypothetical query bound `O(B+s)`: a full binary descent could
then pay `Theta(s B)` in repeated setup. An additive single-product claim
would need a separately justified recovery bound or retained extraction data.
No such stronger conclusion is hidden in this report.

## 7. Exact success law and what it does not establish

For the fixed N-only trial, define a set of useful residue values

`U_(N,B)={a in [0,N):`
`  1<gcd(4a^3+27,N)<N, or`
`  gcd(4a^3+27,N)=1 and 1<gcd(f_K(a),N)<N }`.

This is a mathematical description of the law, **not** an algorithm that
enumerates U or is allowed to know its cardinality. Set

`tau_(N,B)=|U_(N,B)|/2^n`.

Independence of the raw words and the extraction equivalence in section 6 give
the exact finite-trial identity

`sigma_(N,B,r)=1-(1-tau_(N,B))^r`.                            (10)

All words outside `[0,N)`, singular-full-gcd rejections, unit final values,
and full-gcd final leaves remain in this denominator. An early discriminant
success is included, not conditioned away. Repeated residue values are also
included. Independence here is independence of sampled words and events that
are functions of each word, not an assumption about distinct curve orders.

For an explicit semiprime interpretation only, suppose `N=pq` with distinct
primes greater than 3. Define

`D_l={a in F_l:4a^3+27 != 0}`, `t_l=|D_l|/l`,

`eta_l(B)=#{a in D_l: ord_(E_a(F_l))(0,1) divides K}/|D_l|`.

CRT independence for a uniform residue modulo pq and the division-polynomial
annihilation criterion yield

`tau_(N,B) = (N/2^n) [ (1-t_p)t_q+t_p(1-t_q)`
`                + t_p t_q (eta_p(1-eta_q)+(1-eta_p)eta_q) ]`.  (11)

The first two terms are successful discriminant gcds. The last two are
annihilation at exactly one component on a nonsingular retained curve. This
formula does not assert any particular sizes for eta_p or eta_q. It is specific
to independent raw uniform words, the fixed point and b=1 family, and this K.
It is not a law for a short geometric orbit or a prescribed torsion domain.

The condition is `ord(P) | K`, not merely that the largest prime divisor of
`#E_a(F_l)` is at most B. With `K=lcm(1,...,B)`, each needed prime-power
exponent must fit in K as well. A general smoothness slogan does not prove
this event, its frequency in this one-parameter family, or proper splitting.

No positive uniform lower bound on tau has been proved. If a fixed trial is
repeated independently, including all setup each time, and sigma>0, its expected
total cost is `E[T_trial]/sigma`. If sigma=0, repetition never succeeds. A
fixed cap of Q trials has success `1-(1-sigma)^Q` and costs at most Q times the
charged worst-case trial bound. Neither formula supplies the missing useful
probability. The trial can be made a complete splitter by a deterministic
exhaustive divisor search after failure, but the additional
`O(sqrt(N)*poly(n))` work gives only an elementary known completion, and the
tensor trial can make that completion still worse. No improved complete bound
is claimed through that fallback.

## 8. Matched asymptotic comparison and disposition

The original ECM analysis presents its familiar small-factor bound as
conjectural; it is not a rigorous all-input performance theorem for this
particular parameter distribution.
[Lenstra, 1987, publisher abstract and metadata](https://annals.math.princeton.edu/1987/126-3/p09).

For comparison only, adopt the explicit additional law on the *useful slot
probability* itself: with `X=log p`, `log B=b sqrt(X log X)` and b fixed positive,
assume

`tau_(N,B)^(-1)=exp((1/(2b)+o(1))*sqrt(X log X))`,

uniformly on the input regime under discussion. This law includes the
rejections, exact K-divisibility and useful CRT event in (10)–(11); it is
stronger than quoting a smooth-integer frequency. Choose `r` of its inverse
scale so trial success is bounded away from zero. Equation (9) then has the
usual matched leading expression `b+1/(2b)`, whose infimum is `sqrt(2)`.
For this comparison take quasi-linear integer multiplication, so S(B) has
leading B scale and the n-bit arithmetic contributes only polynomial factors
in n; slower setup arithmetic would not improve the comparison.
This calculation is an optimization of a conditional model, not permission to
choose B from an unknown supplied p or a proof that the fixed `B=n^2,r=n`
driver has that running time.

The explicit tensor writes `8^s` entries for the retained size s. At supplied
size `s=r` this is immediately much worse. In the same semiprime model with
`r=L_p[1/2,O(1)]`, the raw-slot law does not normally rescue it by rejection:
the cubic discriminant has at most three zeros at each prime, so early
discriminant success has probability at most `3r(1/p+1/q)=o(1)`. Each slot is
retained with probability at least `(1/2)(1-3/p)(1-3/q)`. Independent-slot
concentration therefore gives `s>=r/4` with probability `1-o(1)`. Thus even
initial tensor allocation is exponential in r in this conditional comparison.
The often-desired additive cost would instead produce
`max(b,1/(2b))`, with infimum `1/sqrt(2)`, **only** after a uniform additive
algorithm, charged recovery, and the actual useful-probability law were
established. This report establishes none of those missing improvements.
Even that hypothetical ECM change keeps the `L_p[1/2]` exponent; for balanced
general inputs it would not beat the heuristic general-NFS `L_N[1/3]` exponent.
The latter exponent and its heuristic qualification were checked directly on
printed pp. 169–170 of
[Coppersmith's primary paper](W002-ecm-source-coppersmith1993.pdf).
It is also separate from rigorous complete factoring and deterministic
power-of-N bounds; `N^(1/6)` would still be exponential in input bit length.

**Strongest supported conclusion:** the displayed tensor invariant gives a
finite, exact batch-product algorithm over every odd composite modulus,
with fully paid gcd recovery, but its explicit state loses exponentially in
the batch size. Preserving its obvious factorization is ordinary independent
curve evaluation with multiplicative scalar-length cost. The selected
norm-first realization is closed as a speedup.

**Exact remaining limitation:** no smaller constructed state with cheap
closed transitions and productive-factor recovery has been supplied. The
cross-term calculation and the literal-state write count do not preclude such
a state on the actual elliptic family. Separately, no useful-success lower
bound for the actual trial law has been proved.

**Next proof/test:** none selected. The symbolic construction already misses
the objective; a numerical tensor run, a larger H009 screen, or a Lean
encoding would not resolve either missing algorithmic step. Any later
reopening should first supply a materially different explicit transition,
rather than treating a desired compressed norm as an oracle. This report's
new derivations remain available for the coordinator's independent review;
they have not been accepted by this author.

## 9. Evidence and execution record

[W002-ecm-provenance.json](W002-ecm-provenance.json) records 20 frozen input
snapshots, byte counts, hashes, URLs and retrieval limitations. The delivery
manifest [W002-ecm-delivery.sha256](W002-ecm-delivery.sha256) identifies this
report and all its adjacent owned artifacts. The frozen brief identity matches
the user's supplied digest.

Li's full archived dissertation was preserved under the owned input prefix.
Its PDF SHA-256 is
`36180aa6bab0fa502efbb4ac0e27e41f055a1a5ffa5d3119d81b9841e3362185`.
Selected passages of chapters 3–4 were read in the existing layout extraction;
printed pages 17, 45 and 49 were visually inspected. The live primary PDF
endpoint also opened successfully. No full-dissertation, FFT precision,
implementation, or probability-theorem audit is asserted.

The newly retrieved Lenstra paper is preserved as
[W002-ecm-source-lenstra1987.pdf](W002-ecm-source-lenstra1987.pdf), SHA-256
`0e1e07c4bbfff73b9d36c981c3466c19e37a930412440baf38360386f81433d3`.
Its text extraction contains only page breaks; that failed reading aid was
retained rather than represented as readable text. Printed pages 649–650
were rendered and visually inspected, and the publisher abstract/metadata
was read and archived as HTML. Search-index crawl dates were not used as
publication dates. Search results beyond these identified sources supply no
mathematical claims here.

The existing primary archive of Coppersmith, *Modifications to the Number Field
Sieve*, Journal of Cryptology 6 (1993), 169–180, was copied under the owned
prefix with its text extraction. Printed pp. 169–170 were read and visually
inspected to check only the NFS exponent and heuristic qualification. The PDF
SHA-256 is `7a389dd62283670a5a4500df0f4baf2d2657250bc5fcce21c356b551dceb26a4`.
This is not a new review of its complete algorithm or of H031.

Only source searches, reads, downloads, text extraction, page rendering,
symbolic reasoning, report writing, evidence copying and hashing occurred.
No mathematical finite experiment, numerical sweep, benchmark, algorithm
implementation, Lean invocation/change, package installation, recursive
delegation, commit, publication or scheduler was performed. No shared file
was changed. There is no numerical input corpus, RNG seed or result set to
reproduce: (1)–(11) specify the proposed symbolic reasoning and future input
law, and the primary-source/input bytes are preserved.
