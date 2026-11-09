# H027 — Independent symbolic review

2026-10-08. **REVISE locally; accept the scoped algebra and cost deductions.**
Accept the recommendation **no implementation or experiment from this round**.
Verified new complete classical factoring complexity improvement: **NONE**.
No new full factoring bound is supplied or accepted.

The mathematical displays A1–A3, B1–B7, C1–C5 and M1 survive review at
specified scopes. The literal B sampler's ensemble-average output obstruction
also survives. Required clarifications concern the fully specified sampler,
actual valuations, literal versus modular relation records, a paid sequential
realization of C4, and overly absolute shorthand for conditional-model results.
These repairs neither produce a survivor nor prove a general impossibility.
The coordinator, not this reviewer, owns adoption and parent-file edits.

## 1. Reviewed bytes, scope and method

I read the governing AGENTS.md, README.md, docs/SPECIFICATION.md,
RESEARCH_LOOP.md, RESEARCH_TEAM.md and all 513 lines of research/STATE.md;
the full H027 hypothesis/brief and intake; all 680 lines of the submitted
construction; the accepted H021/H024/H025/H026 and H016 dispositions; the
current H021 and H024 reports; H026's proof and relevant review sections;
W001's baseline ledger; and H016's integer-processing construction.
The entire submitted draft was read for byte comparison and is identical to
the 680-line construction, so there is only one mathematical text to review.
Both have SHA256:

    24dfd2df7ce509e475d83de93ec19d8f67faa58b0cccbcd8713770da4e11d471

All 17 submitted input entries and all 12 artifact entries matched during this
review's initial verification. Frozen, unchanged copies of 34 inputs are in
[H027-review-inputs](H027-review-inputs/); their identities are recorded in
[H027-review-inputs.sha256](H027-review-inputs.sha256). The captured STATE hash is
`b04c0bf333a5a5b5e3ed62157f2828b10aa46da96ad3b58ccd1036fd984de680`.
It is a historical snapshot, not a constraint on subsequent coordinator edits.
At closing verification, STATE alone had legitimately changed to
`c66da07f6739903e8df4fec3b085fac53d671f6da09f830254beb37b51488377`;
the frozen inputs and all 12 original artifact entries still matched.
The launch instructions supersede stale lifecycle text in that snapshot.
H028/H029 were not investigated or duplicated; no child was started or polled.

This was symbolic review and primary-document inspection only. File copies,
hashes, downloads, text extraction and page rendering are provenance work;
no arithmetic sample, experiment, benchmark, parameter sweep or candidate
implementation was executed. No package, shared code, Lean, registry, parent
report, hypothesis, intake or STATE was edited. No commit, publication or
scheduler was used. My only outputs are this review and H027-review-* artifacts.
No empirical check is needed for the conclusions below, so no finite protocol
is proposed. The literature checks verify attribution and stated scope, not
independent reproving of the cited papers' complete analytic arguments.

Line references below refer to the frozen 680-line submitted text.

## 2. Accepted dependencies and common accounting — ACCEPT

Lines 31–45 preserve the accepted interfaces correctly. H021's rational
bounded-error coefficients are not exact nearest rounding of true logarithms.
H024's nonempty E_star<40ell^2 and indexed-memory optimizer do not establish
useful yield. H026's input count uses the aligned first-ell-prime universe;
it establishes neither a fixed-input/history rarity law nor an obstruction
to arbitrary changed weights, bases, energies or post-LLL domains. H025's
fixed-power-saving density result is not an assertion for every o(N) window.

Lines 73–112 correctly charge elementary preprocessing, prime construction,
units, output bits and duplicate handling. Listing all ordered products ab<=B
with a,b>=2 generates O(B log B) marks; sorting and scanning their complement
certifies the prime list with sequential bit work B*poly(log B). Prime reduction,
gcds and needed inverses contribute B*poly(ell+log B), within the stated setup.
Neither advice nor constant-cost indexed memory is needed for this bound.

For nonzero H-bit values, there are at most k failed divisions and H successful
divisions, validating the conservative trial-division bound. Zero must be
excluded from valuation/product-tree inputs; magnitudes one have empty support.
The faster (B+S)*poly(ell) bound imports the accepted H016 integer construction,
including its fast arithmetic at aggregate widths, prime-partition routing,
full exponent recovery, payloads and output bits. It is not obtained using
schoolbook multiplication on its large product-tree nodes. Keep the separate
conditions H, log B, log S and payload widths=poly(ell). All rejected candidates
remain in S, and undersized batches can repay base setup.
Within an equal-square-residue cluster, compare each retained root with a
fixed representative using gcds before discarding it. If all are global ±
that representative, every pair is trivial; otherwise one comparison splits.
Thus this safeguard costs linear, not quadratic, many gcds per cluster.

## 3. Construction A

**A1. Exact walk, containing objective, convolution and TV — ACCEPT.**

On H=<p_1,...,p_k>, the one-step measure is

    mu = (1/2) delta_1 + (1/(4k)) sum_j (delta_(p_j)+delta_(p_j^-1)).

Coincident residues add their masses; this formula still applies. Fresh starts
at 1 give mu convolution-powered t times. The signed exponent bounds follow
from at most t non-stay steps: ||e||_1<=t and ||e||_2^2<=t^2. The changed flat
objective bound follows from |sum a_j e_j|<=t max|a_j|. It supplies a containing
set, not a uniform law on an energy sublevel set.

With Fourier convention mu_hat(chi)=sum_x mu(x)chi(x), symmetry gives

    mu_hat(chi)=1/2+(1/(2k))sum_j Re chi(p_j)=lambda_chi in [0,1].

Parseval gives

    |H| sum_x |mu^{*t}(x)-1/|H||^2 = sum_(chi!=1) lambda_chi^(2t).

Cauchy–Schwarz then proves A2, including its factor 1/2. For nontrivial chi,
lambda_chi<1 because the chosen residues generate H; this qualitative fact
has no uniform mixing-time consequence. H need not be G. Squaring pushes
this law forward to H^2; it sends uniform H to uniform H^2 and contracts TV.
Replacing H^2 by QR_N requires the additional appropriate group coverage,
and the report makes no such assertion. The spectral expression is not an
N-only method to enumerate H or its characters.

**A2. Random bits, records and sorted access — ACCEPT, with expected-time label.**

For k>1, put d=ceil(log2 k), draw d bits and accept an integer below k.
Acceptance is k/2^d>1/2 unless k is a power of two, when it is one. Expected
bits per accepted index are d*2^d/k<2d in the non-power case. The stay/sign
coins add constant expected bits. For k=1 use its sole index without rejection.
Thus O(t log(k+2)) expected bits is correct. Rejection has unbounded worst-case
length; capped failures must remain explicit. Apply this expected-time label
also to the batch bound at lines 170–171 and to B's analogous random choices.
The arithmetic/access part after the requests have been generated is bounded.

Generate at most St non-stay requests tagged by attempt, index and sign; sort
by index, merge with the paid prime/inverse stream, then sort by attempt.
Multiplication can be reordered because G is abelian. Intermediate walk states
are not selection criteria in this sampler, so its law is unchanged. Sequential
merge sorting pays the record widths and logarithms of list lengths. It gives
(B+St)*poly(ell+log B+log S+log t) expected bit work and a deterministic storage
bound of this scale without an implicit k-scan for every request. Merging
exponent occurrences gives the reported sparse width. The denominator Y in
cost per distinct accepted record is an observed count, not a promised yield.

**A3. Ideal full-group smoothness bound — ACCEPT; actual-walk extension REJECT.**

For distinct odd p,q, the squaring kernel of G has four elements. Uniform g
therefore gives a uniform r on QR_N, of cardinality phi(N)/4. Counting smooth
integers in the whole ambient interval gives A3 even if some are not quadratic
residues. For balanced primes, phi(N)=N(1-O(N^-1/2)). At sigma=3/4,

    log product_(p<=ell^2)(1-p^-sigma)^-1
       <= C sum_(m=2)^(ell^2) m^-3/4 = O(sqrt(ell)).

Together with Psi(N,ell^2)<=N^(3/4) times that product, this proves the stated
N^(-1/4+o(1)) upper bound, uniformly over the balanced-semiprime family.
The constant exponent is a valid loose bound, not an asserted asymptotic.
A walk delta-close to uniform G has smoothness probability at most this bound
plus delta. A small subgroup and a merely inverse-polynomial delta do not
permit deletion of that term. No actual walk yield or root entropy follows.

A direct uniform-unit sampler is polynomial in ell: sample an integer below N
exactly, compute its gcd, and reject nonunits (or return a proper gcd). Even the
elementary bound phi(N)/N>=1/(omega(N)+1)>=1/(ell+1) suffices for expected
polynomial work. Conditional on a square residue, a uniform unit is uniform
on its full root fiber. Subsequent selection must preserve that condition.
This confirms the comparison at lines 198–201, not a positive theorem for A.

## 4. Construction B

**B1. Signed logs, lifting and index — ACCEPT; fix the centered tie.**

The identity at line 226 holds for j=0. If
5^(2^j)=1+2^(j+2)+a*2^(j+3), squaring modulo 2^(j+4) yields
1+2^(j+3): the squared increment is divisible by 2^(j+4).
Thus ord_(2^h)(5)=2^(h-2). The sign s(a) is zero for a=1 mod4 and one
for a=3 mod4; (-1)^s(a)*a lies in the subgroup 1 mod4. That subgroup has D
elements, all generated by 5, proving uniqueness of B1.

Starting with exponent zero modulo 4, bit j is decided by comparing the
current 5-power with the target modulo 2^(j+3); multiplying by 5^(2^j)
toggles exactly the missing bit. Shared successive squares and inverses can
be precomputed in O(h^3) bit work and O(h^2) storage. Maintaining the current
residue permits O(h) modular operations per logarithm, hence O(h^3), not an
unpriced general discrete logarithm. Stored logs cost O(kh) bits additionally.
The O((k+1)h^3) setup is correct besides input reduction/base construction.

The coordinates of 3 and 5 map to (1,d(3)) and (0,1). They generate
Z/2 x Z/D, proving that the homomorphism from the odd-prime exponent lattice
is onto and its kernel index is 2D. For fixed free coordinates there is a
unique solution with e_3 in {0,1} and e_5 in any chosen D-consecutive-integer
interval. Specify, for example,

    e_5 in {-D/2,-D/2+1,...,D/2-1}.

D is even for h>=3. This removes the unassigned tie between ±D/2 and makes
the selector single-valued. Either fixed tie convention preserves all bounds.
The rectangle is a transversal, not a claim that independently reducing an
arbitrary e_3 modulo 2 preserves B2: changing e_3 by 2 may require changing
e_5 by -2d(3). Exactly one solution per 2-by-D rectangle of consecutive
coordinates, or per kernel period, is valid. Arbitrary short-box densities
and N-dependent log-window densities do not follow.

**B2. Literal widths and padded DP — ACCEPT in the specified representation.**

Unique factorization gives coprime odd u,v and B2 implies u-Nv=0 mod2^h.
The free coordinates have l1 norm at most t, e_3 is at most one, and |e_5|<=D/2.
Hence u,v,Nv,u-Nv have O(ell+t log B+2^h) bits. Conversely, materializing
u and v costs at least |e_5| log2(5) bits in one of them: the other prime
coordinates cannot cancel a 5-power in a reduced numerator or denominator.
Cancellation in u-Nv is irrelevant to that particular output lower bound.
It would be incorrect to infer the same lower bound for the bit length of
the residual alone or for every compressed algorithm.

The diagonal energy bound O(t^2+4^h) and explicit 2D-state DP padding are
correct. The latter is the cost of that implementation, not a lower bound
for all algorithms solving the congruences or selecting short representatives.

**B3. Ensemble-average literal-output falsifier — ACCEPT.**

Make the size rules explicit together: B=ell^2, h=ell, t=ell^3, and a law
on free exponents depending only on ell. Fix one free vector f. For any
particular a in {0,1} and integer b with |b|<=L, the congruence

    N = 3^a 5^b product_(free p) p^f_p mod2^ell

specifies at most one ell-bit integer. There are at most
2(2 floor(L)+1) pairs. Possible coincidences and the centered restriction
only reduce that upper count. No uniformity of d(N) is assumed.

Use H026's explicit ensemble E_ell of products of distinct primes in
(2^((ell-1)/2),2^(ell/2)). Its size is Omega(2^ell/ell^2), and both prime
factors eventually exceed ell^2. Thus every such N has the same untouched
base and the same free-choice law, and is neither even nor a perfect power.
For every f and L=2^(ell/2),

    Pr_(N uniform E_ell)(|e_5(N,f)|<=L)=O(ell^2*2^(-ell/2)).

Average over any such N-independent law of f (it need not be uniform).
Interchanging the nonnegative expectations gives

    average_(N in E_ell) E_f[T_literal(N,f)]
      >= c L [1-O(ell^2*2^(-ell/2))] = Omega(2^(ell/2)).

This rejects a single uniform all-input expected-polynomial work bound for
the specified sampler that materializes u,v on each attempt. For each large
ell at least one ensemble member has at least that average expected work.
It does not prove that every input does, that any residual is nonsmooth, or
that an N-adaptive law cannot put its mass on short representatives. Early
rejection before materialization changes the sampler and requires a new yield
analysis. The factor ensemble is a proof denominator, not information passed
to the algorithm. The centered tie, repeated free choices and shared random
tapes do not invalidate this bound.

**B4. Modular identity, width and CRT law — ACCEPT, with exact valuation repair.**

Every selected prime is a unit modulo M=N2^h. Thus g is a unit and g-N is
divisible by 2^h; subtracting multiples of M preserves divisibility. Consequently
0<=w_0<N is integral, 2^h w_0=g modN and gcd(w_0,N)=1. In particular w_0!=0.
Although the solved exponent can have exponential magnitude, its binary width
is O(h), so its modular power requires O(h) modular multiplications. Free
products plus the two correction powers have the claimed polynomial scalar
work, paid base/log setup and batch-sorted access. Sparse records retain the
large signed exponent in O(h) bits. H016 applies to the O(ell)-bit cofactor;
the extra exponent payload must also satisfy its stated width premise.

At lines 315–316, write **v_2(2^h w_0)=h+v_2(w_0)**. h is a forced contribution,
not necessarily the exact valuation. w_0 is a unit modulo odd N, which does
not force w_0 odd. Section 6 already gives the correct vector e-v(2^h w_i),
so this is a clarification of the prose, not a change to that formula.

CRT fixes the component modulo 2^h to the odd unit N, while the component
modulo N ranges freely over G. The fiber has phi(N) elements and density
1/phi(2^h)=1/(2D) among units modulo M. Its map to w_0 is reduction modulo N
followed by multiplication by the unit 2^-h, a bijection to G. Thus B7 is
exact for a UNIFORM fiber law and is independent of h at fixed N,B.
Uniform-unit rejection would require 2D trials on average for this condition;
coordinate solving bypasses rejection without proving fiber uniformity.
Neither support cardinality nor this bijection bounds smoothness under the
actual solved-exponent law.

## 5. Construction C

**C1. Eligibility, CRT roots and nearest lifts — ACCEPT.**

For an eligible odd p, Euler's criterion gives r_p^2=N modp with
r_p=N^((p+1)/4). Reduction and powering have the stated conservative
O(ell^2+log^3 p) cost. Small divisors are handled first, and the prime/root
list is generated from N, not supplied as advice. The greedy rule and fallback
A=1 make no eligible-prime supply claim. With K a nonnegative integer and
A_max>=1, A is odd, squarefree and A(2K+1)<=sqrt(N).

The c_i have disjoint CRT support, so all 2^nu sign patterns give different
roots. Gray-code enumeration costs R*poly(ell) after O(nu*ell^3) setup;
nu, the bit widths of A and sign identifiers are O(ell). For A=1 the empty
pattern gives its single root. A sign change updates the sum by ±2c_i.
No actual uniform-spacing hypothesis enters the construction.

For a root represented in [0,A), x_- in line 396 is the largest such lift
at most isqrt(N). Hence x_-<=sqrt(N)<x_-+A unless there is an exact square
endpoint, already covered by preprocessing. Nonnegative endpoints make
4N versus (2x_-+A)^2 an exact midpoint comparison. Because A is odd, an exact
midpoint tie would require 4N to be an odd square and cannot occur. The
nearest lift satisfies |x_0-sqrt(N)|<=A/2. C1 follows by integer expansion
and x_0^2=N modA; no real precision assumption is hidden.

**C2. Norm bound, distinctness, density and output cost — ACCEPT.**

Set H=K+1/2 and delta=x_j-sqrt(N). Then |delta|<=AH<=sqrt(N)/2 and

    |Q| = |2sqrt(N)delta+delta^2|/A
         <= 2sqrt(N)H+A H^2 <= (5/2)sqrt(N)H.

Also sqrt(N)/2<=x_j<=3sqrt(N)/2, so every x_j is positive. Under A_max>=1,
K is at most order sqrt(N); x_j^2-N, Q and the coefficients have O(ell) bits.
This remains true for the allowed larger public parameters on this branch.

One progression has spacing A and at most floor(J/A)+1 points in an interval
of length J. Summing over R distinct classes gives the stated R(J/A+1)
bound and exact density R/A per period. Distinct (root,j) pairs give distinct
positive integers x_j. Since x^2 is strictly increasing there, their signed
Q values are distinct for fixed A. Across different A, repeated x produces
the same fully factored x^2-N relation; repartitioning its factors does not
create new arithmetic data. Opposite signed Q can still share absolute values
and parity coincidences; the report does not exclude that.

Setup B*poly(ell+log B), sequential CRT generation, and full H016 processing
of U=R(2K+1) scalars prove C3. Appending the nu known factors of A costs
polynomial bits per record, adding 1 to v_p(|Q|) when p divides A and retaining
the sign of Q. No sieve-root table is rebuilt for every branch;
that alternative really would introduce R*k work. A full batch uses
U*poly(ell) bits besides the base and processing scratch; smaller batches
must pay every repeated setup. R=N^o(1) does not imply polynomial time in
ell or even an L_N[1/2,O(1)] bound for enumerating all roots. No useful output
count is proved for any early prefix or for the full set.

**C3. Closest-root join — ACCEPT with the following access-proof completion.**

Lines 466–477 correctly identify the candidates, but a sorted array by itself
does not establish cheap predecessor access on a sequential bit machine.
Add the following on-paper realization, which preserves the bound C4.
This is a reviewer-supplied completion of the cost proof, not an implemented
primitive or a new relation-yield claim.

Let s=isqrt(N), theta=sqrt(N)-s in [0,1), and form both half-sign lists with
residues a,b in [0,A) and their sign tags. For every first-half residue a,
its query point is

    (sqrt(N)-a) mod A = q_a+theta,  q_a=(s-a) mod A.

Sort the second list by b and the first list's tagged queries by q_a.
All queries share theta, so sorting their integer parts sorts the exact real
queries. A sequential merge finds the predecessor and successor among the
integer b's. For nonsquare N these are b<=q_a and b>q_a; for theta=0 include
an exact hit. Include the first/last entries for circular wrap-around.
Retain at most two tagged pairs per query, reconstruct their root classes
and nearest positive lifts, then choose the closest lift.

Two candidates on one side of sqrt(N) compare by their integer order. For
candidates x<=sqrt(N)<=y, compare 4N with (x+y)^2. All operands have O(ell)
bits. Merge sorting lists of lengths 2^floor(nu/2) and 2^ceil(nu/2) costs
2^ceil(nu/2)*poly(ell) bit work and storage including tags, comparisons and
memory movement. Thus C4 needs no binary search with unpaid tape access.
It selects one best root, not many useful relations. Its cost remains
additional to other generation and processing costs.

**C4. Close-window implication and phase model — ACCEPT; repair “no supply.”**

In the positive range, x+sqrt(N)>=3sqrt(N)/2, which proves C5. For a fixed
root set and independent continuous uniform phase, R arcs of radius D_0
have total covered fraction at most min(1,2R D_0/A). With
D_0=2AW/(3sqrt(N)), this is at most min(1,4RW/(3sqrt(N))).
Distinct primes give A>=nu!; log A=O(log N) and the elementary factorial
lower bound imply nu=O(log N/log log N), hence R=N^o(1). Thus for W=N^o(1)
the model probability is at most N^(-1/2+o(1)), even allowing every root.

Replace line 490's “gives no supply” by that quantitative probability bound,
or “does not give inverse-polynomial success per independent target phase.”
Small probability is not zero probability. Actual A, roots and target all
depend on N, so the model proves neither absence of close roots nor a
random-input theorem for the specified construction. C2 is an upper bound;
it is not a pointwise lower bound or an impossibility proof for a targeted
selector. No empirical sample is needed to recognize this distinction.

## 6. Full relation pipeline

**P1. Features, valuations, signs and storage — ACCEPT with literal-B label repair.**

The k prime features plus sign give an (k+1)-by-r matrix of relation columns.
Unused sign or prime features can remain zero. In A,C, |z_i|=O(N) up to an
absolute factor on C's stated branch, so each exponent is O(ell), each needs
O(log ell) bits, and at most O(ell) valuations are nonzero. The retained roots
need O(ell) bits. For compressed B, signed exponents have width
O(h+log(t+ell+2)); with the concrete t=ell^3 this agrees with the report's
O(h+log(t+2)). Its sparse support is O(t+ell), or k if smaller. Tags and prime
indices contribute their full log r and log k widths. Dense parity storage
alone is not full relation storage.

At lines 509–513 explicitly say **“For compressed B (B5–B6)”**. That variant
has v_2 contribution -(h+v_2(w_i)) and odd coordinates e(i,p)-v_p(w_i).
The modular identity then gives product_p p^Z_p=1 after multiplying selected
relations. If all Z_p are even, the displayed positive/negative halves yield
X^2=Y^2. Negative exponents are legitimate because every base prime is a unit.
Here w_i>0, so its sign feature is zero.

Do not transfer that signed-e formula to the literal residual of B4. If that
rejected branch were retained, writing z=(u-Nv)/2^h gives u=2^h z modN;
its left valuations are max(e_p,0), not e_p. Equivalently one could retain
u/v=2^h z/v modN and record the denominator on the right. Factoring signed z
requires its sign and h+v_2(|z|). Omitting v while using signed e would be a
wrong relation. This is a boundary clarification: B5's existing formula is
correct and the report does not supply an accepted literal pipeline.

**P2. Kernel, reconstruction and cost — ACCEPT.**

r>k+1 ensures a nonzero kernel vector without a rank assumption. Conservative
dense elimination can be realized in O((k+1+r)^3) bit work and quadratic
parity/dependency storage. Sparse m^2*poly(ell) work is explicitly a granted
solver for polynomial column sparsity and r=O(m*poly(ell)); it is not a theorem
about an arbitrary unqualified implementation in this report.

For A,C the parity kernel makes the signed product of z_i a positive square
integer; multiplying retained roots and using half valuations gives a square
congruence. For B5 the preceding multiplicative-one identity proves the
positive/negative formula directly; no unavailable square root is assumed.
Exponent sums have O(h+log(r(t+ell)+2)) bits, validating the conservative
modular-power cost with the paid reduced prime list. Summation, root products,
record access, failed dependencies and gcd work remain additional as stated.
A gcd equal to 1 or N is a failed split, not success.

**P3. Proper-root condition, duplicates and restarts — ACCEPT.**

Condition on the full retained right sides and selected dependency so the
other reconstructed root Y is determined. If one included root is uniform
on its entire fiber and conditionally independent of the other included
roots, multiplication by their product bijects its fiber to the fiber of
Y^2. For odd N=product_i p_i^a_i there are exactly two roots of 1 modulo
each prime power, hence 2^d roots in G. Only the two global sign patterns
X=±Y are trivial; every other pattern gives a proper gcd. The stated
probability 1-2^(1-d) follows for d>=2, including prime-power multiplicities.
No analogous favorable distribution has been proved for A, B or C.

A uniform square residue does not imply a uniform chosen root; a deterministic
section of the squaring map is a symbolic counterexample to that implication.
Repeated parity can be useful when the actual roots differ appropriately.
Two identical full records only supply the square of the same equality and
need not supply missing entropy. Costs and failure outcomes still count.

For fresh independent identically distributed epochs with expected cost C_N
and success probability s_N>0, renewal gives E[T]=C_N+(1-s_N)E[T], hence
C_N/s_N. Correlation between cost and success within an epoch is allowed;
independence of future epochs is the requirement. An adaptive strategy needs
its own valid law. Recursive factoring needs a theorem covering every
remaining nonprime input, not just balanced or Blum semiprimes.

## 7. Ordinary-smoothness models — ACCEPT conditionally; REJECT stronger readings

Put t=log N. The model with fixed beta>0 and B=L_N[1/2,b] has
u=log(N^beta)/log B=(beta/b+o(1))*sqrt(t/log t), whence
u log u=(beta/(2b)+o(1))*sqrt(t log t). Granting the specified smoothness
probability, distinct supply, collection/valuation cost, sparse algebra and
productive splitting gives the collection constant b+beta/(2b), setup b and
algebra 2b. Their maximum is M1. AM–GM makes the first term at least
sqrt(2beta), attained at b=sqrt(beta/2), where 2b has the same value.
This is an exact optimization of the declared model.

Under its additional distributional premises, beta=1 gives sqrt(2) for the
random-residue interpretation of A or uniformly compressed B, and beta=1/2
gives 1 for the quadratic-scale interpretation of C. These values are not
actual runtime bounds or lower bounds for the stated samplers. In particular,
C2 alone establishes |Q|<=N^(1/2+o(1)) when K=N^o(1), not an actual cofactor
law of size N^(1/2+o(1)), nor smoothness at that rate. Write line 596 as:

> If C's actual cofactor law is additionally modeled at the quadratic
> envelope beta=1/2 and the stated cost/yield premises hold, M1 gives c=1.

Full enumeration U or the optional join can exceed these modeled costs;
adequate useful prefix population is not supplied. Sparse reconstruction
usually costs k*poly(ell), which is absorbed in the granted model, not just
poly(ell) independent of the number of base entries. The text's “polynomial
reconstruction overhead” should be read and labeled accordingly.

With B=L_N[1/3,b] and fixed N^beta scale,

    u=(beta/b+o(1))*t^(2/3)/(log t)^(2/3),
    u log u=(2beta/(3b)+o(1))*t^(2/3)*(log t)^(1/3).

This verifies lines 605–606. The resulting L_N[2/3,*] term exceeds any fixed
L_N[1/3,c] term within that model. A cofactor log of order
t^(2/3)(log t)^(1/3), or a justified nonuniform smoothness advantage, changes
the model. The calculation does not lower-bound all algorithms using fixed
power-saving norms, and an upper norm envelope cannot establish such a bound.
Lack of a yield theorem is a reason not to promote a candidate; it is not
proof that the actual sampler never has favorable arithmetic behavior.

## 8. Changed next question — ACCEPT formulation only

For distinct p,q=3 mod4 and rho=XY^-1 with rho^2=1 modN, the local signs
are ±1. Since (-1/p)=(-1/q)=-1, Jacobi(rho,N)=-1 exactly when the signs
differ. Then gcd(rho-1,N), or equivalently gcd(X-Y,N), is a proper factor.
Thus E1 is sufficient. It requires units and a lower bound for every claimed
input over the complete pipeline's actual randomness, including selection
and failures, with fixed c and uniform cost constants. It must not become
a probability conditional on an uncharged rare success event.

A poly(ell) factor in expected work or repetition would preserve an existing
L_N[1/3,c_0] constant if the necessary pipeline law were proved. That is a
conditional implication only. The scope would initially be the stated Blum
semiprime family; no all-input theorem or heuristic-constant improvement
would follow automatically. For a unit a, (aX)(aY)^-1=XY^-1 exactly, so a
common mask cannot change the tested sign event.

No RNFS modification, new entropy argument or further child task is supplied
by this review. The next question belongs to later coordinator selection.

## 9. Primary-source checks and immutable hashes

The five original H027 works were independently downloaded again. Each matches
the submitted archived original byte-for-byte. URLs, byte counts, fresh paths,
and results are in [H027-review-primary-retrieval.json](H027-review-primary-retrieval.json).
Their original-byte SHA256 identities are:

- Dixon 1981 PDF: `c586a9b9bd18220098a11c7f9e8de660c2ad59fdac6f2297160c199bd56d14d2`.
- Pomerance 2008 PDF: `668721211aff4254066a2c430048686c677636bb485a5700f9b1e98faf1e396c`.
- Coppersmith 1993 PDF: `7a389dd62283670a5a4500df0f4baf2d2657250bc5fcce21c356b551dceb26a4`.
- Bernstein 2004 PDF: `2ef7aa60f8133ec1125bac4a39498285b626c0f553571fb00385822377facda7`.
- Lee–Venkatesan v1 HTML: `b2acc5a705aa386f5208ea8110fdd131958c7bed468db6776276938a459fd34d`.

**Dixon — ACCEPT attribution.** The original pp. 256–260, including visually
inspected pp. 257 and 259, separate collection from root-fiber randomness.
The theorem on p. 257 states the operation bound with coefficient 3sqrt(2)
in sqrt(log n log log n), not H027's heuristic sqrt(2). Its operation model
is described on p. 256; polynomial bit simulation does not alter that leading
L constant. Lemma 3 conditions on square-residue lists to control failed
dependencies. H027 correctly avoids attributing M1 to that rigorous theorem.
[Primary original](https://pages.cs.wisc.edu/~cs812-1/dixon.pdf).

**Pomerance — ACCEPT prior-art and heuristic scope.** Inspected quadratic
sieving, the explicit structured-value smoothness assumption, pp. 77–79's
optimization and sparse-algebra discussion, and p. 80's multiple-polynomial
attribution. These support H027's QS/MPQS-family classification and conditional
L_N[1/2,1] comparison. They do not certify a new algorithm or the exact
restricted eligible-prime selector as a novel construction. Silverman's 403
remains a disclosed unavailable source; no conclusion depends on its formulas.
[Primary author account](https://math.dartmouth.edu/~carlp/PDF/qs08.pdf).

**Coppersmith — ACCEPT constants and charging.** Sections 1–4, including
visually inspected printed p. 177, distinguish
uniform smooth-number estimates from their heuristic use on generated values,
charge enlarged field-specific columns and square roots, and give the cold
multiple-polynomial constant ((92+26sqrt(13))/27)^(1/3). The roughly 1.639
factory constant excludes massive shared precomputation from each individual
factorization. H027 compares against the correct cold baseline.
[Primary original](https://link.springer.com/content/pdf/10.1007/BF00198464.pdf).

**Bernstein — ACCEPT limited attribution.** Inspected introduction, Algorithm
2.1 and Theorems 2.2–2.3. The original distinguishes the largest smooth divisor
from labeled small factors. Its saturation cutoff is 2^(2^e)>=x, confirmed
visually on p. 3; replacing it by 2^e>=x is a transcription error. H027 relies
on H016's separately accepted full-valuation construction, not on silently
upgrading smooth-part extraction to labeled exponents. The original's stated
memory model does not independently prove tape-access costs; H016 provides
the additional sequential routing/accounting used here.
[Primary original](https://cr.yp.to/factorization/smoothparts-20040510.pdf).

**Lee–Venkatesan — ACCEPT attribution, no unconditional factoring promotion.**
Checked actual Theorems 2.1 and 2.3, Remark 4.31 and section 7. Theorem 2.1
produces a square congruence in expected L_N[1/3,(64/9)^(1/3)]. Theorem 2.3
adds fruitful output for the Blum-semiprime scope conditional on Conjecture
7.82. Remark 4.31 gives Coppersmith's improved constant for congruences.
Section 7 uses the Jacobi character of the rational/algebraic root images,
its independence from imposed characters, and kernel selection; E1 matches
that interface. In the proof of Theorem 2.3, the displayed nontriviality test omits
the global minus alternative and the next sentence says chi_P!=-1 where
fruitfulness requires chi_P=-1. These apparent transcription/editorial slips
do not alter H027's independently checked four-root criterion in section 8. This is a check of the paper's statements, not a proof audit
of RNFS or a supplied new sampler.
[Primary original](https://arxiv.org/html/1805.08873v1).

Two baseline originals were additionally archived in
[H027-review-baseline-retrieval.json](H027-review-baseline-retrieval.json):

- Lenstra–Pomerance 1992, SHA256 `ebf5d89ed9c89f0e4c51abbc2b49be8e52d2c9326dc8d2b347f533ceaef51e14`.
  The visually inspected theorem on printed p. 483 explicitly gives complete
  prime factorization for any positive integer in expected L_N[1/2,1].
  [Primary original](https://math.dartmouth.edu/~carlp/PDF/paper85.pdf).
- Harvey–Hittmeir 2021 v1, SHA256 `ae7e7ebc34e4295f971c91cc8276aab785fc60fbc05e24291e79d60c3ed8575e`.
  Theorem 1.1 and its preceding model definition give the recorded
  O(N^(1/5) log^(16/5)N/(log log N)^(3/5)) complete deterministic bit bound.
  [Primary original](https://arxiv.org/html/2105.11105v1).

H026's Rosser–Schoenfeld original was preserved, SHA256
`8e37b06f82e09421bceb2502578c47b61469141f0287e6acedb70e01765ab556`.
I visually checked printed p. 69: pi(x)>x/log x for x>=17 and
pi(x)<1.25506*x/log x for x>1. They support the accepted ensemble denominator;
no new unproved prime-distribution premise was inserted.
[Primary original](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf).

Rendered inspected pages and all review artifacts are hashed in
[H027-review-artifacts.sha256](H027-review-artifacts.sha256). Text extractions
are derivatives; the preserved PDF/HTML bytes are the source of record.

## 10. Precise requested repairs and disposition

The coordinator can retain the submitted bytes and adopt these local repairs:

1. In section 4 state B=ell^2 together with h=ell,t=ell^3 and fix the centered
   tie, for example e_5 in [-D/2,D/2). Label rejection-based generation bounds
   as expected time unless an explicit failure cap is introduced.
2. Replace “known valuation h” by “known contribution h, total valuation
   h+v_2(w_0).” In section 6 label the signed-e construction as compressed B;
   the literal residual uses the numerator valuations or an explicit denominator.
3. Add section 5's offline query-sort/merge realization (section 5, C3 of this
   review), or state a paid indexed-access model for C4. The sequential
   realization validates the advertised exponent without that assumption.
4. Replace “no supply” in the independent-phase model by the explicit
   N^(-1/2+o(1)) probability upper bound. Keep the actual N-dependent target
   outside that model's conclusion.
5. At lines 355–356 use: “The literal implementation is not uniformly
   expected-polynomial in the stated output model. Modular compression
   preserves the cofactor range N; its actual smoothness advantage remains
   unproved.” Range alone does not disprove a favorable nonuniform law.
6. At line 596 use the explicitly conditional C wording in section 7 above.
   Label reconstruction overhead as polynomial per base/record size; retain
   its k*poly(ell) work within the complete modeled envelope.

No displayed algebraic identity or asymptotic model minimum needs changing.
The auxiliary sequential join proof and the literal/modular distinction above
are reviewer completions, not new accepted factoring mechanisms. Stronger
readings that turn support size, norm upper bounds, an artificial phase model,
or a missing yield theorem into general impossibility are **REJECTED**.
The report's repeated explicit cautions already exclude those readings;
the requested wording removes the remaining local ambiguity.

Accept the narrowly stated negative literal-sampler result and the valid
conditioning/generation primitives after those clarifications. Retain “no
implementation or experiment” as the research selection decision. Do not
accept any new full factoring theorem, actual useful-yield guarantee, or
solution to E1. No finite experiment is needed to complete this review.
