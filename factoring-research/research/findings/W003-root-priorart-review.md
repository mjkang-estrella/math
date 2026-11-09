# W003 Lens B — independent review, first round

2026-10-08. **Review recommendations only; every new deduction and completion
below remains UNACCEPTED until coordinator disposition.**
Verified COMPLETE classical factoring complexity improvement: **NONE**.

The integer construction survives this review at its conservative Dixon bound,
with the explicit parameter procedure, stopped-tape proof, sequential schedule,
and composition given below. Its complete expected bit-time upper bound is
L_N[1/2,3sqrt(2)], with working space L_N[1/2,2sqrt(2)]. These are upper
envelopes, not matching lower bounds or measured runtimes. They do not improve
the existing rigorous Lenstra–Pomerance L_N[1/2,1] complete-factorization bound.

Two field-section statements require correction. A localization failure is not
a proof that the abstract target is absent. Also, rational norms can distinguish
the two extension-square classes when Norm(alpha) is nonsquare in Q. Neither
correction supplies a fast target generator or an NFS-scale success theorem.

## 1. Exact scope, evidence, and recommended disposition

This is a NEW independent review of all 572 submitted lines, not a constructor
continuation. There were no author responses or previous review rounds. The
coordinator intake supplies the eight verification obligations. I did not read
Lens A's report, its submitted snapshot, or the other review's draft. The
governing STATE and W001 synthesis mention its reported sign obstruction;
that shared observation is not an independent audit or acceptance of Lens A.

The original brief is preserved byte-for-byte at
[frozen W003](W003-root-review-evidence/frozen/research/hypotheses/W003.md),
SHA-256 `fc8f5cf42a34b020833832a56994421c183e22a8fd2e951a6cb9c6cee14ab629`.
The submitted report and submitted snapshot are identical, SHA-256
`2053748929ba399bf4e010fc0133ce12cd60d4c568745a44b06ae7a6c788f275`.
The [input inventory](W003-root-review-evidence/input-inventory.json) seals
76 initial review snapshots, including the complete original delivery and
its source/access ledger. All 19 original input entries, 23 source identities,
and 54 original delivery entries independently verify. The
[assignment](W003-root-review-evidence/review-assignment.txt),
[coverage record](W003-root-review-evidence/line-coverage.json),
[source inspection record](W003-root-review-evidence/source-inspection.json),
and [separate delivery manifest](W003-root-review-delivery.sha256) belong only
to this review. Hashes establish identity, not mathematical correctness.
The [validation record](W003-root-review-evidence/validation.json) records
the unchanged protected originals and complete line coverage. Shared STATE
and W001 synthesis changed during parent-owned work; their initial snapshots
and later governing versions are both preserved. This reviewer edited neither.

I read AGENTS.md, README.md, SPECIFICATION, RESEARCH_LOOP, RESEARCH_TEAM, current
STATE and W001 synthesis; W002 B/C dispositions (also A's); H027's corrected
root-fiber section and disposition/prior-art note; H028/H031 dispositions;
and the original dependency passages actually used. Current dispositions
govern historical provisional labels. Parent ownership of acceptance and
shared records is unchanged. No delegation, experiment, numerical example
search, solver implementation, Lean work, package installation, outside-project
write, commit, publication, or scheduler action occurred. Evidence copying,
hashing, document writing, primary-source inspection and PDF extraction/rendering
were the machine work. No code change calls for the shared test suite.

Recommended scoped disposition, subject to the coordinator:

- **Retain after completion:** the exact outer root law, stopped integer twist
  coupling, finite Dixon-scale trial and its complete factoring/ROOT-only
  compositions; sections 2–7 supply their full arguments.
- **Retain after qualification:** the field-square search and localized recovery;
  distinguish abstract membership from this implementation's recoverability.
- **Retain:** the relative-norm necessity, negative-real-place obstruction,
  square-alpha case and quadratic-extension square classification.
- **Correct:** the blanket rational-norm loss-of-bit wording, the domain of the
  small-R cutoff, and the conflation of the two fallback decision predicates.
- **Reject promotion:** no L_N[1/3] target supply/completion theorem, no improved
  complete factoring cost, and no impossibility theorem about all constructions.

## 2. Outer reduction: multiplicities, conditioning, and raw words

Use n=bit_length(N), natural logarithms in L notation, and independent fair
random bits. Paid deterministic primality testing, removal of powers of 2,
and perfect-power recognition leave odd composites with at least two distinct
prime divisors. Perfect powers are recognized by integer root searches for
2<=e<=n, with exact powering checks, in polynomial bit work. Factoring the
smaller base and restoring multiplicities is charged later. The proof-only
decomposition N=product p_i^{e_i} is never an algorithm input.

Let G=(Z/NZ)^*, Q=G^2, and k be the number of distinct odd primes. If u^2=1
modulo p_i^{e_i}, then p_i^{e_i} divides (u-1)(u+1). Their gcd divides 2,
so the entire prime power divides exactly one factor. Thus u=+1 or -1 on
that component. The kernel of squaring on G has 2^k elements by CRT; every
fiber over Q is a coset of that kernel. This handles arbitrary positive
multiplicities, without assuming squarefreeness.

An n-bit raw word x has probability 2^(-n) at every value. Among 0<=x<N,
there are phi(N) units, one full-gcd word (zero), and N-phi(N)-1 proper-gcd
words. The other 2^n-N words are rejected. On the unit branch x is uniform
on G, R=x^2 is uniform on Q, and x conditional on R is uniform on its fiber.

For fixed R, an inner transcript is a function of N,R and an independent
tape. A pathwise finite time bound also bounds the number of bits read, so
unused bits can be padded. Conditioning on any transcript with a verified
root y leaves every outer preimage equally likely: the likelihood of that
transcript is identical for every x in the same fiber. A root of a unit is
itself a unit. Exactly x=y and x=-y have globally equal signs. In every other
case gcd(x-y,N) contains a nonempty proper subset of the whole prime-power
components. Hence

    rho_k = Pr(proper split | verified inner ROOT, unit branch)
          = 1 - 2^(1-k).                                      (R1)

There is no assumption that y is uniform, that success is independent of R,
or that the different p_i have exponent one. For k=1 the mismatch probability
is zero. Prime powers must be handled separately. No even-modulus conclusion
is drawn from this formula. Fresh outer trials prevent root-dependent feedback
from restricting a later call's residual fiber.

Let a_R and s_R be the probabilities of the disjoint terminal outcomes
verified FACTOR and verified ROOT in one inner trial. All invalid outputs,
timeouts, full gcds and ordinary failures receive zero credit. Then the
submitted raw-word identity is exactly

    p_N = [N-phi(N)-1 + phi(N) E_Q(a_R + rho_k s_R)] / 2^n.     (R2)

An inner factor need not be obtained by a root mismatch and need not contain
whole prime-power components. The whole-component assertion belongs only to
gcd(x-y,N) on the verified unit-root branch. Every factor is checked by
1<d<N and d|N before being returned.

For iid cold trials let C_i be trial i's full bit cost, p their common success
probability, and J the first successful index. The event J>=i depends on
earlier trials and is independent of C_i. Tonelli's theorem gives

    E sum_{i=1}^J C_i = sum_{i>=1}(1-p)^(i-1) E C_i = C_N/p.

This requires p>0 and finite C_N, not independence between a trial's own
cost and success. If p=0, there is no such successful-work conclusion.
For a cap C, j attempts cost at most jC and fail with probability (1-p)^j.
Reading bits, preprocessing, retries, squaring, verification, gcds, and all
rejected words belong to C_N. A restart can discard the previous workspace;
an unbounded restart counter is not needed.

## 3. A finite certified construction of B

Submission line 246's certified rounding is underspecified as a program.
The following completion needs no exact-real oracle, integer-boundary decision,
unknown analytic threshold, or computed factor of N.

For N>=3 define w=sqrt(2 log N log log N) and v=exp(w). Use rational interval
arithmetic with outward rounding to obtain an enclosure [l,u] of v satisfying

    l>1,    u-l < min(1/4, (l-1)/2).

Return the integer B=ceil(u). Then v<=B and

    B <= u+1 < v + (l-1)/2 + 1 <= (3v+1)/2 < 2v.

This remains valid when v or u happens to be an integer. The algorithm never
has to determine whether v is an integer. To implement the enclosure by one
finite rational procedure:

1. Range-reduce a positive rational t as 2^j z with 1<=z<2. Compute log 2
   and log z with
   log z=2 sum_{i>=0} q^(2i+1)/(2i+1), q=(z-1)/(z+1), |q|<=1/3.
   After J terms the absolute tail is at most
   2|q|^(2J+1)/((2J+1)(1-q^2)). Evaluate both endpoints when the input is
   an interval; monotonicity supplies enclosing output endpoints.
2. Obtain log N, then log(log N), their product, and its positive square root.
   Rational bisection with squared comparisons encloses the last operation.
   Because N>=3, log N>1, so this nested logarithm stays away from its pole.
3. To exponentiate an enclosure of w, divide by a power 2^s making its upper
   endpoint at most 1. Use the rational exponential series; on [0,1] the
   tail after degree J is at most 3/(J+1)!. Square the enclosing interval
   s times, rounding outward to dyadics. Increase precision until the displayed
   rational stopping test holds.

Here log v=O(n), and v(N)>=v(3)>1 is bounded away from 1. Absolute error in
v bounded by a fixed sufficiently small constant therefore suffices uniformly.
O(n) fractional precision, with O(log n) guard bits for the polynomial number
of operations, suffices after range reduction. There are polynomially many
series terms, bisections and rational-bit operations; retaining dyadic interval
endpoints keeps all intermediate widths polynomial in n. Even exact rational
partial sums have polynomial widths. Increasing precision geometrically gives
polynomial total construction time and space. No value of a smoothness
threshold appears in this executable parameter rule.

Enumerate every integer t=2,...,B; test divisors through floor(sqrt(t)) by
ordinary trial division. Append each prime and test gcd(t,N), returning any
verified proper divisor. This costs O(B^(3/2) poly(n)), including enumeration,
square-root bounds, divisions, writes and gcds. On the continuing composite
domain a prime with gcd N cannot occur: that would say N itself is prime.
Thus, if this branch continues, all base primes are units and every prime
factor of N exceeds B. No prime table is supplied. Let h=pi(B), a=h+1,
and T=16aB, an integer. Bounds log B=O(n) and h<=B will suffice for costs.

## 4. Whole stopped-experiment coupling and exact reconstruction

Fix a promised unit square R. Choose h_R^2=R in G for the proof only.
For each epsilon in {0,1}, define a permutation P_epsilon of the entire
n-bit word alphabet by

    P_epsilon(m) = the representative of h_R^epsilon m modulo N, m<N;
                   m,                                      m>=N.

Multiplication by a unit permutes 0,...,N-1 and preserves gcd with N;
the out-of-range part is fixed. This is a bijection, not just a marginal
distribution argument on accepted rows. Applying it independently to all
T records sends the uniform tape (m_t,epsilon_t) to a tape (z_t,epsilon_t)
in which the z_t are iid uniform raw words and the entire epsilon vector is
independent uniform on F_2^T.

For z_t<N the rejection/full-gcd/proper-gcd/unit decision is exactly the
same as for m_t. On units, the tested representative is

    v_t = R^epsilon_t m_t^2 mod N = z_t^2 mod N.

Call (z_1,...,z_T) the geometric tape. It determines all out-of-range flags,
gcd outcomes and possible early factors, all positive residue representatives,
smoothness flags, full exponents, retained indices and their order, and whether
the run reaches a retained rows before its first proper gcd or the cap. It
also determines the chosen nonzero parity dependency c, because elimination
is required to ignore m and epsilon. The actual algorithm computes none of
the z_t and never computes or reads h_R.

Conditional on any geometric tape that reaches elimination, the retained
epsilon labels remain independent fair bits, including after conditioning on
absence of an earlier factor. The retained index set is fixed by that tape.
As c is nonzero, c dot epsilon is a nonzero linear functional of fair bits:
its parity is odd with probability exactly 1/2. This also proves the assertion
conditioned only on a retained residue/exponent list by taking a mixture.
It would be false to condition additionally on the retained m values or the
epsilon values themselves. Submission lines 280–281 should refer to all
label-independent geometric decisions, rather than saying stopping inspects
only the retained list: early gcds inspect other records too.

For a fixed geometric dataset with kernel dimension kappa, restriction of a
uniform linear functional to that kernel is uniform on its dual. Its being
identically zero has probability 2^(-kappa). This justifies the submitted
1-2^(-kappa) claim only with that label-free meaning of fixed dataset. The
displayed algorithm needs one deterministic nonzero dependency, not a search
over all dependencies and not a square-class basis oracle.

For its selected rows, exact integer parity gives

    S^2 = product v_j^c_j = R^E M^2 modulo N,
    M = product m_j^c_j,    E = sum c_j epsilon_j.

All these residues are units. If E is odd, set t=(E-1)/2. Then

    (S M^(-1) R^(-t))^2 = R^(E-2t) = R modulo N.             (R3)

Thus the reconstruction is correct, including E=1 and repeated retained
residues. Full exponents, not just parities, are needed for S. Modular
exponentiation avoids constructing the integer product. Positive representatives
make a sign row unnecessary; a signed variant would have to include one.

## 5. Dixon supply, rounding slack, and stopped success

I inspected Dixon's Algorithm A_L, theorem and proof passages on printed
pp.256–260, including the images of pp.257–259. The needed statement concerns
uniform residues squared, not uniform integers tested for smoothness. It is
valid uniformly in the odd modulus after small prime factors have been excluded.
Increasing the smoothness bound from v to B preserves its supply, while the
small-prime test supplies the hypotheses for both cutoffs.

There is a rounding detail worth proving: substituting an integer ceiling for
the auxiliary r in the *weaker* bound (log N)^(-4r) alone does not immediately
give 1/v. The slack in Dixon's smooth-number counting argument repairs this.
Here is a complete short derivation of the needed quantitative transfer.

Put L=log N, ell=log L, w=sqrt(2L ell), r=ceil(L/(2w)), and
u=exp(L/(2r))<=v<=B. These are proof parameters, not runtime oracles. For
sufficiently large N, r>=3, r/ell tends to infinity, and u tends to infinity.
The elementary prime-count lower bound pi(u)>=u/(2 log u) used in Dixon's
proof applies. Let A be the number of positive u-smooth integers <=sqrt(N).
Products of at most r primes <=u give

    A >= binomial(pi(u)+r,r) >= pi(u)^r/r!
      >= [u/((r+1)log u)]^r
       = sqrt(N) [2r/((r+1)L)]^r
      >= sqrt(N) [(3/2)/L]^r.                                (R4)

The factorial bound r!<=((r+1)/2)^r follows from AM–GM. This avoids any
integer-rounding ambiguity in replacing u^r by sqrt(N).

For completeness, the square transfer is the key weighted count. All these
smooth integers are units. Partition them by their k quadratic characters
at the distinct odd prime divisors of N. Write S_chi=sum 1/tau(s) in each
part, S=sum S_chi, and S'=sum tau(s). Cauchy–Schwarz gives A^2<=SS' and
S^2<=2^k sum S_chi^2. Also S'<=sum_{s<=sqrt(N)}tau(s)<=sqrt(N)L for all
sufficiently large N. In sum S_chi^2, each ordered pair s,t has st<=N,
is u-smooth, and is a quadratic residue modulo every prime power. For a
fixed product z its weight is at most 1: tau(s)tau(t)>=tau(z), and there
are at most tau(z) ordered factor pairs. Therefore if H_u counts positive
u-smooth unit squares represented in [1,N-1],

    H_u >= sum S_chi^2,
    lambda_u = 2^k H_u/N >= A^4/(N^2 L^2).                   (R5)

No product counted here is N: N has no prime divisor <=u. Each such residue
has exactly 2^k roots, including repeated prime-power moduli. Combining R4–R5,

    log lambda_u >= 4r log(3/2) - (4r+2)ell
                 >= -w + 4r log(3/2) - 6ell >= -w

eventually, because r/ell tends to infinity. Thus the uniform-residue
admission probability at bound B is at least 1/v>=1/B. This is a proved
smooth-*square* transfer; it assumes no random-integer smoothness model and
uses no Dixon useful-dependency theorem for the new twist labels.

For a raw record the probability theta of a retained row is therefore at
least N/(2^n B)>1/(2B). On the hypothetical full geometric tape, the count
X of retainable rows is Binomial(T,theta); mu=T theta>=8a. Its variance is
at most mu. Chebyshev gives

    Pr(X<a) <= mu/(mu-a)^2 <= 8/(49a).                        (R6)

The last function decreases for mu>a, so substitution of 8a is valid.
This binomial assertion is unconditional; it is not asserted after conditioning
on no early factor or on a stopped list.

Let F be the geometric event that the actual run returns an early proper
factor, and C the disjoint event that it reaches a rows without such an earlier
factor. If X>=a then F or C occurs. Given C, odd parity has probability 1/2
by section 4. Reconstruction and verification then succeed. Consequently

    q_R = Pr(FACTOR or ROOT)
        = Pr(F) + (1/2)Pr(C)
        >= (1/2)Pr(X>=a)
        >= (1-8/(49a))/2 > 3/8.                              (R7)

This bound is uniform in every promised R for sufficiently large continuing
N. A successful preliminary prime screen only improves it.

Small continuing inputs have positive success without knowing any analytic
threshold. Indeed the event that the first a geometric words equal 1 has
probability 2^(-na); it has no gcd failures and supplies a smooth zero-parity
row at each step. The chosen nonzero c has odd labels on half its tapes, so
q_R>=2^(-na-1)>0. This is a symbolic tape event, not a generated example or
an experiment, and does not expose h_R to the algorithm. The same program
therefore has finite expected time on each small input. There are finitely
many inputs below the analytic threshold, so their constants can be absorbed
in an asymptotic envelope without making that threshold an algorithm input.

## 6. Complete sequential bit and storage schedule

Use a fixed finite number of sequential work tapes and schoolbook arithmetic.
No unit-cost table access is assumed. All indices, prime values, residues and
loop counters have O(n+log B)=O(n) bits; an individual valuation is <=n and
uses O(log(n+1)) bits. Below, polynomial factors have fixed degrees independent
of N, B, h, R, and the random tape.

1. **Preprocessing and base.** Section 3's rational parameter construction and
   elementary cases take poly(n); explicit prime enumeration and gcd inspection
   take O(B^(3/2)poly(n)). A sequential base tape uses O(h poly(n)) bits.
2. **Records.** Generate each n+1-bit record online. Pay its read, comparison,
   gcd and modular arithmetic even if it fails. On a unit scan the base once,
   repeatedly dividing the O(n)-bit positive representative by each prime.
   Store a temporary dense exponent row, including zeros; discard it if a
   residual cofactor remains. Prime-list rewinds cost O(h poly(n)) per attempt.
   Over T=16aB records, this is O(Ba(h+1)poly(n)). Stop early on a proper
   factor or on a retained rows; the unused random suffix is conceptual.
3. **Retained data.** Append successful rows in original order, with their
   full exponents, m, epsilon, residue and original slot number. There are
   a rows of h exponent entries. Keep labels/roots separate from the elimination
   tape so the pivot rule cannot inspect them. Actual copying is charged.
4. **Elimination.** Process the a parity rows in original order. Give row i
   provenance e_i of length a. Keep previous nonzero pivots on a tape sorted
   by increasing leading column. For each pivot, scan the current work row
   to its indicated column (or simply scan it entirely). If that bit is 1,
   xor the whole parity row and provenance with the pivot; if it is 0, still
   pay the traversal. Rewinds and temporary pivot copying cost O(a poly(n))
   per pivot. At most h pivots are inspected for each of a rows. A nonzero
   new row is inserted by sequentially copying the ordered pivot tape, costing
   O(a^2 poly(n)) for that row. A zero residual returns its provenance c.
   That c is nonzero: its newest coordinate i remains 1, whereas earlier
   pivots have zero there. Distinct leading columns give independent pivots,
   so by row a a zero residual must occur. Total work is O(a^3 poly(n));
   tapes occupy O(a^2 poly(n)). This is a concrete cubic schedule, not a
   cubic arithmetic count followed by an uncharged whole-matrix lookup.
5. **Reconstruction.** Merge c with original ordered rows. Accumulate E and M
   and maintain a sequential length-h vector of exponent sums, with one full
   accumulator scan per selected row. Each sum is <=an and has
   O(log(an+1)) bits. This is O(ah poly(n)) work. Scan primes and sums once
   to compute S with modular binary powers. Compute M^(-1), R^(-1), its
   required power, and verify R3. Every inverse has a unit gcd certificate;
   no full gcd receives success credit. This costs O(a^2 poly(n)) or less.

The cold cap is therefore

    C_trial <= [B^(3/2) + Ba(h+1) + a^3 + 1] poly(n)
             <= B^3 poly(n),
    S_trial <= B^2 poly(n),
    random bits <= (n+1)16(h+1)B.                             (R8)

Only a constant number of current matrix/pivot copies is needed. Empty
dependency prefixes and all control scans are covered by a=h+1. This schedule
finds one dependency; it does not repeatedly rescan the whole matrix for every
bit of every pivot. The exact odd/even test and all failed capped trials
remain paid. No sparse-solver hypothesis, fast field square root, or stored
full random tape enters the integer bound.

As log B=w+O(1), R7–R8 yield expected FACTOR-or-ROOT work at most
L_N[1/2,3sqrt(2)] and pathwise working space at most L_N[1/2,2sqrt(2)].
The total number of trials has no deterministic bound on every infinite tape;
each individual trial is finite and the restart program terminates almost
surely. Calling the former a finite trial must not turn the latter into a
worst-case deterministic factoring claim.

## 7. Complete factoring and a ROOT-only wrapper without circularity

On every unit outer branch, rho_k>=1/2 and a_R+rho_k s_R>=q_R/2. Combining
R2 and R7 gives, for sufficiently large continuing N,

    p_N >= [N-phi(N)-1 + (3/16)phi(N)]/2^n
        >= (3/16)(N-1)/2^n >= 3/32.                          (R9)

The last inequality uses that N is odd and N>=3. Thus small phi(N)/N
causes no success problem: proper nonunit words supply direct factors.
For the finite exceptional set, the positive-tape argument and R1 likewise
give p_N>0. There is a universal p_*>0 below all continuing p_N: choose the
minimum over that finite set and the large-input constant. This is an
existence bound used in the proof, not a constant needed by the program.

Define Split(N) using the paid elementary branches, then independent raw-word
trials with the finite FACTOR-or-ROOT inner routine until a proper factor is
verified. Define Factor(N) by verified recursive calls on d and N/d, with
primality checks at leaves and restoration of perfect-power multiplicities.
Even inputs are split by 2 before invoking the odd routine. There are at most
n prime leaves counted with multiplicity and O(n) nodes in a binary factor
tree. This remains true if an early gcd divides a prime-power component only
partly. Arithmetic at every node and the output factor list are paid.

The envelope is uniform: for 3<=M<=N, v(M)<=v(N), and our rounded B(M)<=2B(N).
Condition on the random path to any node and use its own expected split bound.
Summing over at most O(n) possible node slots gives expected complete work
L_N[1/2,3sqrt(2)]. Discard a node's relation workspace before descending;
store only the pending factors and multiplicities. The recursion stack and
output use poly(n) bits, so the same L_N[1/2,2sqrt(2)] working-space envelope
holds. This is an all-input extension, unlike a Blum-semiprime-only theorem.

For **ROOT-only** on the continuing odd domain and a promised unit square R,
repeat the inner finite routine until it returns ROOT or FACTOR. A ROOT is
already verified. A FACTOR d triggers Factor(d) and Factor(N/d), using the
just-defined Split, not ROOT-only again on the same modulus. Thus there is
no circular oracle. Consolidate the resulting prime powers. Extract a root
modulo each odd prime, lift it, and apply CRT. The initial input remains
only N,R and fresh randomness; internally obtained factors are fully paid.

The extra root work is polynomial expected bit work and polynomial space.
An explicit primary-source-compatible prime-root procedure is Rabin's degree-2
shift/gcd method: for f(X)=X^2-R in F_p[X], sample an n_p-bit word t, reject
t>=p, test gcd(f,X+t), and otherwise test
gcd(f,(X+t)^((p-1)/2)-1). All powers are reduced modulo f, so they use only
degree-1 residues. For the two distinct roots a,b, the fractional-linear map
(a+t)/(b+t) runs through F_p minus 1 when t ranges outside -b. Its nonsquare
values supply (p-1)/2 successful shifts; zero-root shifts are handled by the
first gcd. Thus a raw word succeeds with probability at least 1/8, a deliberately
loose absolute bound. A successful linear factor determines and verifies a root.
Each attempt uses poly(n) bits and work. No enumeration up to p is involved.

Given a^2=R mod p^j, solve

    2a t = (R-a^2)/p^j mod p,
    a_new = a + t p^j.

The division is exact and 2a is a unit. Summed over the factorization there
are at most n lifting digits. CRT of the pairwise coprime prime powers and
the final modular verification are polynomial. The known root algorithm is
randomized expected polynomial time, not a deterministic poly(n) nonresidue
search. The resulting ROOT-only expected bound remains the same conservative
L bound, with the same space envelope.

If a **strict finite tape** is required for this wrapper, make the following
explicit capped variant. Let n_0 be the bit length of its input N and allow
J=n_0^2 finite attempts at every unresolved composite node of Factor, and
J raw shift attempts at each prime-root call. Return FAIL if any cap exhausts.
At most n_0 splitter nodes and n_0 prime-root calls occur. Conditional on
each reached node, fresh trials fail with probability at most (1-p_*)^J;
the prime-root bound is at most (7/8)^J. A union bound bounds total failure by

    n_0 exp(-p_* n_0^2) + n_0 exp(-n_0^2/8) = o(1).          (R10)

One may simply run this capped Factor first, then extract the root; optional
early ROOT returns from the original inner routine can only save work. This
variant uses at most B(N)^3 poly(n_0) bit steps, B(N)^2 poly(n_0) space, and
B(N)^2 poly(n_0) fresh bits, including recursion and prime-root sampling.
Unused bits pad to a predetermined finite bound. Every finite exceptional
input still has a positive success tape. Repeating the capped wrapper therefore
has the stated expected L upper bound too. Neither an unknown threshold nor
p_* is consulted at runtime. The finite wrapper may now be substituted in
R1–R2 literally, instead of pretending an unbounded expected root routine
already has the original finite tape cap.

## 8. Actual square classes, exhaustive search, and localized recovery

Assume the two presented fields and modular maps have passed their stated
checks, alpha_i is nonzero, and every retained q_ij=a_j^2-b_j^2 alpha_i is
nonzero with the same verified unit image v_j. Let V=product v_j over the
selected subset. Multiplication modulo squares defines the homomorphism

    A: F_2^M -> K_1^*/K_1^*2 direct_sum K_2^*/K_2^*2,
    tau=([alpha_1],0).

The abstract mixed target exists exactly when tau belongs to im(A).
Rank-nullity describes ker(A) and gives no such membership theorem. Appending
tau as a column works only if the returned dependence uses that column.
Known ideal valuations test necessary conditions; even complete parity at
all maximal-order prime ideals can leave the ideal-class and unit obstructions.
Nonmaximal-order valuations can lose further information, and reducing an
actual field root can face an additional localization obstruction. These are
different stages, not equivalent square-class coordinates.

For each subset, Q_1/alpha_1 is square exactly when alpha_1 Q_1 is square:
the quotient of these elements is alpha_1^2. Thus factoring the two
polynomials T^2-alpha_1 Q_1 and T^2-Q_2 over the actual fields decides its
abstract target condition. Nonzero radicands make these squarefree quadratics
in characteristic zero. Linear factors supply roots; irreducible quadratics
certify nonsquareness. No search through an unbounded set of proposed roots
is needed. Empty subsets are included and are useful precisely in the
appropriate square-alpha case.

Here is the first substantive scope correction to submission lines 372–380.
Maintain an **abstract-hit flag** when both field square tests succeed, and
a separate **recoverable-hit flag** when the specified reduction checks also
succeed. Enumeration of all 2^M subsets decides the first predicate. The
algorithm that discards invalid reductions and reports only a recovered root
decides the second predicate. A full derivative gcd may stop this particular
localization even when tau is attainable in the fields. Such a run must not
report tau absent. If all the required derivative and leading-coefficient
images are units, the proof below makes every abstract hit recoverable, so
the two predicates then agree. This is a repair to the reference algorithm's
claimed decision scope, not a proof that its target is generally attainable.

For monic f_i of degrees at most d and coefficient heights at most H, multiplication
by a^2-b^2 alpha in the power basis increases the maximum coefficient by at
most a factor (A_0+1)^2(1+dH). Consequently an M-fold product and alpha Q have
coefficient bit lengths

    h_U = O((M+1)[1+log(d+1)+log(H+1)+log(A_0+1)]).

Sequentially multiplying these factors costs at most
(M+1)^3 poly(d,log(H+1),log(A_0+1)) bits with schoolbook arithmetic and
paid coefficient scans. One need not materialize a polynomial of degree Md.

Lenstra's Theorem 4.5 takes a monic polynomial of degree nu over a presented
field with monic defining F, degree d, coefficient maximum A and denominator
b. I checked the displayed operation and operand-width bounds, not just the
abstract:

    O(nu^6 d^6 + nu^5 d^6 log(d|F|) + nu^5 d^5 log(bA)) operations,
    O(nu^3 d^3 + nu^2 d^3 log(d|F|) + nu^2 d^2 log(bA)) operand bits.

Use positive 1+log conventions and |F|<=sqrt(d+1)H. With nu=2, both are
(h_U+1) times a fixed polynomial in the other input parameters. Ordinary
quadratic-cost integer arithmetic gives the stated cubic dependence on h_U.
The auxiliary prime in Algorithm 4.4 has *numerical size* polynomial in h_U
and the field parameters; it need not have numerical size poly(n) when M
is large. The source's prime construction, modular factorization, Hensel lift
and lattice reduction are part of the bound. It chooses an appropriate factor
of F modulo p, not an unprovided inert prime. Its denominator choice uses
the discriminant itself, avoiding integer factorization of that discriminant.

The polynomial/lattice arrays have polynomially many entries in d and nu;
sequential access to their long coefficients fits the schoolbook bound with
another polynomial in those parameters. Small-prime candidate searches can
be streamed. Rational root-output heights and denominator bits are polynomial
in h_U and the field parameters, as in the final factor-height estimate on
p.254. Exact root verification and denominator cancellation are paid too.
Thus a valid conservative exhaustive-search envelope is

    2^M (M+1)^3 poly(d,log(H+1),log(A_0+1),n),                 (R11)

with polynomial working space in those numerical parameters, streaming subset
indices and reusing workspace. Irreducibility/factorization of the defining
polynomials and coefficient reading add polynomial setup. This bound does
not assert a polynomial in n when M has subexponential size: its 2^M factor
is far beyond an L_N[1/3] cost. No matrix of unpaid complete square classes
is being substituted for the exhaustive search.

For the monic recovery, let delta=f'(alpha) and D=f'(R) modulo N.
The order multiplier has a direct proof. If w is integral, consider

    H(T)=Tr_{K/Q}( w f(T)/(T-alpha) ).

The quotient f(T)/(T-alpha) has coefficients in Z[alpha]. Their products
with w are integral, hence have integral traces; H lies in Z[T] with degree
less than d. Writing the trace as a sum over embeddings and evaluating at
alpha leaves only the identity embedding's term. Thus H(alpha)=f'(alpha)w.
This proves delta O_K subset Z[alpha], without computing a maximal order,
factoring a discriminant, or assuming a map from the whole field.

For an abstract hit set w_1^2=alpha_1 Q_1 and w_2^2=Q_2. The radicands are
integral, so each w_i is integral by transitivity of integrality. The original
z_1 need not be integral; using w_1=alpha_1 z_1 is the correct repair already
present in the submission. Compute H_i=delta_i w_i exactly and cancel its
rational power-basis denominators before modular evaluation. Verify that
the remaining coefficients are integers and that
H_i^2=delta_i^2 w_i^2 in the field.

If gcd(D_i,N) is proper, output a verified factor. If it is N, report failure
of this localization; there is no automatic proper split. If it is 1, the
order map extends uniquely to Z[alpha_i,delta_i^(-1)], and

    u_i = H_i(R) D_i^(-1) mod N,
    u_1^2 = R V,    u_2^2=V.

R and V are units, so both u_i are units. It follows that y=u_1/u_2 is a
verified root of R. The alternative original-root expression z_2/z_1 agrees
whenever those reductions are defined. For z_1=w_1/alpha_1 one may explicitly
adjoin alpha_1^(-1) to the localization; its image is invertible because R
is a unit. This avoids suggesting z_1 always belongs to the smaller localized
order. The opposite target orientation interchanges the field roles. Changing
a field root's sign only negates y. No root choice changes R1.

For a nonmonic defining polynomial with nonzero leading coefficient l, first
check any content/leading-coefficient cancellation and its modular gcd; never
cancel a nonunit silently. With gcd(l,N)=1, theta=l alpha is integral and

    F(T)=l^(d-1) f(T/l)

is monic integral, has theta as a root, and satisfies F(lR)=0 modulo N.
Its height has logarithm O(d log(H+1)). Here is explicit denominator clearing
for a subset of s rows, supplementing submission lines 413–417:

    qtilde_j = l a_j^2 - b_j^2 theta,
    Qtilde = product qtilde_j = l^s Q,
    W_1 = l^ceil((s+1)/2) w_1,
    W_1^2 = l^(2ceil((s+1)/2)-s-1) theta Qtilde,
    W_2 = l^ceil(s/2) w_2,
    W_2^2 = l^(2ceil(s/2)-s) Qtilde.                           (R12)

The displayed exponents on the right are 0 or 1, so both W_i are integral
on their respective sides. Use F'(theta) as the order multiplier, reduce at
theta=lR after its unit check, and divide the image by the corresponding
power of l. This recovers the same u_i as above. Separate fields use their
own l_i and s. The additional coefficient widths and exact products fit R11.
A proper leading-coefficient gcd is a factor; a full gcd may obstruct this
implementation. This construction does not assert an all-field fraction map.

Reducible defining polynomials require paid rational factorization and gcd
inspection of their evaluated integer factors, in a fixed order before
declaring failure. Reducibility alone does not promise a split. Zero field
elements are outside K^*; zero modular images have full gcd, while nonzero
nonunits can give proper gcds. Once every retained image is a verified unit,
their product cannot acquire a new zero/nonunit image. These branches must
be explicit and are consistent with the submission's intended restrictions.

If alpha is a field square, a square-root test of T^2-alpha supplies its root
at the same paid complexity. For monic f that root is integral; apply the
same derivative localization. A valid reduction is already a root of R.
For nonmonic f use the analogous scaling W=l sqrt(alpha), W^2=l theta.
The algebra K[T]/(T^2-alpha) then splits and is not a quadratic field. This
special case supplies neither a generic cheap field selector nor a reason
to grant the root or its reduction without paying these checks.

## 9. Norms and involutions: valid obstruction, necessary correction

Assume alpha is nonzero and nonsquare in the characteristic-zero field K,
L=K(beta), beta^2=alpha, and tau(beta)=-beta. Direct multiplication proves

    Norm_{L/K}(a-b beta)=a^2-b^2 alpha.

The coefficient arithmetic of L is available from this presentation, but
a compatible modular evaluation of beta would itself be a root of R. It is
not supplied by the norm identity.

Every nonzero retained product Q is a relative norm. For z in K^*, its
relative norm is z^2. Therefore Q=alpha z^2 implies alpha belongs to the
relative norm group. Since Norm(beta)=-alpha, subgroup closure proves

    alpha is a relative norm iff -1 is a relative norm.       (R13)

This is necessary for the twisted target, not sufficient for occurrence among
the finite subset products. It promises no inexpensive norm-equation solver,
unit computation or class-group computation.

If a real embedding sigma satisfies sigma(alpha)<0, every nonzero generator
has image a^2+|sigma(alpha)|b^2>0. Every retained product is consequently
positive, whereas sigma(alpha z^2)<0 for z nonzero. This proves nonattainability
for this whole product family in that field, at every list length. It includes
the empty product and requires no empirical sign sample. The associated
completion of L is complex over that real place; its nonzero norms are
positive. Total positivity of alpha only avoids this particular obstruction.
For the opposite mixed orientation apply the criterion to the other field.
It excludes this local realization, not every root-independent generator.

If A=product(a_j-b_j beta) is itself square in L, then Norm(A) is square
in K. Thus pairing that same square dependence with its conjugate loses
the nontrivial twisted class. This exact construction-level statement is valid.

More generally write a square root of Q in L as u+v beta. If Q is in K,
the beta coefficient in its square is 2uv=0. As K is a field, one of u,v
vanishes. Conversely either kind of root works. Hence

    K^* intersect L^*2 = K^*2 union alpha K^*2,               (R14)

with the two classes disjoint for nonsquare alpha. The root is invariant
under tau in the first case and anti-invariant in the second. Selecting a
square in L alone does not give a probability of selecting the latter.

**Required correction to line 473:** rational norms do not *always* lose
this bit. Conditional on R14, let b be 0 for Q=z^2 and 1 for Q=alpha z^2.
Taking the field-to-rational norm with its sign gives

    [Norm_{K/Q}(Q)] = b [Norm_{K/Q}(alpha)] in Q^*/Q^*2.     (R15)

If Norm(alpha) is nonsquare in Q, the rational norm square class distinguishes
b exactly. If Norm(alpha) is square, this particular invariant is constant
on the two possibilities. The submission made no assumption forcing the
latter case, so its unconditional wording must be rejected and replaced by
this dichotomy. Norms can be computed by a determinant/resultant with polynomial
work in the explicit input dimensions and bit lengths, and rational square
testing is elementary. This is a conditional diagnostic, not a proved balanced
law, an actual supply of anti-invariant squares, or a field-root algorithm.

The informative case is not an empty algebraic possibility. Symbolically let
D>1 be any nonsquare integer, t=D^2+4, u=1+sqrt(D), s=1+u^2, and s' its
conjugate in K=Q(sqrt(D)). Then ss'=t and alpha=t s' is a totally positive
integral generator with Norm(alpha)=t^3 nonsquare: D^2<t<(D+1)^2. The
retained-form element with a=t,b=1 satisfies

    a^2-b^2 alpha = t^2-alpha = alpha u^2.

It is an anti-invariant square in K(sqrt(alpha)), and its rational norm is
t^3(1-D)^2, which detects that class. This symbolic family only refutes a
blanket loss-of-information claim; it supplies no N,R-dependent generator,
valid modular-image frequency, or low-norm relation theorem.

For an arbitrary field element without the R14 promise, square rational norm
does not generally imply field squareness: rational norms merge the prime-ideal
valuations over each rational prime and retain only a quotient of square-class
information. Submission lines 484–486 are sound in that general sense, but
must not negate the restricted two-class diagnostic R15. Likewise, rational
norm functoriality alone cannot establish target attainment or useful density.

For monic f(T)=sum_{r=0}^d f_r T^r with coefficient height H, multiplying
over embeddings gives

    Norm(a^2-b^2 alpha) = b^(2d) f(a^2/b^2)
                        = sum_{r=0}^d f_r a^(2r)b^(2d-2r),
    |Norm| <= (d+1)H max(|a|,|b|)^(2d).

The homogenized expression covers b=0. This verifies equation (6.4), with
the standing nonzero-element restriction for square classes. It is an upper
bound on size, not a lower bound on smoothness probability, an assertion
of typical norm size, or a lower bound on all factoring algorithms.

## 10. Primary-source and matched-baseline audit

The following are statement/algorithm inspections at the specified scope,
not whole-proof certifications. The adjacent source record identifies the
exact preserved PDFs/text and the pages viewed. Historical access failures
remain in the unmodified original ledger and its review snapshot.

- **Rabin, 1979:** section 2's prime-root/CRT procedure and section 4,
  Theorems 1–2, were inspected; printed pp.12–14 were visually checked.
  The 1/e successful-residue premise, cutoff and historical
  2eF(N)+2log_2 N expression are correctly quoted as a reduction in that
  operation convention. They are not a complete modern raw-word bit ledger;
  R1–R3 and sections 6–7 provide that ledger and multiplicity extension here.
  Known-prime roots are an algorithmic ingredient, not an external factor
  input. [MIT primary PDF](https://dspace.mit.edu/server/api/core/bitstreams/24c62be8-babb-4ae7-8d00-f042f01cafd6/content).

- **Dixon, 1981:** Algorithm A_L, theorem, Lemmas 1–3 and final work count
  on printed pp.256–260 support the submitted conservative 3sqrt(2)
  constant and list-length failure estimate in the stated arithmetic model.
  The small-prime exclusion and prime-power root fibers matter. R4–R7
  explicitly justify the smooth-square input and stopped transfer with
  rounded B; the new twist-bit presentation is this submission's adaptation,
  not something claimed to be printed in Dixon. The dense-space accounting
  here is independent of the paper's historical storage remark.
  [Primary PDF](https://pages.cs.wisc.edu/~cs812-1/dixon.pdf).

- **Lenstra–Pomerance, 1992:** the main theorem on p.483 states complete
  prime factorization of every positive integer in expected L_N[1/2,1]
  time. I also visually inspected section 12, pp.513–514: fair independent
  random bits are charged, and expectation is for each fixed input, not
  over a favorable input ensemble. That section explicitly addresses the
  cost/success correlation in repeated trials. This remains a published
  theorem comparison, not my re-audit of its complete algorithm/proof.
  A supplied factorization is unnecessary: run that factorer internally and
  pay polynomial expected root lifting/CRT overhead. No refined space
  theorem is inferred; pathwise storage is bounded by work, and a time cap
  bounds space. [Primary PDF](https://math.dartmouth.edu/~carlp/PDF/paper85.pdf).

- **Lee–Venkatesan v1:** inspected Theorems 2.1/2.3/2.5/2.6, the concrete
  algorithm and polynomial law, section 7/Conjecture 7.82/Remark 7.85, and
  the relevant reconstruction discussion. The unconditional stated output
  is a square congruence at L_N[1/3,(64/9)^(1/3)]. Useful output for distinct
  Blum semiprimes retains the conjecture. The law selects m between
  (N/2)^(1/d) and N^(1/d), then random coefficients multiplying (X-m);
  it is not an arbitrary handed-in R law. Theorem 2.6 has its exceptional
  polynomial fraction and sufficiently many smooth pairs, not an all-field
  square-class oracle. The section-7 prose indeed has the sign typo noted
  in the submission; its productive criterion is chi=-1. None of this is
  a re-audit of the analytic proof or a transfer to a different generator.
  [Primary v1](https://arxiv.org/html/1805.08873v1).

- **Coppersmith, 1993:** sections 2–4, including the matrix layout and
  per-field square roots feeding one global rational root, support the
  prior-art description. Printed p.177 was visually checked. If
  epsilon^3=(46+13sqrt(13))/108 there, the complete model constant 2epsilon
  has cube (92+26sqrt(13))/27. This gives the quoted approximately 1.902,
  compared with approximately 1.923 for the ordinary model. Section 4's
  approximately 1.639 per-input figure excludes its reusable precomputation.
  The paper labels its estimates heuristic; its character/square-root and
  useful-output premises do not become rigorous here. This is the proper
  cold heuristic comparator, distinct from the rigorous LP comparator.
  [Primary PDF](https://link.springer.com/content/pdf/10.1007/BF00198464.pdf).

- **Prest–Zimmermann:** sections 2.2/3.2 contain the stated auxiliary-prime,
  square-root-near-sqrt(N), c/p common-root and higher-degree progression
  constructions. Their cubic O(N^(5/4)) resultant size calculation uses
  short-vector size expectations/premises; it is not a guaranteed all-input
  height theorem for two nonlinear irreducibles, nor a complete factoring
  theorem. The submission keeps this qualification. Pay prime selection,
  failed choices and irreducibility; an independently prescribed uniform R
  is not their selected common root.
  [Author PDF](https://members.loria.fr/PZimmermann/papers/polyselect.pdf).

- **A. K. Lenstra, 1983:** section 2 and Algorithms 4.1/4.4, Theorem 4.5
  and its complexity passage on pp.251–254 were checked; p.253's formulas
  were visually checked. The bounds and nu/d/b/A dictionary used in section 8
  agree with the source. The auxiliary prime and finite-field factorization
  are included and there is no inert-prime oracle. This inspection does not
  certify every lattice lemma or the entire proof; it supports use of the
  published algorithm and the stated conservative bit-cost substitution.
  [Primary PDF](https://ir.cwi.nl/pub/2541/2541D.pdf).

- **Nguyen, 1998:** the supplied-square methods in section 2, the four
  algorithm stages in section 4, the inert-prime caveat in 4.5, and the
  fixed-field limitations in sections 5/7 support the report. Section 4.1
  also explicitly discusses the difficulty of integral-basis/discriminant
  preparation. Those costs cannot be silently made free in a varying field.
  The observed near-linear relation-count behavior is not an unconditional
  variable-degree bit bound. The paid Lenstra fallback avoids reliance on
  those heuristic speed claims.
  [Primary PDF](https://link.springer.com/content/pdf/10.1007/BFb0054859.pdf).

- **Joux–Lercier–Smart–Vercauteren, 2006:** section 4.3 and equation (6)
  require the known inert prime, class number, generators of powered ideals,
  and corrected unit/Schirokauer-map terms stated in the submission. The
  class-number-one/computable-unit case removes those named difficulties,
  not the need for actual arithmetic. Section 5 is a heuristic finite-field
  DLP analysis in q, not unknown-factor integer factoring. No extra constant
  is borrowed from it for W003.
  [Author PDF](https://lercier.pages.math.cnrs.fr/files/pdfs/JLSV06.pdf).

- **Stevenhagen:** sections 6–10 support the separation of nonmaximal-order,
  ideal-class, unit and root-reduction issues. The derivative multiplier is
  corroborated in section 7 and proved directly in section 8 of this review.
  The source's casual suggestion that a noncoprime derivative has found a
  factor must still exclude full gcd N; this submission does so. This is
  supporting exposition, not the quantitative basis for R11.
  [Author chapter](https://pub.math.leidenuniv.nl/~stevenhagenp/ANTproc/04psh.pdf).

The original ledger records six failed retrieval actions: MIT web Download;
the direct CSAIL mirror timeout; ePrint 2011/292 HTTP 403; IACR direct HTTP
403 and web failure; and the author-publication-page web timeout. Those
historical failures were preserved, not retried away or relabeled successes.
The recovered MIT bitstream, publisher/author PDFs and local primary archives
support the stated inspections. The inaccessible Koo–Jo–Kwon paper still
supports no theorem claim. This review additionally reopened the LV, Dixon
and LP primary URLs successfully; LP's local text extraction was unusable
for its scanned pages, so the relevant pages were read as rendered images.
No new broad literature search or claim of literature completeness was made.

## 11. Small-R count, remaining claim, and closure of this review

For a nonnegative cutoff U and R represented in [1,N-1], uniformity on Q gives

    Pr(R<=U | outer unit) = #(Q intersect [1,floor(U)]) / |Q|
      <= min(1, max(0,min(N-1,floor(U))) 2^k/phi(N)).          (R16)

The submitted looser (floor(U)+1)2^k/phi(N) bound is valid for U>=0.
Its wording about any numerical U needs that restriction or the clamping
in R16: a sufficiently negative cutoff would otherwise produce a negative
right side. For growing balanced distinct semiprimes, k=2 and phi(N)/N
tends to 1. A fixed-constant cutoff U=L_N[2/3,c]=N^o(1) therefore captures
at most N^(-1+o(1)) of this distribution. This is an upper count, not an
attained probability or a prohibition on other representations of R.

The modified pair law evaluates a^2-b^2 alpha_i, constraining the ordinary
linear coefficients to squares and coupling two fields through the same pair.
The LV law described above has different common-root, coefficient and retained-
relation distributions. No map of full probability spaces analogous to section 4
has been supplied for those field streams. Neither randomized polynomial
perturbation alone nor a large homogeneous kernel proves actual target mass.

The unresolved positive statement is still a uniform, paid N,R-only mixed-field
generator with actual completion probability s and cold mean cost C for which
C/s has an L_N[1/3,O(1)] envelope, followed by the valid outer reduction.
The ordinary heuristic GNFS constant and the Coppersmith multi-field constant
are different comparison questions. No rigorous or heuristic constant gain
is established here. A finite field-square membership search, a local norm
obstruction, and a theorem about supplied roots are not that generator.

**Next proof/test selected: none.** The integer claims have been resolved at
their deliberately old upper bound; a finite experiment cannot establish the
missing uniform field supply law. The original proposed next proof only becomes
useful for a separately specified generator that survives its own norm and
real-place checks. This review has not read or independently disposed of the
frozen Lens A construction, so it does not direct a positive-mass proof for
that construction. Its separate review and coordinator disposition remain
authoritative for deciding whether a later changed generator warrants work.

The coordinator can adopt the narrow completed proofs and the stated corrections
without changing any original evidence. This report neither accepts itself
nor closes all root-independent constructions, all NFS variants, or classical
factoring. The requested improvement remains unestablished.
