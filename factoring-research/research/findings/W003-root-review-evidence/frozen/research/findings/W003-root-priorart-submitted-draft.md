# W003 Lens B: primary sources, root inversion, and prescribed targets

2026-10-08. **Research delivery; all new deductions UNACCEPTED pending separate
review. Verified COMPLETE classical factoring complexity improvement: NONE.**

This is the independent source/reduction lens, not an independent review of
Lens A. I did not read `W003-twisted-fields.md` or its supporting artifacts.
No experiment, example search, factoring implementation, Lean action, package
installation, delegation, commit, publication, scheduler, or shared-record edit
was performed. Source downloading, text extraction, page rendering, document
writing and hashing are the only machine work in this delivery.

Frozen brief: `research/hypotheses/W003.md`, SHA-256
`fc8f5cf42a34b020833832a56994421c183e22a8fd2e951a6cb9c6cee14ab629`.
[Input seals](W003-root-priorart-inputs.json),
[source/access ledger](W003-root-priorart-sources.json), and
[separate delivery manifest](W003-root-priorart-delivery.sha256) identify the
bytes. The parent owns acceptance and shared state.

## 1. Outcome and inherited boundary

The root-independent interface is realizable by existing factoring algorithms
followed by prime-power root extraction. It is also realizable at the older
Dixon scale by the explicit random-twist adaptation in section 4. That adaptation
is a deduction here, not a claim that Dixon printed this exact interface, and
not a novelty claim. It provides an exact distributional coupling for integer
relations. No corresponding coupling for the proposed two-field generator has
been established.

The mixed-field recovery algebra is valid with paid field roots and localized
maps. The missing step is finding the prescribed square class, with enough
probability under a completely specified N,R-dependent generation law. A large
homogeneous kernel does not establish that step. Conjugate-pair generation also
has an actual norm-group obstruction; negative real embeddings give a particularly
simple exclusion for the twisted side. These are scoped statements, not a lower
bound on all root-independent algorithms.

The authoritative W002 B/C and H027/H028/H031 dispositions govern this report.
In particular, W002 B accepts a stream with arbitrarily large square kernel and
trivial productive image; H031 accepts its repaired finite trial and
L_N[1/3,3+o(1)] **per-trial upper envelope**, without a useful-mass lower bound.
Their historical provisional labels do not supersede those dispositions.
The corrected H027 root-fiber condition is already accepted at its stated scope.

Write n=bit_length(N), and
L_N[a,c]=exp((c+o(1))(log N)^a(log log N)^(1-a)).
A source's arithmetic-operation count is not automatically a bit count.
Polynomial factors in n do not change the displayed L constants.

## 2. Algorithm and cost map from primary sources

**Rabin 1979, section 4, Theorems 1–2, printed pp.12–14.**
The input to the assumed algorithm is a quadratic residue, not its preimage.
For a product of two distinct odd primes, one root suffices; uniform preimage
sampling gives a useful mismatch with probability 1/2. Theorem 2 permits success
on only a 1/e fraction of unit quadratic residues within a time cutoff F(N).
Its historical expected count is 2eF(N)+2log_2 N in its operation convention.
For W003 use the fully charged bit accounting in section 3, including sampling,
squaring, verification and failed calls. This is a reduction, not a root-generation
algorithm. Section 2 describes root extraction when the primes are known.
[Institutional report PDF](https://dspace.mit.edu/server/api/core/bitstreams/24c62be8-babb-4ae7-8d00-f042f01cafd6/content).

**Dixon 1981, Algorithm A_L and theorem, pp.256–260.**
The theorem uses v=exp(sqrt(2 log N log log N)) and a random list of length
floor(v^2+1). Expected work is O(v^3), or L_N[1/2,3sqrt(2)], in operations
on N-sized integers; failure fraction is O(list_length^(-1/2)), uniformly
on odd integers with at least two distinct prime factors. Polynomial bit
costs preserve that L constant. Lemma 2 and p.259 give smooth-square supply
without a random-integer heuristic; Lemma 3 conditions on the entire square
list and counts root fibers. Multiplicities are allowed. Section 4 below
pays dense storage explicitly rather than borrowing a sparsity estimate.
[Primary paper](https://pages.cs.wisc.edu/~cs812-1/dixon.pdf).

**Lenstra–Pomerance 1992, main theorem, p.483.**
Their probabilistic algorithm completely factors every positive integer in
expected L_N[1/2,1] time. Internally factoring N, then extracting roots modulo
the obtained prime powers and applying CRT, meets the N,R-only interface with
polynomial expected additional work. It uses no supplied factors. This is an
existing, better rigorous comparison than the conservative Dixon adaptation.
No improved space theorem is inferred from the inspected opening: working
space is bounded by elapsed bit work, and a time-capped invocation also caps
space. Only the main theorem and introductory algorithm description were
inspected here, not its entire proof.
[Primary paper](https://math.dartmouth.edu/~carlp/PDF/paper85.pdf).

**Lee–Venkatesan v1, Theorems 2.1/2.3/2.5/2.6, sections 4,6,7.**
Theorem 2.1 gives expected L_N[1/3,(64/9)^(1/3)] square-congruence generation.
Theorem 2.3 needs Conjecture 7.82 for useful congruences on distinct Blum
semiprimes. Section 7 makes the productive character explicit; Remark 7.85
extends the issue to multiple polynomials. These are not prescribed-root
inversion theorems. The supply theorem uses its specific randomized
polynomials and coefficient ranges, with a small chosen common root m;
Theorem 2.6 handles homogeneous square reconstruction under its stated
polynomial law. Neither says that an arbitrary prescribed nonzero square
class belongs to the generated span. This inspection is not a re-audit of
the complete analytic proof. The v1 proof of 2.3 contains a sign typo in its
prose condition; the criterion and following calculation use chi=-1.
[Primary v1](https://arxiv.org/html/1805.08873v1).

**Coppersmith 1993, sections 2–4, especially pp.170,175–178.**
The multi-field algorithm shares rational-prime columns and has separate
ideal/character blocks for each field. It extracts a square root for each
selected field packet and combines their images with one global rational
square root. The paper explicitly labels its smoothness-based running-time
estimates heuristic. Its general single-input constant is about 1.902,
more precisely ((92+26sqrt(13))/27)^(1/3), versus ordinary GNFS's
(64/9)^(1/3), about 1.923. The approximately 1.639 figure is after reusable
precomputation, not a cold N-only bound. This is existing homogeneous
multi-field reconstruction, not the W003 mixed target.
[Primary paper](https://link.springer.com/content/pdf/10.1007/BF00198464.pdf).

**Prest–Zimmermann, sections 2.2 and 3.2.**
Two nonlinear defining polynomials with a common modular root are established
NFS polynomial-selection machinery. The displayed Montgomery two-quadratics
algorithm chooses an auxiliary prime p, a square root c of N modulo p near
sqrt(N), and uses m=c/p modulo N. The generalization uses a geometric progression
with c near N^(1/d), followed by lattice reduction. Its cubic size analysis
gives skewed resultant O(N^(5/4)), with its stated size/short-vector premises.
These are polynomial-selection results, not complete factoring-time or
prescribed-R supply theorems. In particular their selected root is not a
uniform quadratic residue R handed to the procedure. Auxiliary-prime/root
selection, irreducibility and all failed choices remain chargeable.
[Author-hosted primary paper](https://members.loria.fr/PZimmermann/papers/polyselect.pdf).

**A. K. Lenstra 1983, Algorithms 4.1/4.4 and Theorem 4.5, pp.250–254.**
Factoring T^2-U over a presented number field is an actual algorithm that
finds a root or certifies nonsquareness. It does not generate U in the desired
class. For polynomial degree nu, field degree d, defining F, denominator b,
and coefficient maximum A, Theorem 4.5 bounds arithmetic operations by
O(nu^6 d^6+nu^5 d^6 log(d|F|)+nu^5 d^5 log(bA)), with operand bits
O(nu^3 d^3+nu^2 d^3 log(d|F|)+nu^2 d^2 log(bA)). Use 1+log at small values.
For nu=2, fixed polynomial bounds on field parameters, and coefficient
bit length h, schoolbook bit work is O((h+1)^3 poly(n)). Products of M
relations can have h=O((M+1)poly(n)); the root cost must reflect that.
Auxiliary-prime search is included, with no inert-prime oracle required.
[Primary proceedings paper](https://ir.cwi.nl/pub/2541/2541D.pdf).

**Nguyen 1998, sections 2,4,5,7, pp.153,155–156,162–164.**
The Montgomery-like algorithm extracts a square root of a supplied square
represented by many algebraic factors. Ideal simplification, ideal square-root
formation, lattice approximation and residual root extraction are actual
steps. Section 5 explicitly leaves the overall complexity unresolved; observed
linear behavior in the relation count is heuristic, with the field fixed.
The missing bounds include lattice-entry sizes and final-error embeddings.
The CRT method uses suitable inert primes, whose existence is qualified in
section 4.5. Thus a fast *verified* field-root implementation is useful after
a target is attained; it supplies no target-attainment law or unconditional
variable-degree linear reconstruction theorem.
[Primary paper](https://link.springer.com/content/pdf/10.1007/BFb0054859.pdf).

**Joux–Lercier–Smart–Vercauteren 2006, section 4.3, equation (6).**
Automorphism compression of a factor base is established, here for finite-field
discrete logarithms. The section assumes a known inert prime p. Its reduced
system needs the class number and explicit generators of powered ideals,
with extra unit-map terms. The stated simplification is straightforward in
the indicated class-number-one/computable-unit setting. Section 5's L_q[1/3]
bounds are heuristic DLP bounds in q=p^r, not factoring bounds for unknown
prime divisors of N. This is a concrete warning against importing an
involution-based compression without its arithmetic inputs.
[Author-hosted primary paper](https://lercier.pages.math.cnrs.fr/files/pdfs/JLSV06.pdf).

Stevenhagen's NFS chapter, sections 6–10, was also inspected as supporting
exposition: ideal parity, ideal-class obstruction, units, and order-to-field
root denominators are separate issues. It is not the primary basis for a new
root complexity bound; Lenstra's algorithm above provides that bound.
[Author-hosted chapter](https://pub.math.leidenuniv.nl/~stevenhagenp/ANTproc/04psh.pdf).

## 3. Exact outer reduction in the W003 finite-word law

The following is an explicit extension/accounting of known root-fiber algebra,
**UNACCEPTED here pending review**, not a new root algorithm.

After paid handling of even N, primality and perfect powers, suppose
N=product_{i=1}^k p_i^{e_i} is odd with k>=2. This factorization is used only
in the proof. Let G=(Z/NZ)^*, Q=G^2, and rho_k=1-2^(1-k).
Every R in Q has exactly 2^k unit preimages. At each odd prime power the
ratio of two roots is +1 or -1: their difference and sum cannot both be
divisible by p_i because the roots are units. CRT then gives the fiber count.

One outer trial draws exactly n unbiased bits as x. It rejects x>=N; x=0
has full gcd N and is a failure, not a factor. There are phi(N) unit words,
N-phi(N)-1 words with a proper gcd, and 2^n-N out-of-range words. Conditional
on the unit branch, x is uniform on G and R=x^2 is uniform on Q.

Pad the inner tape to a fixed finite cap. For fixed R and inner tape, all
selection, stopping, field failures and the candidate output are functions
only of N,R and that tape. If the output verifies as y^2=R modulo N, exactly
two of the 2^k possible x are +y or -y. All others make gcd(x-y,N) proper;
it selects a nonempty proper collection of **whole prime-power components**.
Thus, even after conditioning on any successful inner transcript,

    Pr[proper split | verified inner root, unit branch] = rho_k.       (3.1)

The returned y need not itself be uniformly random among roots. It may be
deterministic. What matters is the residual uniformity of x given everything
the inner construction sees. A success probability depending arbitrarily on
R does not change (3.1), since all fibers have the same size. Passing x,
a root-dependent selection bit, or outer gcd-failure feedback to the inner
procedure would invalidate this argument. Fresh outer trials avoid that issue.

For each R, let a_R be the probability that the inner trial returns a verified
proper factor before a root, and s_R the probability that it instead returns
a verified root. These events are disjoint; bad outputs and all cutoffs fail.
The exact success probability per **raw outer word** is

    p_N = (N-phi(N)-1)/2^n
          + phi(N)/2^n * E_{R uniform in Q}[a_R + rho_k s_R].          (3.2)

This includes early factors, full-gcd failure, rejected words, and every inner
failure. For k=1 the root mismatch probability is zero; the elementary
prime-power branch is essential. Even moduli are not covered by this formula.
A Jacobi criterion restricted to Blum semiprimes is unnecessary here.
When an internal factorer has obtained the primes, a unit root a modulo p
lifts from p^j to p^(j+1) by solving one linear equation with coefficient
2a modulo p; that coefficient is invertible. Rabin's finite-field root
method, these at-most-n Hensel digits, and CRT require expected poly(n)
additional bit work and polynomial working space. They do not require
supplied factors at the external input.

Let C_N be the actual mean *cold* trial bit cost, including preprocessing when
repeated, random bits, all discarded attempts, root verification and gcds.
Independent identically distributed cold restarts have expected work C_N/p_N
when p_N>0 and C_N is finite. This follows by summing the costs of reached
trials; a trial's own cost and success may be correlated. A cap C with success
p gives failure (1-p)^j after j independent capped trials, cost <=jC and
space no greater than the single-trial storage plus counters. These facts do
not provide a positive p or an economical C for Lens A.

A splitter valid on every remaining composite gives complete factorization
by verified recursion and primality tests. There are at most O(n) nontrivial
nodes including multiplicity handling. Uniform monotone L-cost upper envelopes
therefore keep their leading exponent/constant; a Blum-semiprime-only theorem
does not provide this all-input extension.

## 4. A root-independent mixed-integer construction at the old Dixon bound

**On-paper adaptation, UNACCEPTED.** This addresses whether the proposed
interface is already achievable at a worse bound. It does not claim that the
following twist-bit presentation was explicitly published in the inspected
sources. Its supply input is Dixon's proved smooth-square estimate, not a
new assumption or a square-root oracle.

On the continuing domain of section 3, given N and a promised unit square R:

1. Choose an integer B with v<=B<=2v, v=exp(sqrt(2 log N log log N)), for
   N>=3, using certified rounding. Enumerate primes <=B and inspect their
   gcds with N. Return any proper factor. Prime enumeration by elementary
   trial division already costs only O(B^(3/2) poly(n)); no free prime table
   is needed. Let h be the number of primes. After this branch all such
   primes are units and N has no prime divisor <=B.
2. Set T=ceil(16(h+1)B). Use exactly T records of n+1 fresh bits, streamed
   rather than stored: an n-bit word m and an independent bit epsilon.
   Reject m>=N; inspect gcd(m,N), returning proper factors and discarding
   full gcds. On units form v_j=R^epsilon m^2 modulo N in [1,N-1].
   Trial divide v_j by the base, retaining full exponent rows and m,epsilon
   only when completely smooth. Stop at the first h+1 retained rows;
   insufficient rows at the cap give FAIL.
3. Find one nonzero parity dependency c on those rows by deterministic dense
   elimination. Choose it from the v_j/exponent data and record order alone,
   **without using the epsilon labels or m values**. Let E=sum c_j epsilon_j.
   If E is even, return FAIL and restart the entire cold trial independently.
4. If E is odd, compute modulo N

       M = product m_j^c_j,
       S = product_{p<=B} p^(sum_j c_j ord_p(v_j)/2),
       y = S * M^(-1) * R^(-(E-1)/2).                              (4.1)

   All inverses are of verified units. Verify y^2=R and return ROOT(y).
   No huge integer product or hidden factorization is used. Signed integer
   representatives would require a sign row; this construction uses positive
   representatives only.

**Exact coupling.** Fix any h_R in G with h_R^2=R *for the proof only*.
For each accepted residue word define z=h_R^epsilon m modulo N. For each
fixed epsilon, multiplication by h_R^epsilon permutes Z/NZ and preserves
its gcd with N. Hence z is uniform modulo N and independent of epsilon;
v_j=z^2 has exactly Dixon's law. The rejected-word indicator is independent
of epsilon. Conditional on unit admission, smoothness and the whole retained
v_j list, all retained epsilon bits are still independent unbiased bits.
Stopping and the selected nonzero c inspect only that list. Consequently
E is odd with probability exactly 1/2. This is an actual coupling, unlike
an analogy between the shapes of two different NFS relation streams.

For a fixed finite dataset with kappa independent parity dependencies,
the probability that at least one has odd epsilon sum would be
1-2^(-kappa); the displayed algorithm needs only one, so no full square-class
basis is granted. In algebraic terms it seeks a nonzero value of a fresh
random linear functional on a nonzero known kernel. That is the special
reason the inhomogeneous target is available here.

**Supply and probability, with raw rejects included.** Dixon's Lemma 2 and
p.259 show, for sufficiently large N after the small-prime branch, that a
uniform residue z has a positive B-smooth square with probability at least
1/B. Using B>=v only increases smoothness supply. An n-bit raw record
therefore has admission probability at least (N/2^n)/B>1/(2B). In the
hypothetical full T-record tape, the admission count X is binomial with
mean mu>=8(h+1). Chebyshev gives

    Pr[X<h+1] <= mu/(mu-h-1)^2 <= 8/(49(h+1)).                       (4.2)

Early proper gcds only help. Conditional on no such early success and on
completion, the odd-label probability is 1/2 by the coupling. Thus the
probability of FACTOR or ROOT in a capped trial is at least
(1-8/(49(h+1)))/2, in particular greater than 3/8 for sufficiently large N.
No unproved smoothness or field-character independence has been inserted.
For small N the same finite trial has positive completion/root probability
(the residue 1 and its two epsilon realizations suffice), so independent
restarts have finite expectation; a fixed finite initial range may also use
paid exhaustive handling. No uncomputed threshold is an algorithm input.

**Full conservative costs.** There are T=O(B(h+1)) raw attempts, each using
O(h poly(n)) bit work for complete trial division, gcds and residue work.
The retained matrix has h+1 rows of h full exponents and provenance. A
sequential implementation scans each row for every base prime and each pivot
for every elimination pass; dense elimination costs O((h+1)^3 poly(n)).
Record order and provenance eliminate random-access assumptions. Modular
reconstruction, exponent sums, inverses and verification fit that envelope.
All scalar indices have O(n+log B) bits, individual exponents O(log n) bits,
and summed exponents O(log((h+1)n)) bits. Prime-list scans and rejected
records are charged. Therefore

    time per cold capped trial <= B^3 poly(n),
    working space <= B^2 poly(n),
    random tape length <= (n+1)ceil(16(h+1)B).                       (4.3)

The tape is generated online; stopped records can equivalently be padded.
The resulting expected FACTOR-or-ROOT cost is
L_N[1/2,3sqrt(2)] with space L_N[1/2,2sqrt(2)] in this dense realization.
Combining it with section 3 gives the same conservative complete-factoring
L bound: on any unit outer branch, a_R+rho_k s_R is at least half the
inner FACTOR-or-ROOT probability; nonunit outer words add direct success.
Indeed (3.2) is bounded below by
(3/16)(N-1)/2^n for sufficiently large continuing N. Cold restarts thus cost
only a constant factor at each split, and recursion only poly(n).

This is already slower than the rigorous Lenstra–Pomerance complete bound.
If strictly ROOT-only output is required, an inner FACTOR branch can complete
the factor tree by the same verified splitter on smaller factors, then use
prime-power extraction and CRT. Polynomially many recursive subcalls preserve
the stated conservative L bound. This composition supplies no known-factor
input.

It also does not preserve L_N[1/3] relation costs: the uniform residues have
N-sized representatives. Deleting the hidden preimage has not created an
NFS-scale supply theorem. The coupled law concerns **integer residues**;
it supplies no distributional statement for a_j^2-b_j^2 alpha_i.

## 5. The mixed-field target: what is easy, what is being asked

These symbolic checks of the brief are **UNACCEPTED deductions**, independent
of any Lens A draft.

For a finite retained list let q_ij=a_j^2-b_j^2 alpha_i be nonzero and have
common verified unit image v_j. Define the genuine square-class map

    A: F_2^M -> K_1^*/K_1^*2 direct_sum K_2^*/K_2^*2,
    A(c) = ([product q_1j^c_j], [product q_2j^c_j]),
    tau = ([alpha_1],0).                                           (5.1)

The requested subset exists exactly when tau is in im(A). Rank-nullity
establishes something about ker(A), not membership of tau in im(A).
If full square-class coordinates were paid for, this would be an ordinary
inhomogeneous binary solve. Adjoining a target column and finding some
homogeneous dependency is insufficient: its target coefficient must be 1.
If [alpha_1]=0, the target is homogeneous; section 6 handles that separate
square-alpha case. Parity of prime ideals alone omits unit, class-group and
order obstructions.
Random character columns must evaluate the target too and need their own
separation guarantee. They cannot turn an unattainable target into an
attainable one.

For fixed data an entirely finite reference search exists: enumerate all
2^M subsets, multiply their field elements exactly, and factor T^2-alpha_1 Q
and T^2-Q on the two sides. Reject nonsquares, invalid reductions and
nonunits. Use Lenstra's paid algorithm, not a full square-class oracle.
With field degree d, coefficient height H and |a_j|,|b_j|<=A_0, explicit
product widths are polynomial in M,d,log H,log(A_0+1). A conservative envelope
is 2^M (M+1)^3 poly(d,log H,log(A_0+1),n) bit work and polynomial working
space in those parameters, streaming subsets. It decides attainability of
this finite list. If M itself has L_N[1/3,c] size, this fallback is far beyond
an L_N[1/3] algorithm. A better search must be specified and charged.

**Recovery and denominators.** For clarity suppose f_i are monic irreducible
integer polynomials, alpha_i integral, and f_i(R)=0 modulo N. Factorization
and irreducibility checks are paid. If a proposed defining polynomial is
reducible, evaluate its factors at R and inspect proper gcds; reducibility
alone does not promise a split. A full gcd N is not a proper factor.

If Q(alpha_1)=alpha_1 z_1^2 and Q(alpha_2)=z_2^2, instead extract

    w_1^2=alpha_1 Q(alpha_1),      w_2^2=Q(alpha_2).                  (5.2)

Here w_1=alpha_1 z_1; both w_i are integral, avoiding an unjustified claim
that z_1 itself is integral. Let delta_i=f_i'(alpha_i),
D_i=f_i'(R) modulo N. Check gcd(D_i,N): a proper value is a factor;
full gcd fails this localization; only gcd=1 permits inversion.
The order multiplier gives H_i=delta_i w_i in Z[alpha_i]. Compute this in
the exact field, cancel rational output denominators, verify integer
coefficients and H_i^2=delta_i^2 w_i^2, then reduce

    u_i=H_i(R)/D_i modulo N.

The map is on Z[alpha_i,delta_i^(-1)], not all of K_i. Now
u_1^2=R V and u_2^2=V with V=product v_j, so both u_i are units and

    y=u_1/u_2,                 y^2=R modulo N.                     (5.3)

Equivalently the original reduced z_i give y=z_2/z_1. Opposite orientation
Q(alpha_1)=z_1^2, Q(alpha_2)=alpha_2 z_2^2 reverses the roles and yields
u_2/u_1. Verify the final congruence. Different field-root signs merely
negate y and leave (3.1) unchanged.

For nonmonic f with leading coefficient l, one may use the integral generator
theta=l alpha and monic F(T)=l^(d-1)f(T/l), with theta mapping to lR.
All l inversions and derivative denominators need unit checks, coefficient
height conversion, and paid exact arithmetic. A leading coefficient with
proper gcd gives a factor; full gcd can obstruct this implementation.
Zero q_ij or zero images are outside the square-class domain: inspect gcds
and either output a proper factor or reject. No universal fraction-field map
or discriminant inverse is granted.

## 6. Quadratic extensions, involutions, and rational norm compression

Assume alpha is nonzero and nonsquare in K, and set
L=K(beta), beta^2=alpha, tau(beta)=-beta. Then

    a^2-b^2 alpha = Norm_{L/K}(a-b beta).                           (6.1)

This is ordinary quadratic norm algebra. It does **not** map beta to a known
residue modulo N: evaluating beta would already require a root of R.
The coefficient representation of L is computable without such an evaluation.
If alpha is square in K, the algebra splits instead of defining a quadratic
field; test this separately. In that case a valid reduction of its field
root already gives a root of R, with the same paid denominator checks.

**A necessary norm condition for the twisted side.** Every product Q of
(6.1) is a norm. Every z^2 with z in K is also a norm. Consequently

    Q=alpha z^2  implies alpha in Norm_{L/K}(L^*).

Since Norm(beta)=-alpha, this is equivalent to

    -1 in Norm_{L/K}(L^*).                                        (6.2)

Condition (6.2) is necessary, not sufficient for the finite retained subset
problem: even the entire norm group is larger than the generated list.
No free norm-equation solver or class-group computation is inferred.

A concrete obstruction needs no numerical test. If K has a real embedding
sigma with sigma(alpha)<0, every retained nonzero a^2-b^2 alpha is strictly
positive under sigma, while sigma(alpha z^2)<0 for nonzero z. Thus the
twisted target is unattainable for **every** such product in that field.
It is also the familiar local obstruction to -1 being a norm from a complex
quadratic extension at that real place. Positive-at-all-real-places alpha
avoids this particular obstruction; it does not prove attainability.
For the opposite target orientation, apply the test to the other field.

**Why a homogeneous extension trick can erase the target.** If an algorithm
makes A(beta)=product(a_j-b_j beta) an actual square in L, then
A(beta)A(-beta)=Norm(A) is a square in K. That method selects the untwisted
class automatically. It cannot give nontrivial [alpha] by merely pairing the
same square dependency with its conjugate.

There is a weaker condition that retains both possibilities:

    Q in K^* intersect L^*2  iff  Q in K^*2 or Q in alpha K^*2.       (6.3)

Indeed if (u+v beta)^2 is in K, its beta coefficient 2uv is zero, so its
root lies either in K or beta K. Equivalently tau(w)=+w or -w for a square
root w of Q in L. A homogeneous square condition in L therefore needs an
additional invariant/anti-invariant choice to select the mixed target in
the two fields. The extra bit has no proved balanced distribution here.
Taking rational norms does not recover that lost bit.

For monic f of degree d,

    Norm_{K/Q}(a^2-b^2 alpha)
       = sum_{r=0}^d f_r a^(2r) b^(2d-2r),
    |Norm| <= (d+1)H max(|a|,|b|)^(2d).                            (6.4)

The formula is valid also at b=0 by homogenization. It is a size upper
bound, not a smoothness or small-value theorem. Norm functoriality makes
rational norm compression an arithmetic identity, not a free increase in
usable relations. Full norms aggregate primes over distinct ideals and lose
square-class information; a rational square norm is not a certificate of a
field square. The legitimate automorphism methods in section 2 keep
additional arithmetic structure and have explicit input premises.

## 7. Why the NFS supply theorem has not transferred

This is a comparison of the frozen brief to the inspected algorithms, not a
claim about what Lens A ultimately submitted.

The changed input root is R, uniform in Q on the outer unit branch. It is not
LV's selected m near N^(1/d), and the generator a^2-b^2 alpha restricts the
linear coefficients to squares. Correlations between both fields, common
pairs, retained lists and target labels must be proved for their actual law.
Random polynomial perturbation at R alone does not show that their joint
norms have LV's distribution.

For example, for any prescribed numerical cutoff U,

    Pr[R<=U | outer unit] <= (floor(U)+1) 2^k / phi(N).              (7.1)

On growing balanced distinct semiprimes, a cutoff U=L_N[2/3,c] therefore
captures at most N^(-1+o(1)) of that law. This count rules out casually
identifying the handed-in R with a usual small integer root; it does not
rule out small-height polynomials at other representations of R, paid
lattice selection, or a different successful construction.

There are three separate obligations: obtain useful low-norm relations;
find the prescribed actual square class among them; and extract and reduce
its roots at the advertised full bit cost. Section 3 resolves the *fourth*
step, useful outer mismatch, if all three have succeeded without seeing x.
The known square-congruence theorem resolves neither their modified supply
law nor their target membership. The exact integer coupling in section 4
shows the standard of proof required for any claimed transfer.

## 8. Disposition, unsupported statement, and one next proof

**Disposition:** source/reduction gate delivered; no new complete factoring
improvement and no completed review of Lens A. Known algorithms already
realize root inversion. Two-field NFS, conjugation norms and extraction of
existing field squares are not new ingredients. The randomized integer
adaptation and norm/involution checks above remain UNACCEPTED deductions.

**Unsupported positive statement:** a uniformly specified cold N,R-only
mixed-field construction has a cold mean cost C and an actual completion probability s for which
C/s is L_N[1/3,O(1)], uniformly over the required inputs. Neither the
bounded literature inspection nor this report proves it. In particular there
is no demonstrated inverse-polynomial target-attainment mass, preserved
LV relation law, or improved Coppersmith-matched heuristic constant.
A missing theorem in this search is not a nonexistence or hardness result.

**One next proof that could change the conclusion:** for the eventual frozen
Lens A generator, prove a lower bound on the actual paid probability of
reaching tau in (5.1), after all polynomial, real-place/norm, relation and
root-reduction failures, strong enough that C_N/p_N has the claimed complete
L_N[1/3] envelope. The proof must specify the joint generation law and justify
any coupling it uses. Homogeneous nullity alone fails this criterion.
No finite test or implementation is proposed by this source task.

## 9. Inspection and retrieval scope

Primary content inspected: Rabin section 2 and all of section 4; Dixon's
algorithm, theorem and Lemmas 1–3 with its final work count; LV's named
statements, polynomial law, square-class/character discussion and section 7;
Coppersmith sections 2–4 reconstruction and comparison; Prest–Zimmermann's
explicit selection algorithms and cubic analysis; Lenstra sections 2 and 4;
Nguyen's algorithm and complexity limitations; JLSV section 4.3 and section 5;
Lenstra–Pomerance's opening main theorem only. Supporting Stevenhagen
sections 6–10 were inspected. No source's whole analytic proof is certified
by this read scope.

MIT's repository supplied Rabin's PDF and repository OCR directly. The PDF
was also extracted locally; rendered printed pp.12–14 confirm the theorem,
operation convention and cutoff proof where OCR loses symbols. Dixon's
printed pp.257 and 259 were visually checked for the exact v, list length,
3sqrt(2) constant and smooth-square estimate. Lenstra–Pomerance p.483, Lenstra p.253 and Coppersmith p.177 were
visually checked. All these source bytes are sealed in the adjacent ledger.

Recorded failures: web-tool MIT Download returned Internal Error; a direct
CSAIL mirror fetch timed out although the web tool could open it; ePrint
2011/292 and the IACR CRYPTO 2006 PDF returned HTTP 403 to direct retrieval;
the IACR web open also failed. The author publication-page web fetch timed
out once. Rabin was recovered through MIT's discovered bitstream endpoint,
JLSV through the author's linked PDF, and the two-field selection check used
the inspected Prest–Zimmermann author PDF. The inaccessible Koo–Jo–Kwon
paper is not used for a theorem claim. A bounded search also encountered
secondary discussions of modular roots; none is used as primary evidence.
Nguyen's author landing page lacked an exposed downloadable paper link in
the web text; the publisher PDF was successfully archived and inspected.
