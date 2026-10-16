# Two prescribed orders of vector prefixes: unresolved target and proved method obstructions

Myeongjin Kang; no affiliation. 2026-10-16. Original prose CC BY 4.0;
original code MIT. Third-party material retains its own rights.

**Disposition: UNRESOLVED. No substantial theorem is nominated for review or
campaign counting.** The full target below is neither proved nor refuted.
The complete propositions in §§3–5 exclude three particular transfers of the
pinned one-order proof. They are technical supporting results, not substitutes
for the target. The computations are author checks, not independent reviews.

## 1. Original scope and bounded selection

The scope was fixed in `original-scope.md` at the choice point. The sole selected
target is T2:

> There exists an absolute finite C such that, for every d,N ≥ 1, every
> v_1,…,v_N ∈ R^d with ||v_i||_2 ≤ 1 and every pi,rho ∈ Sym([N]), there is one
> epsilon ∈ {−1,1}^N satisfying
>
>     max_{sigma ∈ {pi,rho}, 0 ≤ k ≤ N}
>         || Σ_{j=1}^k epsilon_{sigma(j)} v_{sigma(j)} ||_2 ≤ C sqrt(d).

There is no zero-sum, arithmetic, lower-norm, genericity, order-width,
displacement, finite-palette or commutativity hypothesis. The same sign belongs
to an index in both orders. No online or efficient algorithm is requested.
The conclusion must be independent of length. A bound growing with N is not a
resolution. The basis input v_i=e_i, N=d, forces C≥1, since every final signed
sum has norm sqrt(d).

This is a research question, not a claim of an established named frontier
problem or of newness to the literature. The bounded search did not establish
its status in all of vector-discrepancy literature. It is substantially
different in subject from every current campaign acceptance and the excluded
crossing-number and poly-Z_p packages.

The campaign's full r3 contribution veto was read, including its invariant
multiset Euler factors, finite characteristic quotient and discrete/pro-p
interface. Its TECHNICAL finding is binding here. The requested parent
`poly-zp-parent/contribution-r1-disposition.json` did not exist at the initial
read; the authoritative contribution review was used without waiting.
No further theorem in that family was attempted. The catalogue screen also
considered Foulkes stabilization and hyperbolicity-cone lift extensions, but
their strong companion coverage did not suggest a convincing new mechanism.
Neither was selected or used as a mathematical input.

## 2. The strongest source operations, and why they do not settle T2

The stipulated input is OpenAI's *The Euclidean Steinitz–Bergström theorem* at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Full pinned URLs, Git-blob checks,
labels and read extents are in `source-contracts.md` and the retrieval records.
Its truth is accepted; this report does not audit upstream truth.

The source's `thm:signing` gives precisely C_0 sqrt(d) for one prescribed order,
all dimensions and lengths, all unit-ball vectors, with one signing controlling
all its prefixes. Applying it twice produces two potentially different
signings. It gives no intersection theorem for their feasible-sign sets.

The stronger proof premises were inspected, not just this final theorem:

* `prop:adaptive` permits bounded adaptive shifts when a bounded symmetric
  convex coefficient body K satisfies lambda_Q(K) ≤ kappa² tr(Q) for **every**
  positive diagonal Q. Here kappa=1/100, delta=1/4; each coordinate is assigned
  once and its shift depends only on coordinates already assigned.
* `prop:filtered` provides a length-independent Dirichlet-energy bound for
  R_t x=C_t R_(t−1)x+b_t x_(d+t), with C_t invertible and
  C_t C_t^T+b_t b_t^T=I. Each new noise coordinate occurs for the first time
  at its own step. The matrices need not commute.
* The symmetric choice b_i=sigma v_i and
  C_i=I−eta_i b_i b_i^T, eta_i=(1+sqrt(1−||b_i||²))^(−1), has predictor
  m_i x=eta_i b_i^T R_(i−1)x^0, using the zero-initial-state part x^0.
  Every predictor column has squared norm at most sigma², by telescoping
  contraction loss. The slab-energy lemma pays for |m_i x|<delta.
* Adaptive coordinates x_(d+i)=epsilon_i+m_i x then cancel the contraction
  exactly, so R_t x=Σ_{i≤t} epsilon_i b_i at the chosen point with zero initial
  coordinates. The support of m_i in earlier coordinates is essential.

Gaussian correlation can combine survival constraints in one coefficient
space. This fact alone does not make the two feedback maps agree. Enlarging to
two independent copies permits unrelated occurrence signs. Identifying those
signs would be an additional constraint with no supplied energy estimate.
In particular, the scalar examples below satisfy the source's full
noncommuting/general-filter hypotheses; the difficulty cannot be repaired by
reciting their breadth.

The source's `cor:colorful-steinitz` already treats independently chosen row
permutations and synchronous aggregate prefixes, by Bárány transference. Its
permutations are outputs and entry signs may be independent in the signed
intermediate problem. T2 fixes two orders of the same indices and requires
identical signs at both occurrences. The colorful result is not T2.

The complete preprint tree was parsed and searched for Steinitz, Bergström,
prefix, signing and vector-balancing families. The sole other top-level match,
*Prefix Instructions and Incompressible Flows*, concerns fluid computation,
not a companion prefix-balancing theorem. No other companion with a T2
statement was identified. This is a bounded companion screen, not a worldwide
priority determination.

## 3. A shared coefficient vector cannot implement the two source feedbacks

**Proposition 1 (exact incompatibility of copied feedback).** Fix 0<c<1 and an
even N≥2. Give every scalar input the value v_i=1. Set b=sqrt(1−c²),
eta=(1+c)^(−1) and q=eta b²=1−c. Use the source's scalar filter in the identity
and reversed orders, with zero initial states. There are no real coefficients
x_1,…,x_N and common signs epsilon_i ∈ {−1,1} such that both filters restore
their signed increments by the source's own predictor-cancellation rule.

Proof. For the forward order let M be strictly lower triangular, with

    M_ij = q c^(i−1−j)       (i>j).

The filtered state before step i is b Σ_{j<i} c^(i−1−j)x_j. Cancellation is
therefore equivalent to x=epsilon+Mx. In reversed order the corresponding
matrix is M^T, so a common x and epsilon would imply (M−M^T)x=0.
Write M−M^T=q K, where

    K_ij = c^(i−j−1) if i>j,   −c^(j−i−1) if i<j,   0 if i=j.

Let S be the lower shift (S_(i,i−1)=1) and L=I−cS. Direct multiplication gives

    L K L^T = J,     J_(i,i−1)=1, J_(i−1,i)=−1,

with all other entries zero. For example, entries at distance at least two
cancel as c^(r−1)−c c^(r−2)−c c^r+c² c^(r−1)=0; adjacent entries equal one
and skew symmetry gives the upper half. The same computation covers boundary
rows. Since det L=1 and det J_N=det J_(N−2), with det J_0=1 and det J_1=0,
det K=1 for even N. Thus x=0, forcing epsilon=(I−M)x=0, a contradiction. ∎

This excludes only **sharing the corrected coefficient vector while copying
both predictors unchanged**. Separate coefficient vectors for the same signs
exist by triangular inversion. No impossibility of a different joint
construction is claimed. Indeed T2 for reversed orders follows immediately
from the one-order theorem: every reversed prefix is a difference of a total
sum and a forward prefix, hence has norm at most 2C_0 sqrt(d). For the scalar
even input in Proposition 1, alternating signs bound both orders by one.

## 4. Omitting feedback encounters a logarithmic spectral obstruction

We prove the analytic estimate used here in full; it is a standard nuclear-norm
factorization operation, not a proposed substantial advance.

**Lemma 2 (integration-by-parts factorization).** Let D ⊂ R^a be nonempty,
bounded and open. Let ell_1,…,ell_m be real linear forms with |ell_k(x)|<R on
D, where R>0. Choose m distinct coordinate indices i_1,…,i_m, and let B_kj
be the coefficient of x_(i_j) in ell_k. Then

    lambda_I(D) ≥ ||B||_*²/(4 m R²).                         (1)

Here lambda_I is the infimum of ∫||grad f||²/∫f² over nonzero H_0^1(D),
and ||.||_* is the sum of singular values.

Proof. Take real f ∈ C_c^infinity(D) with ∫f²=1. In the real Hilbert space
L²(D) put u_k=ell_k f and w_j=−2 partial_(i_j)f. Integration by parts gives

    <u_k,w_j> = −∫ell_k partial_(i_j)(f²) = B_kj.

Also Σ_k||u_k||² ≤ mR² and Σ_j||w_j||² ≤ 4∫||grad f||². For an orthogonal
m by m matrix O, Cauchy–Schwarz and orthogonality give

    |Σ_kj O_kj <u_k,w_j>|
       ≤ (Σ_j||Σ_k O_kj u_k||²)^(1/2) (Σ_j||w_j||²)^(1/2)
       = (Σ_k||u_k||²)^(1/2) (Σ_j||w_j||²)^(1/2).

Taking the maximum over O gives ||B||_* by finite-dimensional singular-value
decomposition. This proves (1) for smooth f; density in H_0^1 and passage to
the Rayleigh infimum prove the assertion. No minimax or assumed common
coordinate-energy witness is needed. ∎

**Proposition 3 (raw prefix bodies have excessive energy).** For N≥1 set

    D_(R,N) = {x ∈ R^N : |Σ_{i≤k}x_i|<R, 1≤k≤N}.

Then

    lambda_I(D_(R,N)) ≥ N log²(N+1)/(4 pi² R²).               (2)

Proof. This is a bounded open parallelepiped. The coefficient matrix is the
lower triangular all-ones matrix T_N. Its inverse is I−S. The symmetric
matrix (I−S)^T(I−S) has diagonal 2 except for its last entry 1, and adjacent
off-diagonal entries −1. Its eigenvalues are

    4 sin²((2j−1)pi/(4N+2)),     j=1,…,N.

To verify this directly, use eigenvector coordinates sin(i theta), 1≤i≤N,
with theta=(2j−1)pi/(2N+1). The first boundary is sin(0)=0; the last is
sin((N+1)theta)=sin(N theta). These N distinct eigenvalues exhaust the
symmetric N by N matrix. Thus the singular values of T_N are
1/[2 sin((2j−1)pi/(4N+2))]. This is also the explicit calculation in
Matoušek–Nikolov–Talwar, §4.1, Proposition 4.1 proof, not a newly discovered
spectrum. Using sin t≤t and Σ_{j≤N}(2j−1)^(−1) ≥ (1/2)log(N+1),

    ||T_N||_* ≥ (2N+1)/pi Σ_{j≤N} 1/(2j−1)
               ≥ N log(N+1)/pi.

Apply Lemma 2 with m=N. ∎

For any fixed R,H, (2) eventually contradicts lambda_I(D)≤H tr(I).
Intersecting a second raw prefix body only increases the Dirichlet eigenvalue.
Consequently the adaptive-sign proposition with zero shifts cannot be applied
to these raw bodies with a fixed length-independent dilation, even for ONE
order of identical scalar vectors. Alternating signs still solve that discrete
problem. Low Dirichlet energy is sufficient for signs, not necessary.
The argument does not contradict the source: its filters and adaptive shifts
are precisely what avoid this raw-body obstruction.

## 5. Keeping one filter and adding the other corrected prefixes also fails

A more serious attempt keeps the source's forward predictor, lets its single
adaptive choice produce epsilon=(I−M)x, and adds the desired second prefixes
as constraints on x. This avoids the incorrect demand Mx=M^T x. The following
estimate rules out a uniform diagonal-energy proof by that unchanged filter.

**Proposition 4 (odd-first crossed-prefix obstruction).** Fix c∈(0,1), R>0
and m≥1. Put N=2m and M_ij=(1−c)c^(i−1−j) for i>j, zero otherwise.
Let epsilon=(I−M)x as a linear expression in the noise coordinates x∈R^N.
Consider the second order

    rho = (1,3,…,2m−1, 2,4,…,2m).

Suppose D is any bounded nonempty open domain in R^(2m+s), s≥0, whose points
satisfy |Σ_{l=1}^k epsilon_(2l−1)|<R for every k≤m. Extra coordinates and
other constraints are permitted; the displayed forms ignore extra coordinates.
Then, writing [t]_+=max(t,0),

    lambda_I(D) ≥ m/[4R²(1+c)²]
          [log(m+1)/pi − c/(1−c²)]_+².                     (3)

Proof. Extract the coefficient on odd coordinate x_(2j−1) in the k-th
displayed form. It is zero if j>k. If j≤k it equals

    1−(1−c) Σ_{l=j+1}^k c^(2(l−j)−1)
      = (1+c^(2(k−j)+1))/(1+c).

Thus the m by m coefficient submatrix is B=(T_m+cG_m)/(1+c), with
G_m=(I−c² S_m)^(−1). Because
G_m=Σ_{r=0}^{m−1}c^(2r) S_m^r and ||S_m^r||_*=m−r,

    ||G_m||_* ≤ m/(1−c²).

The triangle inequality, the spectrum estimate from §4 and nonnegativity give

    ||B||_* ≥ m/(1+c) [log(m+1)/pi − c/(1−c²)]_+.

Lemma 2, using precisely these m noise coordinates, proves (3). ∎

For s=1, which is the scalar source's initial-state block, tr(I)=2m+1.
For every fixed c,R, the ratio lambda_I(D)/(2m+1) diverges. This applies to
the proposed intersection of the forward filtered body, small-predictor
slabs and corrected rho-prefix constraints, independently of the energy of
its first two parts. Every fixed source sigma>0 yields a fixed c<1, so making
sigma very small postpones the obstruction but cannot remove it. Allowing
sigma to tend to zero with N forfeits the source's length-independent
discrepancy constant through division by sigma.

Again the target is not refuted. For these exact two orders and v_i=1, take

    epsilon_(2j−1) = (−1)^(j−1),    epsilon_(2j)=−epsilon_(2j−1).

Every forward prefix is zero or ±1. The first half of rho has alternating
prefixes zero or one. If m is even, its sum is zero and the second half has
prefixes zero or −1. If m is odd, its sum is one and the second half has
prefixes zero or one. Both orders are bounded by one for every m.
The obstruction is to this sufficient variational route, not to existence of
a suitable signing. It survives the stronger source premises and is not a
failure caused by a large or noncommuting input family.

## 6. Primary antecedents and operation-level contribution assessment

Knuth's *Two-way rounding* (1995), initial lemma and complete flow proof, and
Theorem 3 statement, concern rounding real x_i to adjacent integers so that
**unweighted sums of rounding errors** in two orders stay within N/(N+1).
With x_i=1/2 this controls the common signing of identical scalar vectors.
For general vectors, coordinatewise application chooses different signs for
different coordinates. With scalar weights w_i, rounding w_i/2 gives error
y_i−w_i/2 with y_i∈{0,1}; desired signs instead give w_i(2z_i−1).
These are different increments unless the weights have the appropriate
special values. Splitting an index into independently rounded pieces loses
the requirement that all pieces use its one sign. Thus the flow theorem
cannot simply be applied coordinatewise or with weights substituted.

Reis's 2023 dissertation, *Vector Balancing and Integer Programming*, Chapter 8,
printed pp.120–124, was read in full at that extent. Its weighted discrepancy
definition is max_W disc(AW), W diagonal in [0,1]. Theorem 142 gives scalar
two-permutation examples tending to weighted discrepancy 2; Claim 143 proves
the relevant lower bound. This is an important stronger antecedent than
unweighted two-color pairing. It is not an unbounded lower bound and does not
refute T2. Its Conjecture 16 is a statement about arbitrary matrices; it is not
assumed true here. The statements read do not supply the desired Euclidean
two-order theorem. No exact optimal constant is proposed in this report.

Matoušek–Nikolov–Talwar, *Factorization Norms and Hereditary Discrepancy*,
arXiv:1408.1376v2, §2.1 Theorem 2.4 and §4.1 Proposition 4.1 proof, explicitly
supply the trace-norm lower bound and the exact triangular-matrix spectrum.
The integration-by-parts realization in §4 is a direct standard Hilbert
factorization combined with that calculation. Proposition 4 adds an explicit
geometric-series submatrix and a triangle inequality. Proposition 1 is
elementary triangular congruence. Even if these exact presentations are
new-to-source, none is asserted to overcome a nonroutine obstacle to T2.

Bérczi–Liu–Reis–Tarnawski, *Weighted Equitability and Matroid-Constrained
Discrepancy*, arXiv:2608.13983v1 (2026), Introduction through §1.1, was checked
as a recent primary comparison. Its prefix-constrained basis problem and
2-sparse prefix Beck–Fiala discussion have their own quantifiers; they are
not treated as solved by T2 or as equivalent to it. In particular its
weighted-carpooling counterexample is not a counterexample to T2. Its later
proofs were not read or used. This post-pinned external text is a literature
comparison only, not a stipulated mathematical premise.

The bounded searches used 23 query strings over eight batches, with substantial
noise from permutation metrics and ranking. No all-language or database-wide
priority audit was performed. Exact query strings and primary URLs are in
`literature-screen.md`. Non-primary snippets served only as discovery aids.
No source was found that licenses inferring simultaneous signs from separate
one-order existence, and no novelty certificate is inferred from that search.

## 7. Precise remaining task and scope accounting

Relabeling pi to the identity loses no generality. For B>0 define

    S_pi(B) = {epsilon∈{−1,1}^N:
                   max_k ||Σ_{j≤k}epsilon_(pi(j))v_(pi(j))||_2 ≤ B sqrt(d)}.

The pinned theorem proves S_pi(C_0) and S_rho(C_0) separately nonempty. The
unpaid step is a **length-independent intersection or a different coupled
construction** proving S_pi(C)∩S_rho(C) nonempty for some absolute C, with
all original dimensions, vectors and orders. No cardinality, coupling,
topological or correlation lower bound for that intersection has been proved.
Neither Gaussian correlation of continuous bodies nor a pair of marginal
sign distributions implies the discrete intersection.

Three natural sufficient constructions were investigated concretely:
unchanged shared feedback is algebraically inconsistent (§3); zero-feedback
raw bodies have too much energy (§4); retaining one source feedback and adding
the other corrected prefixes has too much energy (§5). The last failure holds
for a completely explicit permutation whose actual signs are easy. A future
proof must change the construction, rather than assume the false uniform
energy estimate for this body. These are method limitations only. No general
impossibility of joint filters or of T2 is asserted.

There is no scope switch. Reversed orders and the scalar odd-first example
are controls, not narrowed nominations. No infinite-dimensional extension,
many-order theorem, prescribed-cardinality rounding or algorithm is smuggled
into the claim. No Lean theorem is requested or claimed before a substantial
full proof exists. No external gate is commissioned here and none has passed.

## 8. Computations, provenance and replay

`checks.py` uses exact rational arithmetic. It checks the tridiagonal
congruence and determinant for 90 cases, the crossed submatrix for 80 cases,
18 inverse-Gram characteristic identities by polynomial interpolation, all
340 signings at N=2,4,6,8 for the feedback incompatibility, and the explicit
easy scalar controls for m=1,…,64. It also exactly minimizes two-order squared
discrepancy on 25 deterministic rational instances of lengths 4–12 and rejects
two deliberately incorrect matrix orientations. The rational vectors lie in
the Euclidean unit ball. These bounded computations establish no universal
upper bound, asymptotic lower bound, spectral integral inequality, novelty or
independent review. The general propositions are the written proofs above.

Input and output manifests bind SHA256 and byte size for every retained file.
The pinned retrieval also checks Git-blob SHA1 against the complete tree.
Third-party inputs and extraction/rendering copies are private and separated
from original output artifacts. `verify.py` authenticates the immutable
inventories and stored receipt **before** running checks, compares the fresh
stdout to the receipt byte-for-byte, and writes nothing. It does not reseal,
regenerate receipts or use the network. See `README.md` for the detached-seal
handoff and disposable-copy mutation tests.

This round ends with T2 unresolved. No new acceptance, increment, commit,
shared edit, external message, upload or submission is authorized or claimed.
