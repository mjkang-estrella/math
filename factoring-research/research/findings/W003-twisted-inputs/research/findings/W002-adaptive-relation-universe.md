# W002, Lens B — Residual recycling into an input-dependent coprime base

2026-10-08. **Constructive research submission; new deductions UNACCEPTED pending
independent review. Verified COMPLETE classical factoring improvement: NONE.**

**Selected realization:** multiplier-one continued-fraction residual recycling,
followed by an explicitly constructed composite coprime base and complete
finite-list dependency extraction. This genuinely changes the H026 universe:
the base consists of divisors obtained from the actual input's residuals, not
a permutation of its first-bit-length-prime alphabet. Its arithmetic generator
is already CFRAC, and coprime refinement is also established prior art.

**Outcome:** close this realization as a new uniform factoring mechanism.
For every composite input of the form `N=s^2+1` that reaches its relation phase,
the entire infinite stream has denominator 1. Every square dependency gives
only a global sign, so the extractor fails for **every** finite cap. This is an
actual arithmetic failure, not merely a missing smoothness estimate. The
short-period issue is already identified by Morrison–Brillhart. The adaptive
base does not repair it. No conclusion about other multipliers, adaptive
generators, Schnorr lattices, or factoring hardness follows.

## 1. Scope, inputs, and the alternatives considered

The frozen brief is `research/hypotheses/W002.md`, SHA-256
`5f34c276110ba4ad79781b16b4a86d7ea3860671d168939aca9c399b0480f723`.
The archived bytes matched the supplied identity. I read AGENTS.md, README.md,
docs/SPECIFICATION.md, RESEARCH_LOOP.md, RESEARCH_TEAM.md, STATE, W001 synthesis,
the W001 relation/baseline reports, H021/H024–H027 dispositions, relevant
sections of the corrected H027/H028/H031 reports, their dispositions, and
H027's root-entropy prior-art note. H030's disposition and H031's **completed**
disposition were read; neither was treated as a live review. The stale H031
status in the archived W001 synthesis is superseded by the disposition and
handoff. No sibling W002 report was opened, and no task was delegated.

The input snapshots and their identities are in
[W002-adaptive-inputs.json](W002-adaptive-inputs.json) and the adjacent
`W002-adaptive-inputs/` directory. Primary-source bytes, retrieval failures,
origins of reused archives, and hashes are recorded in
[W002-adaptive-retrieval.json](W002-adaptive-retrieval.json).

Three concrete alternatives were considered before selecting one:

1. Choose primes using quadratic-residue tests and solve congruences to force
   known divisors of near-square values. This is costable, but H027 C already
   supplies the relevant CRT/QS realization. Merely changing its prime menu
   supplies no new norm-size or useful-yield theorem.
2. Admit residuals themselves as new composite base elements, using gcds to
   separate shared factors instead of factoring each residual into primes.
   This is genuinely input-dependent, but base construction alone changes
   representation. W001 B already records the fixed-list square-kernel
   invariant. A materially different arithmetic source must be specified.
3. Recycle a residual as the next exact divisor in a quadratic-irrational
   recurrence. This supplies the new source in item 2 without root search,
   hard residual factorization, or a smoothness oracle. Developing the
   recurrence identifies it with known CFRAC. This is the selected source.

The objective is a charged arithmetic escape from H026, not an escape by
terminology. H026 does not imply anything about the success of this source.
H028's multiple-field cost model and H031's rotation law are not imported.

## 2. A finite, entirely N-only generator and extractor

The following is an on-paper finite program, **not an implemented solver**.
It returns a verified proper factor or the explicit status `FAIL(H)`.

### 2.1 Constructed parameters and elementary cases

Let `n=bit_length(N)`. Check even inputs and perfect powers first. Integer
roots by binary search, trying exponents `2,...,n`, suffice for a polynomial
bit-cost perfect-power test; return the root when `N=a^b`, `a>1,b>1`.
The remaining promised composite is odd, nonsquare and at least 15.
For a general recursive factorer, primality testing is a separate paid step;
this unsuccessful trial is not asserted to provide the required splitter.

Set, using integer comparisons only,

    s = floor(sqrt(N)),
    k = least positive integer with 2^k >= n+1,
    e = least positive integer with e^2 >= n*k,
    H = 2^e.                                                   (2.1)

These parameters require polynomial bit work to construct. Writing the binary
integer H costs `O(e)` bits; **running H steps costs H**, not `O(e)`.
There are no selected primes, lattice weights, precomputed tables, input
family labels, random tapes, or unknown periods. Multiplier 1 is fixed.

### 2.2 Exact residual recycling

Initialize

    m_0=0, d_0=1, a_0=s,
    X_{-2}=0, X_{-1}=1.

For `i=0,...,H-1`, in this order, compute

    X_i     = (a_i X_{i-1} + X_{i-2}) mod N,
    m_{i+1} = a_i d_i - m_i,
    d_{i+1} = (N-m_{i+1}^2)/d_i,
    a_{i+1} = floor((s+m_{i+1})/d_{i+1}),
    r_i     = (-1)^(i+1) d_{i+1}.                              (2.2)

The division defining `d_{i+1}` is exact. Compute `gcd(d_{i+1},N)`:
a proper gcd finishes successfully; gcd N is never called a factor or unit
and would end this trial unsuccessfully; gcd 1 retains the record
`(original index i, X_i, sign(r_i), |r_i|)`.
In the nonexceptional domain below `d_{i+1}<N`, so the full-gcd branch is
unreachable, but its interpretation is explicit.

The ordinary convergent identity, with unreduced numerator `A_i` and
denominator `B_i` used **only in the proof**, is

    A_i^2 - N B_i^2 = (-1)^(i+1) d_{i+1},
    X_i = A_i mod N.

Consequently every retained row gives the exact congruence

    X_i^2 = r_i (mod N).                                      (2.3)

Neither `A_i` nor `B_i` is materialized. Those integers can become very large;
the modular numerator recurrence is the actual implementation. This detail
is already explicit in Morrison–Brillhart, §§2–3, equations (1), (5), (8).
[Primary paper](https://www.ams.org/journals/mcom/1975-29-129/S0025-5718-1975-0371800-5/S0025-5718-1975-0371800-5.pdf).

For completeness the width guarantee is structural, not probabilistic.
Writing the complete quotient as `alpha_i=(sqrt(N)+m_i)/d_i`, (2.2) is the
usual exact update `alpha_{i+1}=1/(alpha_i-a_i)`. At `i=1` its conjugate is
`-1/(sqrt(N)+s)`; thereafter conjugates remain in `(-1,0)` and
`alpha_i>1`. Thus `d_i=2sqrt(N)/(alpha_i-alpha_i')<2sqrt(N)`, and
`|m_i|<sqrt(N)`. The floors using s equal the floors using sqrt(N), since
the discarded fractional part is less than 1 and the other operands are
integers. Divisibility propagates from `d_i | N-m_i^2` and
`m_{i+1}=-m_i mod d_i`. These observations justify exact division and
`O(n)`-bit state. The same bounds appear in the primary paper's Remark 3.2.

This is a real size advantage over N-sized random-square residues, but it is
the established continued-fraction advantage. It is not a new improvement
over CFRAC/QS. Nor does `|r_i|<2sqrt(N)` certify smoothness.

### 2.3 Construct the adaptive composite base without factoring residuals

If no factor was found, keep all H original records. Duplicate norms and
duplicate parity rows are paid records, not H distinct useful relations.
In particular, equal norms with different X values are retained: those
roots might be productive. No period or duplicate-label shortcut discards them.

Start with the distinct integers `|r_i|>1`, with row decompositions, and use
the following elementary refinement; it makes the algorithm self-contained.
While two distinct current base integers a,b have `g=gcd(a,b)>1`, replace
them by the nonunit integers in `g,a/g,b/g`, merging equal integers. In every
row replace the old powers using `a=g(a/g), b=g(b/g)` and combine powers
of equal new elements. Use increasing integer order to choose the first
overlapping pair and fixed sequential scans. Continue until all distinct
base integers are pairwise coprime. The resulting base is `c_1,...,c_t>1`,
and the stored exact decompositions are

    |r_i| = product_j c_j^(v_ij),  v_ij >= 0.                 (2.4)

All base elements are divisors of supplied residuals. They are obtained only
by gcd and exact division, and are units modulo N. They need not be prime,
squarefree, or primitive perfect powers. No prime factors of a hard residual
are requested. Empty base and residual 1 are allowed.

Termination has a simple charged potential: the sum of binary logarithms of
the distinct current base elements drops by at least 1 at each overlapping
pair replacement. Before merging coincidences the product of new entries
is `ab/g`, and merging only decreases it further. Initially this sum is
at most `S=sum_i bit_length(|r_i|)<=H(n+1)`. There are at most S refinement
steps and at most S base entries at any time. The decompositions are part
of the state and must be updated; the potential is not a free factor oracle.

Test each c_j for being an exact square by integer square root and squaring
back. Save its square root when it is a square. A nonsquare composite c_j
is left composite. Include the sign column and one parity column for each
nonsquare c_j; its row entry is `v_ij mod 2`. Square c_j need no parity
column, but their full exponents and roots remain stored for recovery.

This refinement is an intentionally elementary realization of a known
primitive. Bernstein's Algorithms 18.1 and 21.2 give much faster coprime-base
construction and full decompositions, with cost in aggregate input bits.
No near-linear bound is assigned to the sequential pair scans specified here.
[Bernstein, archived 2004 manuscript / 2005 journal paper](https://cr.yp.to/lineartime/dcba-20040404.pdf).

### 2.4 Exact dependencies and paid extraction

Let K be the kernel over F_2 of the transpose of this signed row matrix.
Compute a basis of K by dense elimination with row provenance and fixed
pivots. Process **every basis vector**, until a proper factor is found.

For each selected subset E of rows compute

    X(E) = product_(i in E) X_i mod N,
    V_j(E) = sum_(i in E) v_ij,
    Y(E) = product_(c_j nonsquare) c_j^(V_j(E)/2)
           * product_(c_j square) sqrt(c_j)^(V_j(E)) mod N.   (2.5)

The sign sum and nonsquare exponents are even. Powers are modular binary
powers. Verify `X(E)^2=Y(E)^2 mod N` and test both `gcd(X(E)-Y(E),N)` and
`gcd(X(E)+Y(E),N)`. Return only a divisor strictly between 1 and N.
After all basis vectors fail, return `FAIL(H)` with the finite-list certificate.
No random dependencies or restarts are used.

## 3. What the construction does, and what it does not create

The following finite-list deductions are supplied for independent review;
none is labeled a newly accepted theorem or a novelty claim.

**Exact square-kernel invariant.** A product of selected signed residuals is
a positive integer square if and only if its parity vector vanishes in the
constructed matrix. Necessity for a nonsquare c_j uses any prime having odd
valuation in c_j; coprimality keeps that prime out of every other base element.
Sufficiency follows from (2.5) and even sign. This proof uses prime
factorization as mathematics, never as an algorithmic input. It is the same
fixed-list invariant already observed in W001 B. Refinement preserves all
square dependencies that full prime factorization would reveal; it creates
none on the same list.

In particular, a nonsquare base element appearing to odd power in just one
remaining row forces that row's coefficient to zero in every dependency.
Iterated singleton removal is valid for the current list, but old rows cannot
be thrown away permanently if later rows are to be added. This implementation
keeps them all. Conversely, many dependencies need not be productive.

**Why testing a kernel basis is sufficient for the fixed list.** All r_i and
X_i are units. For E in K, use the positive integer square root before modular
reduction to define

    z(E)=X(E)/sqrt(product_(i in E) r_i) mod N,
    R_N={z in (Z/NZ)^*: z^2=1},
    phi(E)=[z(E)] in R_N/{+1,-1}.                           (3.1)

Then phi is a homomorphism. For E,F in K, cancelling the overlap in their
products gives

    z(E) z(F) / z(E xor F)
       = product_(i in E intersect F) sign(r_i) in {+1,-1}.

**The quotient by global sign matters:** for signed relations z itself need
not be a homomorphism. No missing sign is dropped in (3.1).
If all basis vectors have trivial phi, every dependency has trivial phi.
If any dependency has nontrivial phi, at least one tested basis vector does.
For odd N, a nontrivial class yields a proper gcd: the two gcds of z-1 and
z+1 with N have product N and are coprime, since their common divisor divides
2. A global sign yields only trivial gcds. This proves the asserted finite-list
certificate, without assuming a productive dependency exists.

If one instead sampled uniformly from K, its exact productive fraction would
be `1-1/|image(phi)|`. For a distinct odd semiprime it is zero or one-half.
This is an identity about already-generated data, not a generation or root-
independence law. The actual algorithm tests the basis deterministically.
Inverses in (3.1) explain the proof; the implementation (2.5) needs none.

**Why H026's particular counting proof does not apply.** The new alphabet
is constructed from d_i(N), potentially containing primes outside the first
n primes, with magnitude up to `2sqrt(N)`. Neither these integer generators
nor their decompositions are the fixed aligned prime/weight/energy universe
of H026. Even the unrefined first residual `N-floor(sqrt(N))^2` varies with N.
A label `(N,i)` is not the escape; the actual computed integer and admissible
prime support change. A common universe obtained by including all such
residuals would require a new cardinality/width argument. This establishes
only the failure of that specific containment premise, not useful yield.

## 4. Full cost of the selected finite procedure

Let h be the number of attempted recurrence steps; `h<=H`, with `h=H` on
the no-factor branch. Let `w=n+ceil(log_2(H+1))+2`. Schoolbook arithmetic,
binary-search roots, and Euclid give polynomial bit work in w per bounded-
width scalar operation. The following conservative ledger includes sequential
memory movement and does not invoke a word-RAM with free large indices.

- Parameter construction and elementary input processing cost `poly(n)`.
  Recurrence generation, exact divisions, gcds, and writing all records cost
  `(h+1)poly(w)`. Scalar arithmetic operands have `O(n)` bits; indices have
  `O(log H)` bits. No exponentially long exact convergent is present.
- With `S<=h(n+1)`, at most S refinement steps each scan at most `S^2`
  pairs for gcd. Updating and merging full decomposition records costs at
  most another `S*h*poly(w)` per step. Integer values remain `O(n)` bits;
  individual row exponents are at most `O(n)`. Thus all elementary refinement
  and data movement fit `(S+1)^3 poly(w)`. Discarded duplicates and unhelpful
  factors are paid. This is an upper bound, not an assertion that each input
  requires that much work.
- Square tests, column labeling, signs, and dense matrix assembly are charged.
  The matrix has at most h rows and `S+1` columns. Elimination, full kernel
  basis/provenance storage, and sequential pivot scans cost
  `O((h+1)^2(S+h+1) poly(w))`. No favorable sparse core or rank is presumed.
- There are at most h basis dependencies. For each, summing the stored full
  exponents, all modular powers/products, checking the square congruence,
  and both gcds fit `(h+1)(S+1)poly(w)` conservatively. Aggregate exponents
  are at most `O(hn)` and have `O(log(hn+1))` bits. The huge integer product
  of residuals is never built. Integer roots were computed only for individual
  base elements of `O(n)` bits.
- A safe full working/retained memory bound is `(h+1)^2 poly(w)` bits,
  including a dense decomposition matrix, parity matrix, kernel basis and
  original record identities. Repeated sequential scans are included above.
  There is no once-per-size or once-per-input uncharged factory.

The resulting bound is

    T_trial <= (H+1)^3 poly(n+log H),
    memory  <= (H+1)^2 poly(n+log H).                         (4.1)

For (2.1), `H=L_N[1/2,1]`, because
`log H ~ sqrt(log N log log N)` with natural logarithms. Hence (4.1) is an
upper envelope `L_N[1/2,3]` for a finite trial, with an `L_N[1/2,2]` memory
envelope. It is **not** a successful factoring bound. On the failure family
below a much cheaper execution is possible; the envelope is not a lower bound.

Known fast coprime refinement could replace the cubic refinement term by
essentially linear aggregate-bit work, paying product-tree widths as large
as the aggregate bit mass. Dense dependency work and all root/gcd recovery
would still remain. A sparse replacement must specify its actual matrix
dimensions, fill, verification and reconstruction. None can change the exact
failure below while leaving the relation source unchanged.

Repeating this deterministic trial on N repeats the same data. There is no
justification for a positive independent-trial success probability or a
restart quotient. Appending exhaustive trial division would provide a known
complete fallback at its full cost; it would not establish this mechanism's
improvement and is not part of the selected realization.

## 5. Decisive symbolic falsifier: complete failure on period-one inputs

Take any integer `s>=2` for which `N=s^2+1` is an odd composite entering the
relation phase. Since `floor(sqrt(N))=s`, (2.2) gives

    m_1=s, d_1=1, a_1=2s;
    m_i=s, d_i=1, a_i=2s for every i>=1.                     (5.1)

There is no finite numerical computation in this argument: substitute these
symbols into the recurrence and induct. Every residual is consequently

    r_i=(-1)^(i+1).

Since `s^2=-1 mod N`, induction in the modular numerator recurrence gives

    X_i=s^(i+1) mod N.                                      (5.2)

The adaptive positive base is empty. The signed parity matrix has only its
sign column and, for any cap H>=1, rank 1 and nullity H-1. Thus this is not
an example with insufficient raw relations or no dependencies.

A selected subset E is a square dependency precisely when
`sum_(i in E)(i+1)` is even. Its positive integer square root is 1, and (5.2)
then gives `X(E)=+1 or -1 mod N`. Both gcds are trivial. All input gcds are
also trivial since every d_i is 1. Therefore

    image(phi)={1}, and the algorithm returns FAIL(H)
    for every cap H on every such composite N.              (5.3)

There are infinitely many inputs satisfying the selected preprocessing:
take `s=50t+2` for any positive integer t. Then N is odd, exceeds 5, and
`N=5 mod 25`, so it is composite with `v_5(N)=1` and cannot be a perfect
power. This symbolic congruence verifies the family without a factor oracle
inside the generator or a finite experiment.

The small factor 5 makes this example easy for other algorithms; no hardness
claim is made. Nor is the phenomenon confined to 5: for any **fixed finite**
trial-prime set P, choose a prime `q=1 mod 4` outside P, choose a root r of
-1 modulo q, and choose a lift `r+jq` that is not a root modulo q^2. CRT with
`s=0 mod 2*product_(p in P) p` gives an infinite progression of even s with
`gcd(s^2+1,product P)=1` and `v_q(s^2+1)=1`. Every sufficiently large member
is a non-perfect-power composite with the same (5.1)–(5.3) failure. This is an
existence argument for counterexamples after a fixed finite prime screen;
it makes **no** claim about every size-dependent prime cutoff, balanced
semiprimes, efficient hard-instance generation, or arbitrary preprocessors.

Morrison–Brillhart Remark 3.5 already explains the need to change the
multiplier when the continued fraction has too short a period, including
`sqrt(g^2+1)=[g; overline(2g)]`. The contribution of (5.1)–(5.3) here is to
spell out why admitting all residuals and using an adaptive coprime base
cannot repair that known failure. It is not a new CFRAC impossibility theorem.

The narrow useful-yield statement required by this exact deterministic
extractor is now explicit:

    For the generated H-prefix, either an early proper gcd occurs,
    or the actual map phi on its signed square kernel is nontrivial.       (Y)

(Y) is sufficient, because the algorithm tests a kernel basis. It is false
uniformly, by (5.3), even with unlimited H. Asking for more smoothness, more
rows, or more nullity cannot fix it: this family has perfect smoothness and
arbitrarily large nullity. A new multiplier law would change the algorithm
and must pay for all attempted multipliers and prove its own useful yield.

## 6. Prior art and the correct comparison

This is a targeted primary-source comparison, not an exhaustive novelty
survey or a proof audit of every cited algorithm.

**CFRAC.** Morrison–Brillhart, *A Method of Factoring and the Factorization
of F7*, Mathematics of Computation 29 (1975), 183–205, supplies the exact
continued-fraction relations, modular-only numerator computation, small
denominator bound, parity/provenance processing, factor recovery, and the
short-period/multiplier limitation used here. Sections 2–3 and Remark 3.5
were inspected in the archived full PDF/text. The selected generator is
within that known mechanism. Adaptive composite decomposition is the changed
processor; it is not a new source of smaller norms.

**Coprime bases.** Bernstein, *Factoring into coprimes in essentially linear
time*, Journal of Algorithms 54 (2005), 1–30, manuscript dated 2004-04-04,
permanent ID `f32943f0bb67a9317d4021513f9eee5a`, gives the established faster
replacement for the elementary refinement. Sections 1–2, 16–18 and 21 were
checked. W001 B already records its relevance to integer square relations.
It removes an individual-prime-factorization requirement, not the need for
useful square dependencies.

**QS.** Pomerance, *Smooth numbers and the quadratic sieve* (2008), pp. 73–80,
distinguishes structured-value smoothness heuristics from proved smooth-number
counts and includes the matrix charge. Its conventional heuristic complete
model is `L_N[1/2,1]` with sparse linear algebra. Near-square norm size is
already its mechanism; dense elimination can worsen the model. No result
here beats that baseline. [Primary chapter](https://math.dartmouth.edu/~carlp/PDF/qs08.pdf).

**A precise surrogate, not the law of our generator.** Balister–Bollobás–Morris
Theorem 1.1 concerns independent uniform integers in `{1,...,X}`, sampled
with replacement. Its square-subset threshold is `(exp(-gamma)+o(1)) J(X)`,
where `J(X)=min_y pi(y) X/Psi(X,y)` and
`log J(X)~sqrt(2 log X log log X)`. At `X=floor(2sqrt(N))` that is
`L_N[1/2,1]` samples. Thus admitting all composite residuals does not lower
the leading **square-availability** threshold in that exact random-integer
law, even with free postprocessing. Continued-fraction residuals are
correlated and periodic; that theorem is not their distribution, an
expected factoring bound, or a lower bound on this actual arithmetic source.
[Primary paper, pp. 50–52](https://annals.math.princeton.edu/wp-content/uploads/annals-v188-n1-p02-p.pdf).

No smoothness heuristic is needed for the conclusion of this report: (Y) is
disproved for the actual generator. In particular I do not optimize a supposed
successful-time model by silently replacing this source with the independent
uniform surrogate or by granting productive-root randomness. For the actual
law on fixed N there are no random choices, and on (5.3) the success mass is
exactly zero. There is therefore no finite full-cost heuristic consequence
of this realization to promote against QS or NFS.

**NFS and rigorous factoring.** Coppersmith's *Modifications to the Number
Field Sieve* (1993), pp. 169–170 and §3, describes heuristic general NFS and
the multiple-field improvement, with cold constant approximately 1.902
instead of ordinary GNFS's approximately 1.923 at exponent 1/3. His separate
amortized precomputation claim is not the cold baseline. Neither follows
from the present norm generator. Lee–Venkatesan's square-congruence theorem
and their conditional productive Blum-semiprime result retain their actual
law and character hypothesis, as recorded in accepted H031. The rigorous
complete baseline `L_N[1/2,1]` is separately supplied by Lenstra–Pomerance;
their primary theorem on p. 483 was inspected as an archived page image.
[Coppersmith](https://link.springer.com/content/pdf/10.1007/BF00198464.pdf),
[Lee–Venkatesan v1](https://arxiv.org/html/1805.08873v1),
[Lenstra–Pomerance](https://math.dartmouth.edu/~carlp/PDF/paper85.pdf).

**Schnorr-type relation lattices.** Vera's primary research paper,
*A Note on Integer Factorization Using Lattices*, arXiv:1003.5461v1,
§§1–2 and Figure 1, sets out the fixed-prime smooth-product/close-vector
relation search and derives sufficient norm conditions. Those conditions
do not provide a supply theorem for this residual recurrence or adaptive
alphabet. This report neither labels generic CVP hard as a proof about the
prime-number lattice nor assumes a short-vector oracle. The requested
Schnorr 2021 corrected ePrint PDF was blocked with HTTP 403 in both retrieval
interfaces; its indexed abstract was not treated as checked full text.
Comparison is limited to the mechanism explicitly available in Vera's
archived primary paper. [Vera v1](https://arxiv.org/abs/1003.5461v1).

## 7. Handoff and evidence limitations

**Strongest supported conclusion:** there is an explicit N-only residual
recurrence, exact adaptive composite-base construction, finite-list square
kernel, and fully charged deterministic extractor. The input-dependent
arithmetic escapes H026's fixed-universe premise. It recovers known CFRAC
relations and known coprime processing. The exact period-one family refutes
its uniform useful-yield requirement even though it supplies arbitrarily
many smooth formal dependencies. These submitted deductions remain
UNACCEPTED until the coordinator's independent review.

**Exact limitation:** only multiplier-one residual recycling and the retained
relation interface above are closed. A different generator, a paid multiplier
selector, an actual structured norm law, or additional arithmetic operations
may behave differently. Neither H026 nor this report is a factoring lower
bound. The finite cost envelope is not a bound for complete factoring.

**Next proof/test:** none selected. A larger cap or a gcd-basis implementation
cannot falsify the symbolic failure; changing multipliers is already part
of CFRAC and would need a new justified advantage before another task.
Independent review of this report is the coordinator's decision, not a
recursively launched review or a new proposed mathematical test.

No numerical experiment, corpus, benchmark, parameter sweep, implementation,
Lean change, package installation, shared-file edit, commit, publication,
outside-project write or scheduler occurred. Executed data processing was
limited to document discovery/reading, primary-source retrieval, text
extraction, archival copying and hashing. Source limitations are preserved:
one web Bernstein-index request returned 502 before successful direct
retrieval; both Schnorr PDF attempts returned 403; the Lenstra–Pomerance PDF
has no useful text layer, so its archived theorem image was used. No missing
page or blocked proof was inferred from a search snippet. Existing primary
archives are identified as copies, not fresh network retrievals.

The delivery seal is [W002-adaptive-delivery.sha256](W002-adaptive-delivery.sha256).
All owned writes match this report or the `W002-adaptive-*` support prefix.
**Verified COMPLETE classical factoring complexity improvement remains NONE.**
