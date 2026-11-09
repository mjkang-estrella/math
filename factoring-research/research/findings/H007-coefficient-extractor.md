# H007 — Audit of scalar-normalized Delannoy transfer blocks

Date: 2026-10-08 UTC / 2026-10-07 America/Los_Angeles.

**Verified improvement: NONE. Disposition: reject this restricted route as an
asymptotic improvement.** A correct factor-or-action block is supplied below.
Its apparent binary recursion does not have bounded polynomial state; its
factor-return branch reduces to consecutive-integer product factoring. A
different, executable series-Newton revision avoids nonunit denominators but
retains linear-in-index coefficient storage. These are draft mathematical
arguments and a finite diagnostic, pending independent review, not a new
general factoring theorem.

Read in full: AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md, research/STATE.md, and research/hypotheses/W001-algebra.md,
including Card A and the recommended next step. The user-assigned scope
overrides the general shared-harness workflow: only this report and adjacent
H007-coefficient-* evidence files are owned. No delegation, packages, solver,
Lean, STATE, original-report, publication, scheduling, or commit changes.

## 1. The one restricted route and its explicit formula

Let n=bitlength(N), R=Z/NZ, and d_j=[X^j](X+1)^j(X+2)^j. Thus d_0=1,
d_1=3, and, for k>=1,

    (k+1)d_(k+1) = (6k+3)d_k - k d_(k-1).

Use v_k=(d_k,d_(k-1))^T. One may start at v_0=(1,0)^T: the second
component is auxiliary and the transition at zero discards it. Define

    U(x) = [[6x+3, -x], [x+1, 0]],
    T_L(x) = U(x+L-1) ... U(x),
    D_L(x) = (x+1)(x+2)...(x+L).

Over Q, the exact transfer is

    v_(a+L) = T_L(a) v_a / D_L(a).                       (1)

The chosen representation stores the four entries of T_L and D_L as dense
univariate polynomials, with an optional common scalar polynomial cancelled.
It is not an arbitrary index-dependent program, a matrix change of basis, or
a conjectured compressed representation. Its genuine doubling identities are

    T_(2L)(x) = T_L(x+L) T_L(x),
    D_(2L)(x) = D_L(x+L) D_L(x),                         (2)
    T_(2L+1)(x) = U(x+2L) T_L(x+L) T_L(x),
    D_(2L+1)(x) = (x+2L+1) D_L(x+L) D_L(x).

These identities derive by splitting the ordered products, so no coefficient
oracle appears. At a numerical x, evaluating both halves recursively has L
leaves, despite logarithmic depth. Reusing the symbolic half requires storing
and shifting its polynomial entries, whose degrees grow with L.

### A total factor-or-action implementation across nonunits

Assume 0<=a<a+L<N. Compute T_L(a), D_L(a) modulo N by a product tree and
g=gcd(D_L(a),N).

1. If g=1, return D_L(a)^(-1) T_L(a) v_a modulo N. Extended gcd supplies
   the inverse only after the unit test.
2. If 1<g<N, return g, already a verified proper factor.
3. If g=N, descend a scalar product tree for a+1,...,a+L. At a node with
   gcd N, inspect its left child: a proper gcd finishes; gcd N descends left;
   gcd 1 descends right (whose gcd is then N). A leaf j<N cannot have gcd
   N. Thus a proper gcd is eventually found. A tree reconstructed for this
   one bad block costs O(L) modular multiplications and O(log L) further
   gcds, or O(L) gcds if implemented as a simple complete scan.

This is a valid action-or-factor primitive. It deliberately **does not return
the action after returning a factor**. Computing the scalar denominator is
charged, and a gcd equal to N alone is not accepted as success. No prime
characteristic, factors, or auxiliary roots are supplied to this implementation.

## 2. Representation-specific obstruction

### No symbolic scalar cancellation

For every L>=1,

    gcd_Q[x](D_L, all four entries of T_L) = 1.          (3)

Proof: D_L has the distinct roots -j, 1<=j<=L. At x=-j, the integer
arguments of the matrices range from -j to L-j-1. Since
det U(k)=k(k+1), all factors are invertible over Q except those at -1 and
possibly 0. For j=L, U(-1) is a nonzero rank-one matrix with invertible
factors on its right. For j<L, the singular adjacent pair is

    U(0) U(-1) = [[-9,3],[-3,1]],

also nonzero, with invertible factors on either side. Therefore T_L(-j)
is not the zero matrix at any root of D_L. Each linear factor of D_L
remains in the common denominator of the rational transfer matrix.

Consequently the minimal scalar polynomial denominator in this representation
has degree L. Also, the leading coefficient matrix of T_L is V^L, where
V=[[6,-1],[1,0]] and det V=1, so its matrix degree is exactly L even after
reduction modulo N. Dense state therefore uses Theta(L) ring slots, or
Theta(L n) bits with fixed-width residues. Doubling L doubles that state;
it does not give O(poly(n)) state for L comparable to N.

This is **not** a lower bound for all Delannoy coefficient algorithms.
Specialization x=0, followed by applying the canonical initial vector, can
cancel the entire denominator over the integers. Matrix-valued gauges,
other representations, special identities for that vector, and arbitrary
modulus-dependent programs are outside (3). A product notation or a circuit
with unevaluated shift operators is not an O(log L) evaluation algorithm.

### Residue-only state loses information at a nonunit

Let r be a prime divisor of N and consider the single transition at k=r-1.
Starting from any integer pair (u,v) with integral next value, replace it by
(u,v+N). The input pair modulo N is unchanged. The first output changes by

    -(r-1)N/r,                                         (4)

an integer that is nonzero modulo N. Both pairs have integral next values;
the second output is u in each case. In particular one may take
(u,v)=(d_(r-1),d_(r-2)). Thus there is no universal map from just the two
input residues to the exact reduced action on all such integral lifts.
This explains the obstruction to silently dividing a zero divisor. It does
not show the canonical Delannoy sequence cannot be computed another way.

The factor-or-action contract escapes (4) by returning gcd(r,N); finding the
relevant r without scanning or a charged interval product remains work.

### Exact quotient lifting is correct but does not bypass widths

There is an explicit way to evaluate an integrally divisible numerator:
let D=D_L(a)>0, take the initial vector modulo ND, and compute

    w = T_L(a) v_a mod ND, with 0<=w_i<ND;
    output w_i / D mod N.                              (5)

If the exact numerator is divisible by D, each representative w_i is too,
and (5) is the desired quotient modulo N. However, knowing v_a modulo N
does not supply v_a modulo ND. Even with v_0 exactly known, the modulus
has n+log2(D) bits. For an initial block D=L!, this is
Theta(n+L log L); a block near index a has log D=O(L log(a+L)). In
particular L comparable to N costs exponentially many bits in n before
the quotient is taken. Computing a gcd of exact integer entries and D
after materializing them cannot refund that construction cost. We do not
assert that every specialized, fully reduced rational denominator is large.

Already 3^j<=d_j<=6^j follows from the positive Laurent polynomial
3+X+2/X: d_j is its constant coefficient, its constant-only term is 3^j,
and its sum of coefficients is 6^j. Thus exact d_j itself has Theta(j)
bits. Exact numerator methods are not cheap merely because the final
residue has n bits.

## 3. Fully charged costs and prior-art comparison

Let M(n) be n-bit multiplication cost, G(n)=O(M(n) log n) an extended-gcd
bound, and P_R(s)=soft-O(s M(n)) a conservative bound for multiplication of
degree-O(s) polynomials over R. Soft-O suppresses logarithms of the index
and bit length, not powers of N. Coefficients reduce after every arithmetic
operation; elementary scalar products use O(n)-bit temporaries. Fast
polynomial multiplication packs or processes O(s n) bits and is charged
through P_R, not as one n-bit operation.

**Literal block evaluator used in the diagnostic.** Constructing a block
numerically takes O(L) matrix and scalar modular multiplications, one gcd,
and at most O(L) extra products/O(log L) gcds for the gcd=N branch.
Thus its bit cost is O(L M(n)+G(n) log(2L)); an explicitly retained scalar
tree costs O(L n) bits. The diagnostic additionally computes exact references
and lifted moduli; those are identified separately and are not free solver
inputs. Scanning to the first prime divisor p costs O(p M(n)+p G(n)) with
single-step gcds, at worst soft-O(N^(1/2) M(n)).

**Dense polynomial batching.** To cover H consecutive transitions, choose
block length B and K=ceil(H/B). Build T_B(x),D_B(x) by product trees,
then evaluate them at 0,B,...,(K-1)B using monic remainder trees. The last
partial block may be built directly in O(B) operations. Monic division
does not require unknown field inverses. The cost is

    soft-O((B+K) M(n)) + O(K G(n)),
    space soft-O((B+K)n).                              (6)

This includes polynomial construction, multipoint evaluation, all K gcds
and successful inverse checks, K matrix-vector actions, and reconstruction
of one bad scalar block in O(B) work. Interpolation at consecutive points
is not used: factorial inverses in such an implementation would need
additional checks. In this explicitly dense, all-block scheme the stored
degree-B polynomial and K outputs alone take Omega(B+K) slots; minimizing
B+H/B gives the square-root-in-H scale, not polylogarithmic cost.

For an action computation to m=(N-1)/2, (6) has soft-O(N^(1/2) M(n))
cost. For the permitted factor-or-action objective on an odd composite,
stop the interval search at H=floor(sqrt(N)): a prime divisor is guaranteed
in [2,H]. Choosing B near sqrt(H) gives soft-O(N^(1/4) M(n)) time and
soft-O(N^(1/4)n) space. At these boundaries every leaf is less than N.
The numerator matrices are unnecessary for this factor search; its
success is completely explained by the denominator products. This is not
a newly discovered coefficient-based factoring speedup.

Bostan–Gaudry–Schost already develop matrix-product doubling, recurrence
batching, nonunit checks, and integer factoring. Their paper explicitly
distinguishes unit-dependent interpolation from general product methods;
see sections 1–5, especially the displayed block identity in section 4
and Theorem 11. This audit's conservative monic-tree construction pays
extra logarithms instead of presuming the faster interpolation inverses.
[Checked author-hosted primary paper, 2007](https://mathexp.eu/bostan/publications/BoGaSc07.pdf).

The deterministic benchmark requested here is
O(N^(1/5) log^(16/5)(N)/(log log N)^(3/5)), established by
Harvey–Hittmeir. Our N^(1/4) factor branch is worse in exponent, and
the N^(1/2) action route is worse still.
[Checked primary abstract](https://arxiv.org/abs/2105.11105).
The customary heuristic GNFS comparison is
L_N[1/3,(64/9)^(1/3)]; every fixed positive exponent of N above loses
asymptotically to it. This comparison does not turn that heuristic into
a proved worst-case theorem or claim optimality of its constant across
NFS variants.
[Checked primary chapter abstract](https://link.springer.com/chapter/10.1007/BFb0091539).

## 4. One materially different executable revision

Use the algebraic generating function directly in R[[z]], not a transfer
matrix. Put Q=1-6z+z^2 and h=1 mod z. For odd N, 2 is a unit. At precision
s, where Q h^2=1 mod z^s, compute

    h_new = h (3-Q h^2)/2 mod z^(2s).                  (7)

Writing e=1-Qh^2, direct multiplication gives

    Q h_new^2 = (1-e)(1+e/2)^2
              = 1 - 3e^2/4 - e^3/4.

Thus precision doubles over any odd composite modulus. The constant term
1 fixes the unique inverse square root: recursively its next coefficient
has coefficient 2, a unit. Equation (7) yields d_j modulo N for every
j below the final precision, with no factorial division, prime discovery,
or unknown characteristic. Even N yields the factor 2 immediately.

This is an actual executable revision, included in the scratch checker.
It costs O(P_R(m+1)) under standard multiplication regularity, conservatively
soft-O(m M(n)), with Theta(m n) bits of dense state to reach d_m. The
scratch uses schoolbook convolution, so its actual bound is O(m^2 M(n)).
Logarithmically many precision doublings are **not** logarithmically many
scalar operations. At m~N this revision is slower than either factoring
benchmark. It fixes the representation's nonunit defect, not its asymptotic
factoring cost, and is retained only as a correctness baseline.

The Delannoy generating function and d_j=P_j(3) connection are established
prior art, checked in Banderier–Schwer, section 1.
[Primary author-hosted paper](https://lipn.fr/~banderier/Papers/delannoy.pdf).
Fast power-series square-root computation is also established machinery;
Harvey's paper concerns algorithms over C[[x]], not a free unknown-composite
coefficient oracle. The validity of (7) over R is derived above.
[Primary paper](https://arxiv.org/abs/0910.1926).

## 5. Translation, general-family, and bounded-state limitations

The chosen route audits normalized transfer blocks. It has not disproved
every bounded-auxiliary-state index-doubling identity for scalar d_m.
Equations (2) are exact binary block identities whose auxiliary state grows;
the no-cancellation argument applies to precisely that representation.
The already-known nonrational generating-function obstruction only excludes
fixed constant-matrix powering over Q, not general modular schemes.

Neither (1) nor (7) supplies the translated-t coefficient extractor needed
for Card A's random-shift guarantee. Fixed t=1 does not inherit that
probability: for N=187=11*17, C_11(f_1)=d_5=1683=9*187, so Card A's
product identity implies C_187(f_1)=0 mod 187. This is an algebraic failure
control, not an additional numerical run at index 93. The full random-t
family still excludes both primes 3 mod 4, where every shift fails.
The denominator-factor branch can split odd composites independently of
those curve restrictions, but is just the slower general interval method.

No p-adic expansion, CRT decomposition using hidden factors, finite-field
coefficient automaton, Schoof computation at p, or characteristic-dependent
digit transition is included as an uncharged step. Any such addition would
need its own construction and cost, and is not established by this report.

## 6. Frozen diagnostic protocol — written before execution

One invocation only, Python standard library, external `timeout 60s`.
No seeds: every case is deterministic and exhaustive in the tiny lists
below. The cap covers checker setup, all cases, and result writing. No
package installation or general harness run. Formulae (1)–(7) and the
rejection rules are fixed before running.

Owned scratch names:

- H007-coefficient-check.py — the single diagnostic source;
- H007-coefficient-preregistered.md — exact pre-run copy of this report;
- H007-coefficient-results.jsonl — every completed case and run metadata;
- H007-coefficient-run.log — retained stdout/stderr and process exit status;
- H007-coefficient-hashes.json — SHA-256 hashes and execution status.

Parameters: N in (91,143,187); marked indices r in (7,11,13,17).
For every (N,r), test the three-transition block a=r-2, L=3, which covers
denominators r-1,r,r+1. Additionally, for each N test a=5,L=13, covering
denominators 6 through 18 and all four marked indices, to retain the
gcd=N case. Total 15 block cases. The action routine receives only N,a,L
and the initial residue pair; reference coefficients never enter its
factor search. Reference initial pairs deliberately come from exact sums,
so these are transition diagnostics, not factor-blind full-solver trials.

Reference coefficients for indices 0 through 18 use the exact finite sum
d_j=sum_(k=0)^j binomial(j,k)^2 2^k. For all 15 blocks compare the integer
product quotient and lifted quotient (5) with the exact endpoint pair;
verify each unit action or returned proper divisor. Record denominator
gcds, descent trace, initial/endpoint residues, and exact/lifted widths.

For the six (N,r) with r dividing N, retain the two equal input residue
pairs and unequal integral outputs from (4). These are explicit negative
controls against residue-only division; do not attempt an invalid inverse.
For every N, run (7) to precision 19 and compare at r=7,11,13,17 (12
comparisons). No comparison at the full target (N-1)/2, no new moduli,
random shifts, enlarged corpus, or timing/scaling benchmark is authorized
in this screen. Internal coefficients at precisions 1,2,4,8,16,19 are
required arithmetic, not independent cases.

Rejection: any wrong quotient/residue, non-proper returned divisor,
unjustified inverse, unreported growing integer width, or timeout rejects
the implementation as a surviving extractor. Stop on the first unexpected
failure and retain it and all unstarted case IDs. Even complete agreement
does not support an improvement: degree L state, Theta(L log L) lifted
width at a=0, or the charged N^(1/4) factor branch rejects the proposed
fast normalized-block interpretation independently of the finite screen.

The checker will hash its exact source, this pre-run report snapshot, and
the original W001 report. Results will be appended below without changing
the frozen protocol. Preserve the failed mechanisms and all gcd=N cases.

## 7. Results and disposition

The single frozen invocation completed all 33 planned cases. Exit code 0;
checker elapsed time 0.00242 seconds; external process elapsed time 0.04334
seconds; no timeout, unexpected failure, or unstarted case. These times are
only evidence that the cap was respected, not a performance comparison.

- **15 transfer blocks:** six returned correct unit actions; nine returned
  verified proper factors. All 15 exact-integer quotients and all 15 lifted
  quotients matched their reference endpoint pairs.
- **Four gcd=N controls:** the short N=91 block over denominators 12,13,14
  returned gcd 91 before descent, then factor 13. The three long blocks
  over 6,...,18 returned gcd N, then factors 7,11,11 for N=91,143,187,
  respectively. None was recorded as a factor until descent succeeded.
- **Six negative residue-only controls:** equal starting residue pairs
  produced first-output residue pairs (45,58) at (N,r)=(91,7), (3,10) at
  (91,13), (3,16) at (143,11), (94,105) at (143,13), (102,119) at
  (187,11), and (105,116) at (187,17). Thus all six confirm obstruction
  (4); they are retained failures of the residue-only normalization idea.
- **12 series-Newton checks:** at indices (7,11,13,17), the residues were
  (45,81,3,14) for N=91; (19,3,94,105) for N=143; and
  (19,102,182,105) for N=187. All matched the finite binomial sums.

Width evidence is retained, not hidden by the small moduli. Each long block's
integer denominator used 46 bits. Its lifted modulus used 53,53,54 bits for
the three moduli, and its observed lifted products reached 105,106,107 bits.
The exact product/reference action reached 89 bits. Ordinary factor-or-action
arithmetic across all cases reached at most 16 observed bits. The Newton
revision retained 19 coefficients at final precision, via precisions
1,2,4,8,16,19. Each modulus used 714 schoolbook polynomial multiply-adds
and 49 final scalar rescalings over those stages. This is already work
growing with precision despite five updates.

The scratch meters are **partial diagnostics**, not a certified bit-machine
instrumentation. In particular reference binomial generation, Python
allocation/control flow, and builtin inverse/gcd internals are not completely
metered; Newton's explicit initial gcd(2,N) check is outside its meter and
must add one gcd per modulus. All these operations are covered by the stated
theoretical bounds or reference-work disclaimer. No benchmark claim rests
on the meter values.

Evidence files, all adjacent and retained:

- [Frozen pre-run report](H007-coefficient-preregistered.md).
- [Exact checker source](H007-coefficient-check.py).
- [Every result and negative control](H007-coefficient-results.jsonl).
- [Process log](H007-coefficient-run.log).
- [Hash manifest and exact invocation](H007-coefficient-hashes.json).

SHA-256 anchors:

    checker: 753476f0880b3a91cdcdaa6f9b0431471e10b8bc33dc35b946af8015d2eded39
    frozen:  958fc8da4d932544605d19265ef55a15fba9123db73abfd36407de51b4427ddb
    results: 047b00ec05038267cfaec0f42832f0ecbf971228e9e5f5535ded0b71a090334c
    log:     3513858becc4aa7705fa1b00ced8a62774b6d678e486aa11441aa0ccc76d5c99
    W001:    96acb9218ed6ad2b5d7e564fd1103903a0834566a536a13a7e6cd23ab05387ad

The manifest also records the final H007 report hash, added after results.
The original W001 report is read-only and its before/after hash is checked.
No checker rerun or parameter revision was performed. Production checks and
Lean builds were not invoked because the assigned ownership permits only
these scratch files and no shared solver or Lean change was made.

### Evidence level and next step

**Idea rejected:** scalar cancellation of this polynomial transfer matrix
does not yield bounded-state binary extraction. Equations (3) and (4)
identify the representation-specific obstacles; neither is a general
coefficient-extraction lower bound.

**Conditional reduction unchanged:** Card A gives expected splitting cost
O(T_coef(n)+G(n)) on its stated mixed-congruence semiprime family if the
translated coefficients can be extracted in cost T_coef. This pass supplies
no improved T_coef for that family and no new random-shift success theorem.

**Explicit algorithms supplied:** the transition diagnostic implements
factor-or-action blocks, including gcd=N descent, and the different
series-Newton revision across every odd modulus. The former's batched
general factor search has the familiar soft-O(N^(1/4) M(n)) bound under
standard polynomial arithmetic; the latter computes the t=1 coefficient
with soft-O(N M(n)) dense-series work. The fast polynomial batching itself
was analyzed, not implemented or benchmarked in this tiny screen.

**Proved general complexity:** the cited deterministic 1/5 bound belongs
to prior literature. No new general complexity result is accepted here;
all H007 mathematical arguments await independent critical review.

Next action for the coordinator: independently review the pole argument
(3), the precise integral-lift scope of (4), and the accounting in (6).
Retain (7) as the executable revision/reference if a later, explicitly
different coefficient representation is proposed. Do not spend another
benchmark wave on the same scalar-normalized blocks without an actual new
transition formula and a bound that changes their degree/output cost.
**Verified factoring time-complexity improvement remains NONE.**

Source-access note: the cited primary BGS paper, Delannoy paper, and primary
Harvey–Hittmeir, GNFS, and power-series abstracts were checked online in this
pass. The initial UMD copy of the GNFS volume returned a retrieval error;
the publisher's chapter abstract was then checked successfully. This is a
bounded prior-art audit, not a novelty certificate. No source text was
copied wholesale into the repository.
