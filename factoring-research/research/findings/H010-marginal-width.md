# H010 — A clean Boolean marginal network fails its frozen dense-bucket cap

2026-10-08. **Verified new factoring complexity improvement: NONE.**

**Disposition: reject this registered representation/order/bucket implementation
at its finite width cap; asymptotic marginal simulation remains unresolved.**
The first nontrivial arithmetic case, `n08-N0-a0-k02` with N=143, a=35 and a
two-bit all-zero semiclassical history, required an 11-bit bucket against the
preregistered cap 10. The one-bit convention matters: its resulting output
factor had 10 bits. This is a failure of the implementation that explicitly
materializes bucket products. It is **not** a demonstrated failure of an
output-factor-only cap of 10, a lower bound on optimal treewidth, or a rejection
of every possible O(log n) bound with different constants.

One frozen screen ran, stopped at its first rejection, and retained all 688
cases: 2 completed prefixes, 1 width rejection, 685 unstarted, 0 incomplete,
0 timeouts. A separate exact audit replayed every selected vertex through the
rejection using an independently implemented bitset score calculation.

## Scope and durable evidence

Read AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md, research/STATE.md, and W001-orders.md Card C and its complete
ranking/protocol. This assignment's H010 ownership overrides the general loop's
shared registration/state-update steps. Only this report and adjacent
H010-marginal-* files were written. No shared solver, Lean, STATE, other report,
package, commit, publication, scheduler or child agent was changed/created.

The exact source, frozen choices and every outcome are available here:

- [Frozen protocol](H010-marginal-prereg.md), including bit order, all allowed
  cancellations, creation indices, width convention, rejection and timeout rules.
- [Candidate and validation source](H010-marginal-screen.py).
- [688 cases frozen before width execution](H010-marginal-cases.json).
- [Pre-screen exact validation](H010-marginal-validation.json).
- [Timed-run manifest](H010-marginal-manifest.json) and
  [append-only event journal](H010-marginal-outcomes.jsonl).
- [Complete merged results](H010-marginal-results.json), with an explicit final
  status on every case, including all unstarted cases.
- [Independent witness replay and symbolic checks](H010-marginal-audit.py) and
  [audit result](H010-marginal-audit.json).

No general numerical amplitude simulator was implemented. All executed
mathematical checks were Boolean/integer/rational or formal phase-coefficient
identities. The standalone validation and audit are the applicable checks for
this owned scratch implementation; the shared harness and Lean build were not
run or modified.

## Exact arithmetic representation

Input to `candidate` is exactly N, a unit a and public prefix length k. Let
n=bitlength(N), m=ceil(log2(N^2)), Q=2^m. The expression
`(N*N-1).bit_length()` computes this m without floating point. Compute constants
c_j=a^(2^j) mod N by repeated squaring. Factors, orders, prime-size labels and
order-specific compilation are never candidate inputs. Tiny prime generation
belongs only to the separate corpus generator.

All wires are binary. A deterministic gate is a truth table with at most three
input bits and one output bit; its constraint factor is
`[output = table(inputs)]`, with arity at most four. A ripple cell computes

    sum_i = u_i XOR v_i XOR carry_i,
    carry_(i+1) = majority(u_i, v_i, carry_i).

These are two separate bounded-arity factors, sharing the three input wires.
Low bits are created first, sum before next carry. No n-bit word or modular
arithmetic operation is counted as one constant-width factor.

For current word u<N, bit b and literal d<N, `addmod` forms the (n+1)-bit sum
s=u+b*d, then ripple-adds the (n+1)-bit complement of N and carry-in 1.
Denote this difference word by D and the final carry by h. Since s<2N,

    h = [s >= N],
    result_i = mux(h, D_i, s_i),   0 <= i < n.

If h=0 then s<N and its n low bits suffice. If h=1 then D=s-N<N. This proves
both reduction and the invariant that the output lies in [0,N). The first
addition cannot overflow n+1 bits; discarded high bits introduce no additional
choices or hidden residue wraparound.

`multiply(y,c)` starts v=0 and, for i=0,...,n-1, performs

    v <- addmod(v, y_i, d_i),    d_0=c, d_(i+1)=2*d_i mod N.

The invariant is v_i = c*(y mod 2^i) mod N, so the result is c*y mod N for
every n-bit y, including y>=N. `exponentiate` starts at 1 and visits exponent
bits from high to low. At bit j it builds `multiply(current,c_j)` and selects
that word versus current with the exponent bit. Therefore its output is a^x
mod N. Constants and comparisons are all generated from N and a by charged
classical arithmetic.

**Why the deterministic DAG represents a clean reversible computation.**
Compute each bounded-arity gate into a fresh zero scratch bit using a reversible
truth-table implementation, copy the final word into a zero output register,
then undo the DAG in reverse order. Constant-arity reversible implementations
cost a constant number of elementary reversible gates (a constant-size
algebraic-normal-form construction suffices). This realizes

    |x>|0_output>|0_scratch> -> |x>|a^x mod N>|0_scratch>.

There is exactly one satisfying internal assignment of the forward DAG for
each x. Consequently its constraint sum describes this clean computation's
output, with no factor counting alternative garbage values. In particular the
two branches must agree only on the retained work output. Imposing equality of
their intermediate garbage would incorrectly remove valid interference.

## Which prefix probability is contracted

Use Fourier convention `exp(+2*pi*i*x*y/Q)`. Write s for the first k *low*
output bits, so a semiclassical implementation measures high exponent bits
first. Start from the clean state

    Q^(-1/2) sum_(x<Q) |x>|a^x mod N>.

Tracing the work output gives exactly the equality indicator between the two
residues. Summing Fourier outputs y=s+2^k*z, z<2^(m-k), gives a finite geometric
sum. It vanishes unless x=x' mod 2^(m-k), and otherwise has 2^(m-k) terms.
Thus the joint prefix mass, not a conditional probability by itself, is

    P_k(s) = 1/(Q*2^k) sum_(x,x'<Q)
       [x=x' mod 2^(m-k)] [a^x=a^x' mod N]
       exp(2*pi*i*(x-x')*s/Q).                         (1)

The first indicator is the trace coupling on the unmeasured exponent bits.
Measured exponent bits are **not** identified across branches. Equivalently,
each measured high-bit pair has a phase-projector entry of magnitude 1/2;
on an all-zero history that entry is the constant 1/2 for all four assignments,
not a diagonal/equality matrix. Omitting this distinction would change the
distribution.

Let t=m-k and write x=2^t*u+v, x'=2^t*u'+v. The common unmeasured low-bit
suffix multiplies the two work words by identical units. For each such clean
arithmetic pair the exact identity is

    [c*w mod N = c*w' mod N] = [w=w']  when gcd(c,N)=1.   (2)

It follows by multiplication by c's inverse; the implementation never needs to
find an order or factor N. Apply (2) backwards along the common low-bit suffix.
The remaining v sum contributes 2^t, yielding

    P_k(s) = 2^(-2k) sum_(u,u'<2^k)
       [a^(2^t*u)=a^(2^t*u') mod N]
       exp(2*pi*i*(u-u')*s/2^k).                       (3)

This cancellation is a recognized composition of unit-multiplication
identities on valid residues, with polynomial recognition cost. It is not
unrestricted cancellation of arbitrary deterministic many-to-one gates.

The candidate constructs both residual DAGs in (3), not an exponential table
of u. The last n pairs of work wires get equality constraints. The global
normalization is 2^(-2k). For s=0 the phase factors are constant and disappear
legally. For a general fixed history they are explicitly the product

    product_(j<k) exp(2*pi*i*2^j*s*u_j/2^k)
                  exp(-2*pi*i*2^j*s*u'_j/2^k).

Thus the omitted zero-history phase edges are not missing measurement
couplings: these fixed-history projectors factor into ket and bra one-bit
terms, and become constants at zero. Values and cancellations on other
histories are still different; this screen establishes no sampler for them.
Actual sampling would use ratios of the two next-prefix masses and would owe
certified error control and nonzero-denominator handling.

Equation (3) is computed without an order oracle. Replacing its equality
predicate by counts of multiples of an unknown order would not be an
implementation of it. Nor does the identity itself reduce its exponential
summation cost.

## Legal local simplification and function evidence

Gate construction exactly substitutes constants and repeated arguments,
removes inessential truth-table arguments, aliases identity gates, and shares
identical deterministic subexpressions. Unused deterministic outputs can be
summed in reverse order, each contributing one. This does not discard free
exponent variables, whose summations may contribute two.

After adding the trace equalities, the fixed-point normalizer substitutes
equal variables and pinned bits, removes independent arguments and constant-one
factors, recognizes unary pins and binary equality, and deletes duplicate
Boolean indicator factors. Each identification has a unique extension to the
eliminated variable; each duplicate deletion uses f*f=f for f in {0,1}.
The representative is always the smallest creation index. No generic identity
`[f(u)=f(v)] => [u=v]` is used: it is false for noninjective f. Negation and
disequality remain explicit unless ordinary local truth tables remove them.

Before any width execution, exact exhaustive checks passed:

- Every odd N=3,5,...,15, every d in [0,N), every u<N and control bit:
  1,358 addmod assignments.
- The same N,d and every n-bit input word: 876 multiplier assignments.
- The same N, every unit a and all m-bit x: 7,712 exponentiation assignments.
- Every generated unit power, both control values and all residue pairs:
  89,664 checks of the paired cancellation identity.
- Every prefix length for all those N,a: 384 exact rational checks of (1)=(3)
  on the all-zero history.
- All satisfiable collections of two nonzero unary/binary relations on three
  variables: 1,317 exhaustive partition-preservation tests of normalization.
- For N in {3,5,7}, every unit a and k<=3: 44 exhaustive complete-network
  partition checks. Four cases with more than 18 remaining variables were
  explicitly omitted; they are not reported as exhaustive partition passes.

The pre-screen validation finished in 0.6324 seconds internally under its own
60-second external cap. These tests supplement the all-input invariants and
local identities above; tests alone do not prove arbitrary-size correctness.

After the screen, the audit additionally checked every residual input pair for
the three started prefixes (1,4,16 pairs respectively). It also checked all 384
small-domain prefix identities as exact coefficient dictionaries in a formal
2^k-th root of unity. Equality of the dictionaries establishes the identity for
*every* s simultaneously without floating-point phases. This was verification
of the same frozen representation, not another width screen or circuit change.

## Frozen elimination, outcome and exact witness

The primal graph has one vertex per remaining binary variable and a clique for
each factor scope. The selected vertex minimizes the number of missing edges
among its neighbors, then its original creation index. There is no degree
tie-break. Each chosen neighborhood is made a clique and the vertex removed.
The exact source and preregistration define every creation-order detail.

For this particular contraction implementation, a dense bucket product on
`{selected variable} union neighbors` is allocated before summation. Reported
w includes that product as well as initial/output factors. This convention was
frozen before the run. It costs one index more than a fused multiply-and-sum
implementation that never stores the bucket product. Graph scopes are the
storage scopes of this declared dense algorithm; no claim is made that their
values lack a more concise representation.

The sole width command was:

    timeout 60s python3 research/findings/H010-marginal-screen.py screen

It returned exit code 0, empty stderr, and internal elapsed time 0.3266 seconds.
The cooperative limit was 55 seconds from before corpus generation. Source,
protocol and all case IDs were frozen before the command. Generation was
repeated within the timed process and counted. The observed times are scratch
diagnostics, not bit-complexity bounds or factoring benchmarks.

Results, all for N=143,a=35 before the global stop:

- `n08-N0-a0-k00`: completed, width 0, 0 variables/factors.
- `n08-N0-a0-k01`: completed, width 2, 2 variables and 1 factor after cleanup.
- `n08-N0-a0-k02`: rejected at width 11 > 10. Construction created 464
  variables; cleanup left 426 variables and 430 factors. Initial maximum
  factor arity was 4. After 252 completed eliminations, the next selected
  variable was 28, with fill score 11 and neighbors
  `[1,4,6,7,30,36,39,40,41,42]`. Its 11-variable bucket exceeds the cap;
  the output factor would have 10 variables. There were 174 live variables at
  rejection. Scoring used 73,336 candidate evaluations and 3,000,052 pair
  checks; construction took 0.01743 seconds and this case 0.32215 seconds.

The journal retains all 253 selected IDs, including the rejecting selection.
Their compact-JSON SHA-256 is
`c1602acc5eba0af5470337c50dddd7549571afc8c571f3df12e36fbba2d90946`.
The independent bitset replay verified the minimum score and creation-index tie
break at every step, the witness neighborhood, and both width conventions.
No suffix of this elimination order was executed, so **11 is a lower bound on
this order's eventual maximum bucket width, not its measured complete width**.

All nominal cases remain in the denominator. At 8 bits there were 98 prefixes:
2 completed, 1 rejected and 95 unstarted. All 150 prefixes at 12 bits, 196 at
16 bits and 244 at 20 bits were unstarted. There were no interrupted started
cases and no measured widths for any unstarted prefix. The full JSON includes
the three distinct moduli and two distinct unit bases at each size. Balanced
means factor ratio <=4, specified in advance: insisting on two distinct 4-bit
primes cannot provide three distinct 8-bit moduli. Factor-size information
never reaches the candidate.

## Complete cost and limits of the conclusion

There are O(n) factors per modular addition, O(n^2) per constant multiplier,
and O(k*n^2)<=O(n^3) in each residual exponentiation DAG. Compute-copy-uncompute
uses O(n^3) reversible elementary gates and O(n^3) scratch bits under this
deliberately simple construction. The constants require O(n) n-bit modular
squarings, plus the multiplier doublings; with schoolbook arithmetic this is
polynomial, conservatively O(n^3) bit operations apart from indexing overhead.

For V,F=O(n^3), the explicit fixed-point truth-table simplifications cost a
polynomial in V; O(V^3 log V) is a conservative bit bound. Naive min-fill costs
O(V^4) adjacency-pair tests plus polynomial bit/index/sorting overhead. Graph
storage costs O(V^2) bits plus indices. Planning is not free: it could cause a
timeout independently of width. It did not do so on the only started cases.

A dense contraction of this nonnegative all-zero network would require
O(poly(V)*2^w) bit operations. Intermediate integer counts need at most O(V)
bits because they sum at most 2^V Boolean assignments. A conservative memory
bound is O(V^2 + F*2^w*V) bits, including retained factors and the dense bucket.
The actual screen stored graphs/scopes, not those numeric dense arrays.

For general histories the complex phase factors would require controlled
precision. No interval implementation or propagation proof was supplied, and
no useful joint probability of a cheap instance and a splitting base was
established. The O(n^2) Fourier samples, all prefixes on sampled histories,
continued-fraction processing, verification and restarts from W001 Card C
would all remain chargeable obligations of an eventual factoring algorithm.

This rejection is deliberately narrow. It neither demonstrates growing
optimal treewidth nor proves large scalar contraction complexity. In fact,
this k=2 prefix has just 16 exponent-input pairs; direct deterministic
evaluation computes it in polynomial work. The observed failure therefore
exposes the limitations of local simplification plus this dense min-fill
implementation, even at a classically easy prefix. It cannot justify a generic
simulation lower bound, a whole-state-rank argument, or a factoring-hardness
claim. One finite violation of the chosen constant cap also cannot rule out
some other O(log n) asymptotic bound for the same broader family.

No general factoring route survives this screen as a demonstrated improvement.
A concrete changed representation for a *separately preregistered* follow-up
would condition on the k ket/bra exponent bits, propagate the deterministic
DAGs, and sum their exact output-equality indicators. This removes the present
carry-graph artifact for fixed k, at explicit O(4^k*poly(n)) cost. It was not
run as a replacement here and is exponential when k=Theta(n); a rescue would
need a proved polynomial bound on the conditioned cutset or a new compact
counting primitive. Merely increasing this cap or enumerating all exponents
would not supply that missing mechanism.

## Primary prior art checked via web

[Markov–Shi, Simulating quantum computation by contracting tensor networks](https://arxiv.org/html/quant-ph/0511069v7)
establish width-dependent classical simulation. Their general simulation
framework is prior art; this report measures a specifically defined Boolean
primal-graph elimination/bucket width and does not substitute it for every graph
parameter in their theorems.

[Yoran–Short, Classical simulability and the significance of modular exponentiation in Shor's algorithm](https://arxiv.org/html/0706.0872v1)
already reduce Shor simulation to suitable product-input/product-measurement
simulation of modular exponentiation and conditional measurement probabilities.
This was checked in the primary full text, including the iterative measurement
construction. The proposed reduction is consequently not new.

[Griffiths–Niu, Semiclassical Fourier Transform for Quantum Computation](https://arxiv.org/abs/quant-ph/9511007)
provides the adaptive single-qubit measurement replacement for the final
Fourier transform. Equation (1) independently fixes this report's output-bit
order and prefix normalization. [Cuccaro et al., A new quantum ripple-carry addition circuit](https://arxiv.org/abs/quant-ph/0410184)
is established ripple-arithmetic prior art; the particular implementation here
uses the explicitly described Boolean DAG and clean reversible embedding,
not an assertion that it reproduces Cuccaro's optimized ancilla count.

These primary pages were checked during H010. The bounded check supports the
specific provenance above; it is not an exhaustive novelty survey. The outcome
is a reproducible finite falsification of a declared implementation, not a new
factoring reduction or complexity improvement.

## Integrity references

- Frozen source: `a75816496e1148235baf31a9770e3454d80fb354b46eafb3eeccbdb3b36fc14e`.
- Frozen protocol: `3078ae1fa24dd14b5d4616d9ea7c9b4e36e36307687ff1ee0cc7704d8220eb6f`.
- Frozen case IDs: `960b0e9c8efb154099e86206dd71b12425ef98e769f8da81a7f9309bca6a09fb`.
- Raw outcomes: `dd10cb97bf409e2d0bdc3014de55658c2e78964a833a3026eb541701f69d0468`.
- Complete merged outcomes: `d926d4bb8d74167ccd9a8c351382c2b3f59d7b87b582af13e65e56da8226d60a`.

The audit confirmed the timed manifest, pre-screen validation and current
source share the same frozen source hash and that the timed cases exactly match
the pre-execution case file. Frozen source and protocol were not edited after
the screen.
