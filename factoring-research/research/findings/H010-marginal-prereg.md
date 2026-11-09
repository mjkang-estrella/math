# H010 frozen structural screen, version 1

Written before any graph width or elimination order was evaluated. Validation
of the Boolean functions is a separate exact mathematical check and has already
passed. No circuit change, limit increase, or second screen is authorized within
this preregistration. The sole candidate source is H010-marginal-screen.py;
the screen records its SHA-256 and this file's SHA-256 in the manifest.

Frozen before width execution:

- Source SHA-256: `a75816496e1148235baf31a9770e3454d80fb354b46eafb3eeccbdb3b36fc14e`.
- Exact 688 case IDs and numeric N,a,k are in H010-marginal-cases.json, SHA-256
  `960b0e9c8efb154099e86206dd71b12425ef98e769f8da81a7f9309bca6a09fb`.
  This file was generated without calling candidate() or minfill(). The timed
  screen regenerates the same complete corpus, charging that work again.

## Input and arithmetic representation

The candidate receives only odd N >= 3, 0 < a < N with gcd(a,N)=1, and a public
prefix length k. n=N.bit_length(), m=(N*N-1).bit_length(), Q=2^m. Compute
c[j]=a^(2^j) mod N by m-1 modular squarings. No factors, orders, size-family
metadata or compiled gates using orders enter candidate().

For an n-bit word u<N, an input bit b and constant d<N, addmod forms the
(n+1)-bit ripple sum s=u+b*d, then forms t=s+(2^(n+1)-1-N)+1 with another
(n+1)-bit ripple adder. Its final carry h is 1 iff s>=N. Output bit i is
mux(h,t[i],s[i]) for 0<=i<n. Each ripple cell creates sum=x XOR y XOR carry,
then majority(x,y,carry), low bit first. A mux has three Boolean inputs.
Every factor enforces ONE output bit's truth table with at most three inputs;
no arithmetic word is a constant-width gate. Constants use literal 0/1.

multiply(y,c) starts v=0 and runs these addmod rows for y[0],...,y[n-1] and
constants c,2c,...,2^(n-1)c reduced modulo N by successive doubling. This
computes c*y mod N even for n-bit y>=N. exponentiate starts at 1, processes
exponent bits from high to low, computes multiply(current,c[j]), and selects
product versus current with that exponent bit, low output bit first.

## Clean semantics and prefix factors

The deterministic DAG admits a compute-copy-uncompute reversible realization:
each constant-arity truth table is reversibly computed into a fresh zero bit,
the final word is copied, and the entire DAG is reversed. No scratch output is
traced before uncomputation. Summing the Boolean constraints has exactly one
scratch assignment for each input, and represents this clean output word.

Fix the QFT convention exp(+2*pi*i*x*y/Q). Semiclassical history is the low
output bits y[0],y[1],..., all zero. These measure high exponent bits first.
For a k-bit history s, the joint mass is

    1/(Q*2^k) sum_(x,x') [x == x' mod 2^(m-k)]
                [a^x == a^x' mod N] exp(2*pi*i*(x-x')*s/Q).

Let t=m-k, x=2^t*u+v. The equal unmeasured low bits give the same v in both
branches. A paired modular multiplication by a common unit is bijective on
residues, so its traced pair cancels: [cw=cw' mod N]=[w=w']. Apply this to the
low-bit suffix, in reverse circuit order. Sum the now unused v; this gives

    P_k(s) = 2^(-2k) sum_(u,u'<2^k)
       [a^(2^t*u) == a^(2^t*u') mod N] exp(2*pi*i*(u-u')*s/2^k).

The candidate builds two explicit DAGs for the residual high k bits and
identifies their final word bits through equality factors. For this all-zero
history every measured-bit pair factor is the constant 1/2 (before the
normalization above). There is NO equality constraint on measured exponent
bits. General histories carry the displayed product of one-bit phase factors;
their structural scope can be at most each measured ket/bra bit pair, but their
value-dependent cancellations and success probabilities are not screened here.
At k=0 the correctly cancelled mass is 1.

## Creation indices and allowed simplifications

Allocate ket exponent inputs least significant first, then ket arithmetic in
the order above, then bra inputs least significant first, then bra arithmetic.
Only actually allocated variables consume IDs; constants consume none. Each
gate enumerates its <=8 input assignments, substitutes literal constants and
repeated inputs, removes inessential arguments, returns a literal for a constant
function and returns the input for identity. Negation remains an explicit unary
gate. Exact common-subexpression keys (sorted input IDs, output truth table)
share one output wire, including across ket and bra when genuinely identical.

Reverse-topologically remove unused deterministic outputs: summing each such
output contributes exactly 1. Preserve all exponent inputs, even isolated ones.
After adding final equality factors, repeatedly process factors in lexicographic
order: substitute pinned variables and equality representatives; remove
inessential arguments; discard constant-one factors; pin single-support unary
factors; identify an equality pair, keeping the smaller original creation ID;
deduplicate identical Boolean indicator factors. Repeat to a fixed point.
No disequality aliasing, global implication solver, range-invariant optimization,
order-based identity, or factorization of later dense intermediates is included.
These are exact identities, not unit-cost modular-arithmetic contractions.

## Graph and deterministic elimination

Vertices are the remaining binary variables, including isolated free inputs.
Each factor scope forms a clique. Score a live variable by the number of absent
edges among its neighbors. Choose minimum (score, original creation index).
Inspect vertices ascending by ID; a zero score can end the scan because no later
ID can win. Complete its neighborhood and delete it. No heuristic alternative
or lower-degree tie break is permitted.

This particular dense method materializes the whole bucket product before
summing the selected variable. Width w includes initial factor scopes and each
bucket scope {v} union neighbors(v), as well as the smaller output factor.
Thus w=max(initial arity,1+maximum elimination degree); the one-bit distinction
from output-factor-only width is explicit. Even if a dense intermediate could
be compressed semantically, this implementation retains its complete array.
Only scopes are constructed in this screen; dense numeric arrays are not run.

Reject the registered cap at the first bucket with
w > 2*ceil(log2(n))+4. Store the selected vertex, its neighbors and fill score,
the entire order prefix and its hash. Stop the entire wave on this first width
rejection or on a planning timeout. Passing a prefix is not a theorem for other
histories, inputs, optimal orderings, numeric error or factoring success.

## Cases, order, budgets, and retained censoring

Use Python standard-library random.Random(1002). For n=8,12,16,20, in that
order, set h=n/2. Enumerate trial-division primes in
[2^(h-2),2^(h+1)), ascending. Draw two distinct primes with rng.sample; accept
N=p*q iff its bit length is n, max(p,q)<=4*min(p,q), and N is new at that size.
This is the frozen definition of balanced (ratio at most four). Strictly using
two distinct h-bit primes cannot supply three 8-bit moduli; the ratio definition
makes the requested grid feasible without silently duplicating moduli.

For each of three accepted N, draw two distinct unit bases using rng.randrange(2,N)
and gcd rejection. Generate their prefixes k=0,...,m in increasing order.
The generator retains no factors in its manifest or candidate invocation.
Generation and all draws for the complete grid occur before planning and count
toward the budget. Case IDs nNN-Ni-aj-kKK use zero-based modulus/base indices,
two-digit bit/prefix fields, and include the numeric N,a in the manifest.

Command, exactly one screen:

    timeout 60s python3 research/findings/H010-marginal-screen.py screen

The process has a 55-second cooperative deadline measured before generation
and a 60-second external timeout. No budget extension or retry. Before first
planning, write every case with status unstarted in H010-marginal-manifest.json.
Flush a started journal record before construction and a finished record after
each result. A started record without a finished one is external-timeout or
interruption censored, not zero-cost or a pass. All remaining manifest cases
stay unstarted. Preserve partial width lower bounds and all planning counters.
Building/simplification can also be externally censored. A 55-second check is
between elimination steps, so a single slow score calculation may instead hit
the external limit. The resulting report must disclose this distinction.

Validation before the screen uses exact Boolean arithmetic only, with its own
60-second external cap. It exhausts addmod, multiplier, exponentiation, local
paired permutation identities, and all-zero prefix cancellation over the stated
small domain in the source. Normalization has exhaustive small relation tests;
full-network partition checks disclose any >18-variable omissions. No amplitude
simulator, numerical phase approximation or width benchmark is part of validation.

## Cost obligations

Each addmod has O(n) constant-size factors, multiplier O(n^2), exponentiation
O(m*n^2)=O(n^3). Classical constant generation and truth-table work are charged.
With V=O(n^3), F=O(n^3), straightforward fixed-point normalization is polynomial
(a conservative O(V^3 log V) bit bound suffices); naive min-fill has at most
O(V^4) edge-pair tests plus index/sorting cost and O(V^2) graph bits. Time spent
planning is part of the observed cost and can itself censor the wave.

The proposed dense exact all-zero contraction, if executed, would require
O(poly(V)*2^w) arithmetic operations, with O(V) bits sufficient for integer
partial counts and O(V*2^w*V) conservative storage bits. Polynomial sampling
would additionally need uniform width, general-history certified precision,
charged O(n^2) samples/postprocessing, and a useful joint splitting probability.
No such theorem is assumed or inferred from this screen.
