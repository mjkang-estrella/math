# H034 fewer seeds with C4-light graphs: conditional collision law

Status: mathematical candidate screen, not an adopted solver or cost gain.
Factory Opus suggested reducing seed count; root derived the density correction;
native Astra independently reviewed exact prefix counting and probability.
No experiment, implementation, new Lean claim or change to the frozen C4-free
contract. The sparse construction's full-work comparison remains unresolved.

## Precise alternative

Fix constants K,A>0 with K²>A, take n=ceil(K q^(1/4)) vertices, and sample a
uniform ordered sequence of distinct edges of the complete simple graph.
Stop at m=ceil(A sqrt(q)/2). Seed labels remain IID uniform in Fq², independently
of graph and order. Charge their generation and full EC scalar multiplications.
Emit the same two signed x-only leaves per accepted edge as in the C4-free
construction. This is not the previously rejected deterministic complete graph.

For one four-vertex set, its three perfect matchings use disjoint sets of two
edges. With independent-edge density rho, coverage probability is

    1-(1-rho²)^3.

Every covered four-set contributes exactly eight signed forms modulo global
sign, however many matchings realize them. With L=binom(n,2) and a uniform
m-edge prefix, the EXACT coverage probability instead is

    3(m)_2/(L)_2 - 3(m)_4/(L)_4 + (m)_6/(L)_6,

using falling factorials (terms vanish when too few edges are selected).
Thus E[N] is eight times binom(n,4) times that expression. At fixed positive
density, N/(4m²) tends to 1-rho²+rho^4/3. At rho=1 this recovers the complete
graph's factor1/3, making the duplicate-equation cost explicit.

Crucially, at t=x sqrt(q) leaves in this fixed-n family, rho(x)=x/K² changes
with the stopping prefix. The limiting mean event count is

    lambda(x)=x²-x^4/K^4+x^6/(3K^8).

Using the cap density throughout the stopping distribution would be wrong.
The raw review's K=6 numerical mean-loss assertion has not been established
by this paper screen; cap-density loss is not mean stopping loss.

## Why concentration and the Poisson screen still apply

Changing one edge changes the number of covered four-sets by O(n²). Exposing
a uniform edge permutation prefix and coupling different choices by a swap
therefore bounds each martingale increment by O(n²). There are O(n²) exposures,
so the variance bound is O(n^6), versus squared mean Theta(n^8). The resulting
O(n^3) fluctuation scale is lower order. A finite grid and monotonicity handle
compact prefixes; this is a paper argument, not a Lean concentration proof.

Conditional on graph/order, distinct four-support signed forms are still
nonproportional over odd Fq. Their zero events have marginal1/q and pairwise
probability1/q². An event has O(n^3) neighbors sharing vertex variables. The
same independently checked AGG zero-event bound used in
H034-paired-sum-mathematical-screen.md has error O(q^(-1/4)) at fixed positive x,
since n=Theta(q^(1/4)) and N=O(q). Lower-support forms number at most O(n^3),
so their probability is also O(q^(-1/4)). Independent-label marks handle null
target coefficients as before, with explicit paid exception/fallback policy.

Hence the putative candidate-key coefficient is integral_0^A exp(-lambda(x))dx,
and the separately priced fresh-blinded fallback has probability
exp(-lambda(A)). Neither expression includes graph construction or lookup work.

## Complete-cost obstacle

The smaller n reduces seed scalar-multiplication work to O(q^(1/4)log(q)),
but exact graph generation is not free or lower order merely because n is small.

- Lazy sparse Fisher-Yates samples the required permutation but retains O(m)
  dictionary state and charges random draws, lookups and updates.
- Uniformly propose an edge index and reject repeats using an exact dictionary.
  Through m accepted edges the expected proposal count is
  L * sum_(j=0)^(m-1) 1/(L-j). At fixed density it is Theta(sqrt(q)).
- Scanning all O(n²) Bernoulli positions is also leading work. Lexicographic
  accepted prefixes are not uniform edge prefixes, so cannot inherit this law.

Unbiased integer sampling, triangular pair-index decoding, graph dictionary
hashing/clearing, payloads and peak storage must all be included. A PRF or an
unproved deterministic edge permutation does not supply the exact graph law.
Even if graph memory replaces saved roots at finite sizes, its dictionary work
may exceed the candidate's small key-count margin. No asymptotic exponent gain
is proposed: the number of generated keys is still Theta(sqrt(q)).

### Subsequent root correction: a packed bitset replaces the dictionary

Native Astra independently accepted the following exact sampler. Draw i,j
independently uniformly in [0,n), reject i=j, sort to i<j, then test/set bit
i*n+j in an initially zero n²-bit array. Reject repeated edges. Each unordered
edge proposal is uniform; the accepted sequence is a uniform edge permutation
prefix. No graph hash table or integer square-root pair decoding is necessary.

After j accepted edges a raw ordered pair is accepted with probability
2(L-j)/n². Through m accepted edges the expected raw-pair draws are

    (n²/2) sum_(j=0)^(m-1) 1/(L-j).

Do not put E[m] into this nonlinear expression for a stopped search. With
independent randomness, each waiting time is independent of the next accepted
edge. Conditional on accepted order and seed geometry, the same harmonic sum
applies through its determined stopping count M. Consequently expected draws
are sum_j [n²/(2(L-j))] Pr(M>j). The leading coefficient is

    (1/2) integral_0^A exp(-lambda(x))/(1-x/K²) dx.

Count prepaid generated-edge overshoot and vertex-sampling rejection separately.
Elapsed-time or proposal-count aborts require separate censoring analysis.

For fixed K, n² bits are lower order than sqrt(q)log(q) archive bits, despite
being leading Theta(sqrt(q)) bit initialization work. Under an explicitly
declared Theta(log(q))-bit word RAM, zeroing costs O(sqrt(q)/log(q)) word writes.
These are different accounting models. Random bit tests, updates, unbiased RNG,
sorting/index multiplication, seed fetches and archive work remain charged.
Compact storage does not make each random access free.

Updated cheapest falsifier: use this bitset ledger rather than an unnecessary
dictionary, price saved seed setup against added graph work, and retain the
variable-density survival law. No synthetic run or physical cost claim follows.

Process: Factory task ecdloop-h034-sparse-pair-priorart-factory-opus-20261008-r1
initial unverified suggestion; root correction; /root/h007_additive_relations
independent read-only review completed. Reviewers ran no experiments or imports.
The original finite contract is unchanged; verified improvement remains NONE.
