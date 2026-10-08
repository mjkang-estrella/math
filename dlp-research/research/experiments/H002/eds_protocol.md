# H002 A1: fixed-family EDS diagnostic — pre-run protocol

Status: implemented for independent pre-run review; **not run or accepted**.
No discrete-log solver, noisy reconstruction, asymptotic improvement, recovery
probability, or hardware throughput is claimed. Verified improvement remains
NONE. The diagnostic asks whether a small, fixed family of computable point
predicates has parity correlation on declared tiny ordinary synthetic groups.

The source is `eds_diagnostic.py`. Only Python syntax checking is authorized
at this checkpoint. A later independently authorized command would be:

```
python3 research/experiments/H002/eds_diagnostic.py --output /tmp/H002-eds-results.json
```

## Arithmetic and independent normalization checks

Work on the short-Weierstrass curve `y^2 = x^3 + a*x + b` over an odd prime
`p > 3`, with full prime group order `q > 3`, `q != p`, and
`gcd(q,p-1) = 1`. Every declared group order is independently checked by
enumerating all affine points using a counted dictionary of squared ordinates.
Nonsingularity and primality are checked. Thus nonidentity points have exact
order q; no scalar inverse table is consulted. The deterministic generators
below are verified on-curve and `q*P = O`. The auxiliary H001 fixtures also
have nonzero a,b; no special-curve property is used.

Use the pointwise division-polynomial sequence `W_R(n) = psi_n(R)`, with:

```
W(0) = 0; W(1) = 1; W(2) = 2*y
W(3) = 3*x^4 + 6*a*x^2 + 12*b*x - a^2
W(4) = 4*y*(x^6 + 5*a*x^4 + 20*b*x^3
             - 5*a^2*x^2 - 4*a*b*x - 8*b^2 - a^3)
W(2*m+1) = W(m+2)*W(m)^3 - W(m-1)*W(m+1)^3
W(2*m) = W(m)/W(2) * (W(m+2)*W(m-1)^2 - W(m-2)*W(m+1)^2)
W(-n) = -W(n)
```

The even recurrence uses the inverse of the fixed nonzero W(2), rather than
dividing by a possibly zero intermediate W(m). Zero terms at indices divisible
by q are therefore harmless in recursion. An identity point is never passed
to this representation. Squares/cubes and all displayed field arithmetic are
executed through the field wrapper; there is no Python integer power used to
perform a field power.

Memoized recursion halves indices and requests a bounded band of neighbouring
half-indices. It does not enumerate every term up to n. For a single positive
query, each recursion depth lies in a band of at most nine integer indices;
each path has at most `ceil(log2(n))+1` expanding depths. Consequently the
number of evaluated recurrence nodes is O(log n). This is an elementary
algorithmic bound, not a runtime measurement or a Lean proof. A batch of q
distinct requests can fill O(q) cache entries and is not claimed to cost O(log q)
overall. Each pointwise phi calculation has its own fresh cache.

Set `e = inverse(q*q mod (p-1), p-1)` using counted extended Euclid. Define

```
phi(R) = ( W_R(p-1) / W_R(p-1+q) )^e
```

The **whole ratio** is exponentiated. Both its numerator and denominator are
checked nonzero. This direct definition is used separately at every nonidentity
R. It does not compute phi(R) from the scalar label or the identity being tested.
Independent affine coordinate addition generates the labelled orbit; binary
scalar multiplication checks every tiny-fixture label and the public boundary
indices 1,2,q-1 in larger cases. These functions do not use EDS values.

For every `k = 1..q-1` and each unwrapped index `n in {k,k+q}`, test:

```
phi(n*P) = phi(P)^(n*n) * W_P(n)
chi(W_P(n)) = chi(phi(n*P)) * c^n, where c = chi(phi(P))
chi(W_P(k+q)) = c * chi(W_P(k))
c = chi(W_P(p-1) * W_P(p-1+q))
```

The character is obtained with explicit binary exponentiation, not a supplied
residue oracle. The n^2 identity and c^n identity are the corrected forms
derived in the retained H002 normalization review. The printed n^2-1/c^(n-1)
forms are not adopted. The original primary reference is
[Lauter–Stange, arXiv:0803.0728v2](https://arxiv.org/pdf/0803.0728), definition
(3) and the surrounding normalization discussion; the review records the
misprint and derivation. This protocol does not claim an independently published
erratum or correctness theorem for the new implementation.

## Frozen cases, predictors and controls

Execute in this fixed order, without choosing a generator by its character or
observed bias:

1. `p=13,a=2,b=4,q=17,P=(0,2)`, expected c=+1.
2. `p=19,a=2,b=9,q=23,P=(0,16)`, expected c=-1.
3. `p=59,a=28,b=27,q=73`, generator seeds 7,19,43.
4. `p=127,a=78,b=87,q=139`, generator seeds 7,19,43.
5. `p=251,a=218,b=156,q=257`, generator seeds 7,19,43.

For each seeded generator, use the first `random.Random(seed).randrange`
index into the lexicographically enumerated full affine-point list. Repeated
generator choices are retained and reported, not replaced. These are selected
tiny synthetic examples, not a representative random-curve survey or fresh
cryptographic instances. The larger fixtures are taken from the H001 diagnostic,
not searched during this run. Validation and generator-selection costs are
reported, including shared per-curve validation once in the global vector.

Freeze the family:

```
(0), (0,1), (0,1,2), (0,1,3), (0,2,4), (0,1,2,4,8)
```

For every minimal scalar residue `k in [0,q)`, define
`G_A(k*P) = product_a chi(phi((k+a)*P))` and label `(-1)^k`.
Exclude precisely the windows with any `k+a == 0 mod q`. Report the excluded
indices and their exact mass over q, and normalize correlation by the eligible
count. All families contain zero, so k=0 is always excluded. No zero is silently
assigned a predictor sign. Point lookups use `(k+a) mod q`; EDS indices use the
unwrapped integer `k+a`. The former is not substituted into the latter.

Verify the window identity at each eligible k:

```
G_A(k*P) = c^(len(A)*k + sum(A)) * product_a chi(W_P(k+a))
```

In the c=-1 class this gives the exact correlation numerator
`sum_k (-1)^(sum(A)+(len(A)+1)*k) * product_a chi(W_P(k+a))`.
Its per-window equality is checked. Odd families therefore give an untwisted
EDS-character sum with the known offset sign; even families give a parity-twisted
sum. **Even products are legitimate predictors, not universal null controls.**
The c=+1 class is reported separately and still has ordinary point-predicate
correlations; it is not labelled “no information.”

For every family report signed numerator N, denominator T, and correctness of
the frozen +1 orientation, `(T+N)/2`. Correlation is N/T; prediction advantage
is N/(2*T). Do not choose the sign using test labels. Do not select a winning
family, claim statistical significance from maximum absolute correlation, or
convert a large tiny-instance correlation into a scalar-recovery result.
Exhaustive evaluation is descriptive on that finite group, not independent
Bernoulli sampling. Family members/windows and seeded generators can be dependent.

For each family, shuffle the eligible labels with independent, predeclared
control seeds 7,19,43 using explicitly counted Fisher–Yates. This preserves the
label imbalance and exclusion mask. Report all three shuffled correlations;
do not select the most favourable control. Shuffling is the declared negative
control. No significance test, confidence interval, multiple-testing-corrected
discovery claim, or trained orientation is implemented in this diagnostic.

The exhaustively constructed label/point/phi tables are **diagnostic data**.
They are not advice or preprocessing available for free to a hypothetical DLP
solver. All their arithmetic and recorded table construction costs are included.
No claim about amplification or noisy bit-to-scalar reconstruction follows:
minimal-residue wraparound, reconstruction errors and the precise epsilon
dependence of a reduction remain unresolved.

## Budget, event convention, output and pre-run gates

One global ledger covers all requested eleven cases and per-curve validation.
Default caps are 1,000,000 instrumented events and 60 monotonic elapsed seconds.
CLI caps can only be lowered. Every recorded operation checks both caps before
execution. Stop on the first exceeded cap; do not restart with a fresh budget,
skip a losing case, or claim completion from a prefix. JSON retains completed
cases and the partially completed active case, with its phase, completed rows,
partial event vector and stop reason. A budget stop or arithmetic failure exits
2; a fully completed diagnostic exits 0. No correlation is calculated from an
incomplete pointwise table; any already completed family is explicitly part of
an incomplete case if a stop occurs later. JSON always distinguishes total
requested/completed case counts.

The event vector records field adds/subs/muls; field inversions; exponent bits
and exponent multiplications; character evaluations/products; group additions
and binary scalar multiplications/bits; EDS requests/recurrence nodes; cache
reads/writes/hits; dictionary/table accesses; explicit comparisons; loop
iterations; random draw calls; and the listed integer arithmetic/Euclid work.
`exponent_muls` is a breakdown counter that **overlaps** `field_muls`; both
ticks are included in the conservative event-stop total. These are instrumented
events, not a disjoint count of mathematical operations. An inversion executes
binary exponentiation to p-2 and charges its field multiplications; q^2's
inverse modulo p-1 instead uses counted integer Euclid. Character and division-
polynomial cache hits remain charged. No unbounded integer exponentiation,
built-in modular pow/inverse, or hidden division-polynomial library is used.

The ledger is limited operational accounting: it does not count every Python
instruction, arbitrary-precision bit operation, allocator/GC byte, dictionary
hash computation, PRNG internal operation, file/hash/JSON metadata operation,
or hardware memory transaction. It cannot establish a whole-solver cost or
matched wall-clock advantage. The elapsed observation starts before arithmetic
validation and ends before final source hashing/JSON writing; output finalization
can run after the arithmetic cutoff. Event categories and exclusions must
accompany any quoted counts. No physical RAM peak is measured: the pointwise
EDS cache is O(log(p+q)), while diagnostic labels, point/phi tables and the
generator EDS batch cache require O(q) stored values, plus O(p) validation data.

Expected work, without asserting measured constants:

- Curve admission/enumeration: O(p) field operations/dictionary accesses, plus
  counted trial-division primality and Euclid; no p-by-p point search.
- Each pointwise phi: O(log(p+q)) recurrence nodes, plus O(log p) field
  multiplications for inversions, root power and its character. A conservative
  bound for the two large-index queries is 18*(ceil(log2(p-1+q))+1) recurrence
  nodes, each with at most six field multiplications and one field subtraction.
- Label generation: q orbit additions per case, with actual inversions;
  O(q*log q) additional group additions on the two exact fixtures for independent
  scalar checks, and O(log q) boundary scalar checks in larger cases.
- Normalization checks: 2*(q-1) unwrapped identities, each including an actual
  power with exponent n*n. Two large phi queries do not make this batch free.
- Correlation/control work: O(q*sum_A len(A)+q*|family|*|seeds|) charged character
  products/accesses/shuffle operations after the full pointwise table is built.

The requested tables contain 1,436 nonidentity labelled rows. The conservative
recursion bound does **not** guarantee all eleven cases fit the global 1M-event
cap. A partial run is an expected possible outcome, not permission to enlarge
the cap. No run or elapsed/operation estimate has yet been measured. Before
authorization, an independent reviewer must inspect the recurrence constants,
even-term handling of zeros, actual whole-ratio exponent, scalar/group code,
counter overlap/exclusions, modulo-versus-unwrapped window indexing, output
failure propagation, fixed sign/control policy, and the partial-output path.
Any mathematical mismatch fails implementation validation before interpreting
correlations. Successful syntax checking alone establishes none of these.
