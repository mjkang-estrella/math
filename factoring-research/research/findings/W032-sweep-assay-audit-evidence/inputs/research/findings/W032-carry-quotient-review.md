# W032 carry-quotient and small-tail depth review

**Disposition: accept the new divisibility and uniform small-tail obstruction;
accept the unguarded quotient construction and its stated conservative bit-cost
envelopes, with the implementation and scope qualifications below. Verified
complete factoring improvement: NONE.**

The small-tail guard forces `R=O(log N/log log N)` and leaves an integer gcd
argument of magnitude `N^o(1)`, uniformly over legal stencils. The unguarded
construction has no such guard and computes the same filtered observation
from a degree-`2R-2` polynomial modulo `N^(2R)`. Its shared acquisition and
integer convolution are executable mathematical algorithms. Neither supplies
a separating-yield theorem, a factoring-time bound, or a novelty claim.

The essential qualifications are:

- Check the **full** denominator condition through `2R+1`. Inverting only the
  denominators used by the shortened recurrence does not certify its imported
  truncation and digit-comparison theorem.
- Use the actual unwrapped integer progression. Reducing each input modulo
  `N` and then evaluating its canonical digit can change the observation.
- Evaluate the residue polynomial modulo `M`, but perform the final convolution
  **over the integers**, with signed sums recovered exactly before division.
- The cost comparisons are upper bounds for specified acquisition methods.
  They do not lower-bound scalar acquisition, optimal carry evaluation, or
  factoring. All point, denominator, endpoint, and gcd failures remain visible.

## Evidence and boundaries

The reviewed versions are the frozen copies of
`W032-exact-carry-quotient.md` and `W032-small-tail-depth-bound.md` in
[inputs](W032-carry-quotient-review-evidence/inputs/research/findings/).
Their respective SHA-256 hashes are
`6439746a120c49bf128a7554b455cfc18c51edfb763bc939ef24145e78dc50a0` and
`bd794d553a07cb43001cfb2a31111a9f570b732ad18e4eeb08e41d95ead8b617`.
The [full brief](W032-carry-quotient-review-evidence/brief.txt) and
[input manifest](W032-carry-quotient-review-evidence/input-manifest.json)
freeze twelve local inputs. The five governing documents were read. STATE
was consulted for coordination only; it does not enlarge this assignment.

The accepted scalar review supplies the diagonal, justified tail truncation,
and common-denominator floor identity. The original unit-step proposal is
used only to identify its variables and the exact guard. This review proves
the **new** exact division and depth restriction; it does not repeat that
live review's coefficient-table construction, conservative guard/sign
implementation, or generic cost audit. Fixed-label/period filters, their
separate reviews, W033, and the assay implementation/results are excluded.

This is a symbolic prose proof. There were no numerical substitutions,
experiments, sweeps, assay reruns, symbolic-program evaluations, Lean changes,
installs, commits, or delegation. Python was used only for freezing sources,
recording provenance, and checking file integrity. Only this report and its
assigned evidence directory were written. No project checks were needed:
no shared implementation changed. The fast-arithmetic claims are mathematical
cost bounds, not a benchmark or a refinement of the repository's Python.

## 1. Conventions and the imported interface

Assume `N>1` is odd composite, `R>=1`, and `leastprime(N)>2R+1`. This last
condition is an executable preprocessing obligation, not a factor supplied
as input. Put

```text
D_j = 4^j (2j+1)!,       E_j(Y) = product_(i=1..j) ((2i-1)^2-Y),
D = D_R,                 M = N^(2R),              Q = N*M,
m = 2R+1,                w_i = (-1)^(m-i) binom(m,i).
```

Canonical residues `[x]_q` lie in `[0,q)`. For a sequence on an integer
progression `a_i=a0+i*h`, write `Delta_h^m f = sum_i w_i f(a_i)`.
For polynomial degree less than `m`, this sum is zero over any commutative
coefficient ring. An integer-coefficient lift of a residue polynomial is
therefore sufficient; its canonical value sequence need not be an ordinary
integer polynomial.

The accepted scalar identity gives, on unit inputs,

```text
V_R(a) = [sum_(j=0..R) N^(2j) E_j(N^2) D_j^(-1) a^(2j)]_Q,
V_R(a) = M*d_R(a) + r(a),       0<=d_R(a)<N,    0<=r(a)<M.
```

Here inverses are taken at the displayed modulus, where they are units.
For `j>R`, the accepted proof instead uses the integral raw coefficient
`alpha_j` and the explicit factor `N^(2j-1) alpha_j U^(-1)`, with
`U=(-4)^((N-1)/2)`. This vanishes modulo `Q`. It does **not** assume
`N | alpha_j` for those distant indices or invert their factorials.

The original scalar input domain is canonical units `0<=a<N`. The same
polynomial identity extends to arbitrary integer units if the scalar
computation is performed at that integer input: the accepted cancellation
and congruence proof is algebraic in `a`. This extension does not justify
replacing an integer input by `[a]_N`. In particular, canonical endpoint
checks are required when the original canonical experiment is the consumer.

## 2. New small-tail division

Use the accepted notation `C_k(x)=D G_k(x)` and define the polynomial over
`Z/DZ`

```text
P(A) = -sum_(k<R) N^(-(2R-2k)) C_k(A^2) mod D.
```

Its degree is at most `2R-2`. Let

```text
epsilon(A) = sum_(k<R) N^(2k-2R) C_k(A^2),
sigma_i = 1 if epsilon(a_i)<0, else 0,
y_i = sigma_i + [P(a_i)-sigma_i]_D.
```

Regardless of changes in `sigma_i`, `y_i=P(a_i) mod D`. Hence, on any
integer arithmetic progression,

```text
D | Delta_h^m y,         c_small := Delta_h^m y / D is an integer.
```

This part does not need the small-tail guard. The guard is needed for the
identification with the digit filter and the strict size estimate.
For that estimate, let `h_i` be the accepted floor label and put
`J_i=C_R(a_i^2)+h_i*N`, so `J_i=P(a_i) mod D`. Under
`|epsilon(a_i)|<1`, the defining sign correction gives

```text
f_i := frac((J_i+epsilon(a_i))/D) = (y_i+epsilon(a_i))/D in [0,1).
```

Since `Delta_h^m epsilon=0`, it follows that
`c_small=sum_i w_i f_i`. The positive and negative weight totals are each
`2^(m-1)=4^R`; a weighted sum of numbers in `[0,1)` therefore satisfies

```text
|c_small| < 4^R.
```

The strict inequality is not a consequence of `0<=y_i<=D` alone. It uses
the fractional parts and annihilation of epsilon, so it survives both
sign changes and `epsilon=0`.

The imported digit identity is `D*d_R=C_R-y mod N`. Its order-`m`
difference, and the unit `D`, now imply

```text
gcd(Delta_h^m d_R,N) = gcd(Delta_h^m y,N) = gcd(c_small,N).
```

Thus the factor `D` in the older residual estimate supplies no larger
useful gcd argument. The displayed division is ordinary exact integer
division, with negative sums allowed.

## 3. The exact unit-step guard bounds depth uniformly

This section uses `h=1` and the guard at every point of the full stencil.
For `R>=2`, put `d=2R-2`. Only the term `k=R-1` contributes to the leading
coefficient of epsilon. The accepted diagonal gives

```text
[A^d] epsilon(A) = L_R/N^2,
L_R = (D_R/D_(R-1)) product_(j=1..R-1)(2j-1)^2
    = 4(2R)(2R+1) product_(j=1..R-1)(2j-1)^2 > 0.
```

Take the order-`d` difference on the first `d+1` points of the stencil.
This is a real polynomial identity, independent of `a0`:

```text
Delta_1^d epsilon(a0) = d! L_R/N^2.
```

Every epsilon value used here has absolute value strictly less than one.
The triangle inequality and the exact total `sum_i binom(d,i)=2^d` give

```text
0 < d! L_R/N^2 < 2^d,
N^2 > d! L_R/2^d.                                      (A)
```

No bound on individual coefficient magnitudes, no conservative sufficient
guard, no modular root count, and no favorable sign pattern is used.
This is a necessary condition; passing (A) is not a sufficient guard.

Here is a uniform inversion rather than a pointwise asymptotic assertion.
Let `t=R-1>=1` and use natural logs. Since `(2t)! >= (t!)^2` and
`product_(j=1..t)(2j-1) >= t!`, (A) implies

```text
N^2 > 4(2R)(2R+1) (t!)^4 / 4^t,
log N > 2t log t - (2+log 2)t.                         (B)
```

The last inequality uses `log(t!) >= t log t-t`, obtainable by integrating
`log x`. Its constants do not depend on the start, the signs, or `N`.
Write `L=log N`. If `t<=sqrt(L)`, then `R=O(L/log L)` directly. Otherwise
`log t > (log L)/2`, and (B) gives, for sufficiently large `N`,

```text
t < L / (log L-(2+log 2)) <= 2L/log L.
```

Both branches, including bounded `R`, have a common threshold and constant.
Consequently the target's conclusions hold uniformly:

```text
log N >= 2R log R - O(R),
R = O(log N/log log N),
log(4^R)/log N = O(1/log log N) -> 0.
```

For each fixed `eta>0`, for all sufficiently large `N`, **every** legal
small-tail stencil has `4^R<N^eta`. If `leastprime(N)>=N^eta`, then
`c_small=0` gives gcd `N`, while nonzero `c_small` gives gcd `1`. The
filtered gcd cannot be proper. This covers repeated prime factors too;
there is no squarefree or semiprime assumption.

For `R=1`, `D=24`, `epsilon=D/N^2>0`, and `P=0 mod D`, so `sigma=0`
and `y=0`. Whenever the guard holds, `c_small=0` and the filtered gcd is
`N`. This symbolic special case does not use the growing-depth argument.

The obstruction concerns this guarded order-`2R+1` **combined filter**.
It says nothing negative about individual digit gcds, initial point gcds,
an unguarded construction, a different selector, or factoring generally.

## 4. Unguarded residue polynomial and quotient

Reduce the imported degree-`2R` identity modulo `M`. Its `j=R` term
vanishes because its denominator is a checked unit and it contains
`N^(2R)`. The distant `j>R` terms vanish by the integral raw-coefficient
argument already described. Therefore

```text
r(a) = [P_R(a)]_M,
P_R(A) = sum_(j=0..R-1) b_j A^(2j) in (Z/MZ)[A],
b_j = N^(2j) E_j(N^2) D_j^(-1) mod M.                 (C)
```

This is degree at most `2R-2`; reducing it does not need any inverse of
`a`. Evaluation is defined even at nonunit points. Comparison to the
original normalized scalar is asserted only on its unit branch.

Choose arbitrary integer-coefficient lifts of the full polynomial modulo
`Q` and of `P_R` modulo `M`. Polynomial annihilation on the actual
unwrapped progression proves

```text
Delta_h^m V_R = Q*t,      Delta_h^m r = M*c,      t,c in Z.
```

Applying the difference to `V_R=M*d_R+r` and cancelling the nonzero
integer `M` gives

```text
Delta_h^m d_R = N*t-c,
gcd(Delta_h^m d_R,N) = gcd(c,N),
c = (sum_(i=0..m) w_i r(a_i))/M,        |c|<4^R.       (D)
```

The strict estimate follows directly from `0<=r(a_i)<M` and the equal
positive/negative weight totals. No label period, guard, approximate
derivative, or inverse of `N` is involved. Neither the step `h` nor point
differences must be units. Modulus `M` alone suffices to **compute** `c`;
the extra `N` digit in `Q` is needed only in the proof relating it to
the original digit difference. Taking just the difference modulo `M`
would return zero and destroy the quotient information.

As a consistency check, on a guarded stencil the accepted floor lift
satisfies `r(a_i)/M=f_i=(y_i+epsilon(a_i))/D`. Thus `c=c_small` exactly,
not merely up to a unit or gcd equivalence. Removing the guard genuinely
extends the domain of the same quotient observation.

At `R=1`, (C) is the constant polynomial `1`, so all differences vanish
and `c=0`, also without a guard. For growing `R`, choosing
`R=Theta(log N)` is compatible with the canonical width `m<N` for large
`N`. The separate least-prime and all-unit conditions still have to hold
or produce their paid exits. Width alone does not guarantee a legal
all-unit progression. Larger permitted support is no proof that a
nontrivial quotient, let alone a proper gcd, occurs.

## 5. Coefficients and full denominator preprocessing

The recurrence in the target is exact, because

```text
E_j(N^2) = E_(j-1)(N^2) ((2j-1)^2-N^2),
D_j/D_(j-1) = 4(2j)(2j+1).
```

Starting with `b_0=1` and reducing every product modulo `M`, this proves

```text
b_j = b_(j-1) N^2 ((2j-1)^2-N^2) [4(2j)(2j+1)]^(-1) mod M.
```

There is no propagation of numerical error. Reduced precision for later
coefficients is optional and is not assumed in the cost proof.

The actual truncated recurrence uses `j=1,...,R-1`. Its denominator
checks alone do not certify `D_R`: the omitted factors at `j=R` matter
to the truncation proof. One completely explicit prefilter, using only
`N,R`, is to test `gcd(t,N)` for
`2<=t<=min(2R+1,floor(sqrt(N)))`. On the composite-input promise, a
nonunit here is a proper factor because `t<N`. If the scan reaches the
square root without finding a factor, the composite promise is false.
Otherwise its successful unit branch certifies `leastprime(N)>2R+1`.
This costs `O(R)` gcds on `O(bitlen(N))`-bit integers, plus a paid integer
square root if used. Testing all integers requires no prime oracle.

Alternatively, a product check can include all
`q_j=4(2j)(2j+1)`, `j=1,...,R`, whose product is exactly `D_R`.
A full gcd `N` from an aggregate product is not a proper split; localize
among the known factors, with the work charged. Forming that product
modulo `N` or `M` avoids storing a huge unreduced factorial.

Once the needed denominators are certified units, prefix products modulo
`M`, one extended-gcd inverse, and a reverse pass produce all their
inverses using `O(R)` modular multiplications. Every prefix is a unit.
One may include `q_R` in this batch without changing the cost, even though
its inverse is not needed to produce the `R` lower coefficients.

## 6. Bit cost and monic evaluation over the composite ring

Let `ell=bitlen(N)`, `B=bitlen(M)=Theta(R*ell)`, and
`T=K+m=K+2R+1`, where `K>=1`. Assume canonical supplied points for the
stated input-width bound. General supplied wide integers require their
actual reading/reduction cost in addition. Soft notation below suppresses
logarithms of the bit/length parameters, not a declared factor `ell` from
binary exponentiation. In particular, when `R,K` are polynomial in `ell`,
only polylogarithms of `ell` are suppressed.

We use standard fast integer multiplication, division, and extended gcd;
the primary arithmetic reference is Brent–Zimmermann, *Modern Computer
Arithmetic*, sections 1.4, 1.6.3, 2.3.3 and 2.5.1. Multiplication and
division are soft linear in operand length, and gcd/inversion adds only
logarithmic factors. [Author-hosted text, version 0.5.9](https://www.loria.fr/~zimmerma/mca/mca-cup-0.5.9.pdf).
Its unchanged source and provenance are frozen in the evidence. These
standard primitives are assumptions of the chosen implementation model;
no claim about a Python big-integer timing is inferred.

Constructing `M` by powering costs soft `O(B)`; all intermediates have
`O(B)` bits. The coefficient recurrence and batch inversion cost soft
`O(R*B)` and retain `O(R*B)` coefficient/prefix bits. The prefilter above
costs soft `O(R*ell)`. Even without a full batch inverse, independently
inverting `O(R)` denominators has the same conservative soft envelope.

For completeness, composite-ring evaluation follows constructively:

1. Build a balanced product tree of monic factors `X-[a_i]_M`.
2. Reduce `P_R` down the tree. Every divisor is monic, so division is
   defined over `Z/MZ`. At a leaf the remainder is `P_R(a_i)`.
3. Implement fast monic division by reversing the divisor: its constant
   coefficient becomes `1`. Power-series inversion by
   `g <- g*(2-f*g)` doubles the certified precision, using only ring
   additions and multiplications. It never divides by a point difference.

Repeated points and nonunit differences cause no problem. This is
evaluation, not interpolation or a CRT reconstruction requiring coprime
linear factors. No roots of unity in `Z/MZ` are assumed.

To justify the bit conversion directly, multiplication of two length-`s`
residue polynomials can lift coefficients into `[0,M)`, pack with slots
of `2B+ceil(log2(s+1))+2` bits, multiply integers, unpack, then reduce
each coefficient modulo `M`. Each unreduced convolution coefficient is
less than `s*M^2`, so slots cannot carry. This costs soft
`O(s*(B+log(s+1)))`. Fast monic division has the same soft envelope by
the doubling construction. Across the tree, degree totals are `O(T)` per
level; `deg(P_R)<T` for all `K>=1`. Consequently multipoint evaluation
costs

```text
soft O(T*(B+log(T+1))).                               (E)
```

One can pad a tree to a power of two with repeated points and discard
the added outputs; this changes sizes only by a constant factor. If
`K` is much larger than `R`, (E) remains a valid bound. It does not reuse
an `O(R)`-point bound while silently making `K` large. Product/remainder
trees, coefficient arrays and arithmetic scratch require explicit storage;
soft `O(T*(B+R+log(T+1)))` bits is a conservative workspace envelope,
including materialized convolution arrays.

For one stencil, `T=m+1=O(R)`. The coefficients and evaluation therefore
cost soft `O(R^2*ell)`. Generating its binomial weights by the exact
recurrence `binom(m,i+1)=binom(m,i)*(m-i)/(i+1)` costs soft `O(R^2)`;
the explicit weights have `O(R)` bits each. The signed numerator has
`O(B+R)` bits, since its magnitude is strictly less than `M*4^R`.
Its exact division and final gcd add soft `O(B+R+ell)`, while a direct
weighted sum still fits soft `O(R*(B+R))`. Reading canonical points,
point gcds, endpoint checks, and witness validation fit the same total.

Thus the target's single-stencil soft `O(R^2 log N)` envelope is supported.
The accepted independent-scalar method has soft `O(R*ell^2)` per point,
hence soft `O(R^2*ell^2)` for `O(R)` independent points. The new bound
removes that method's factor of `ell` in this comparison, up to the
specified soft factors. Both are **upper bounds**, and other methods may
share scalar work. This is not a lower bound proving an optimal speedup.
It computes the combined filter, not every individual top digit. The
end-to-end factoring comparison is still NONE.

## 7. Consecutive starts: exact signed convolution and large K

For starts `s=0,...,K-1`, let `r_j=r(a0+j)`, `0<=j<T`. Define

```text
A(X) = sum_(j=0..T-1) r_j X^j,
H(X) = sum_(i=0..m) w_(m-i) X^i = (1-X)^m.
```

The coefficient of `X^(s+m)` in `A*H` is exactly
`sum_(i=0..m) w_i r_(s+i)`. These **K interior coefficients** are
divisible by `M`. Boundary coefficients outside that range need not be.
This proves the proposed `K+m` point count and the kernel orientation.

A fully specified safe signed-packing method is to split `H=H_+-H_-`,
where both polynomials have nonnegative coefficients. Each has coefficient
sum `2^(m-1)=4^R`. Thus every coefficient of either `A*H_+` or `A*H_-`
is strictly less than `M*4^R`, including partial edge sums. Choose a binary
radix `beta=2^q` with, for example, `q=B+m+2`. Pack both nonnegative
products separately. Their integer products have carry-free coefficient
slots. Unpack the slots **before** subtracting corresponding coefficients;
then signs, borrows and a negative final numerator are unambiguous.

The packed integers have `O((T+m)*(B+R))=O(T*(B+R))` bits. Two integer
multiplications and linear packing/unpacking cost soft `O(T*(B+R))`.
The exact divisions of all K interior coefficients add soft `O(K*(B+R))`.
Each quotient has `O(R)` magnitude bits, but its gcd with `N` must also
read the `ell`-bit modulus; all K gcds cost soft `O(K*(R+ell))`. Zero
quotients and full gcds are retained. No modular inverse of `M` exists or
is requested.

Including (E), coefficient setup, weights, point acquisition and gcds,
an explicit conservative batch envelope is exactly of the proposed form:

```text
soft O((K+R)*(R*ell + R + log(K+R+1))).                 (F)
```

The signed convolution itself does not actually need `log K` extra bits
per coefficient: its weight sum bounds the coefficients independently of
`K`. Keeping that term in (F) is harmless and covers the simple full
product-tree packing bound and indexing. There is no suppressed `K*R`
list of separately weighted summands. Compared with independently
materializing each stencil, overlap and convolution remove the repeated
factor of `R` in the dependence on a large K, after the shared setup.
They do not make an exponentially long output list polynomial in `ell`.

For original canonical inputs, check
`0<=a0` and `a0+K+m-1<N`. If the **whole** block is required to be unit,
its length must also be less than every prime divisor of `N`: a block
of `p` consecutive integers contains a multiple of `p`. This is a scope
restriction, not a new factor oracle or a promised way to find such blocks.
Polynomial residues and the integrality of the K quotients are still
well-defined at nonunit points, but the original scalar comparison then
applies only to stencils whose points pass their unit checks. Do not
remove nonunit points and splice the remaining values into a new stencil.
All-unit blocks are a sufficient common scope, not an automatic consequence
of `leastprime(N)>2R+1` for arbitrary K.

The explicit algorithm above performs each output gcd; no unpriced batch
localization is required. Any alternate aggregate-gcd consumer must retain
full-gcd cases and pay for its own localization. Consecutive quotients share
both input data and coefficients; no independent-trial probability follows.

## 8. Algorithm scope, failures, and disposition

This is a supplied-parameter primitive: input `N,R,a0,h` for one stencil,
or `N,R,a0,K` for a consecutive block. A factoring proposal must give a
paid `N`-only rule or sampler for those parameters. The proof uses no hidden
factor, order, roots, or size-dependent advice. Polynomial time in `ell`
requires bounding all attempted depths, points, starts, input widths and
repetitions, not merely choosing one `R=Theta(ell)`.

An executable consumer records the following branches separately:

- An even-input or denominator-precheck factor is an ordinary preprocessing
  success. A product gcd equal to `N` needs localization, never acceptance.
- A proper `gcd(a_i,N)` is an ordinary point-gcd success. A full point gcd
  invalidates scalar normalization; noncanonical endpoints invalidate the
  requested canonical stencil. Alternative unwrapped inputs must be declared.
- The unguarded primitive has no tail-guard rejection. If a guarded version
  is used, any failed guard rejects that simplified evaluation, without
  being discarded from an attempted-trial denominator.
- A nondivisible purported numerator contradicts the proved invariant and
  signals an implementation/scope error. Never round it to manufacture `c`.
- `gcd(c,N)=1`, `gcd(c,N)=N` (including `c=0`), and invalid or unstarted
  attempts are failures of this quotient channel. Return a factor only
  when `1<g<N` and `g|N`, with its check charged.

No finite attempt was run in this review, so there is no empirical success
denominator, timing, or discarded trial to report. A large `4^R` is only
a support bound; it supplies no useful mass, no independence, and no
deterministic cover. A small bound rules out this filter on the stated
large-least-prime family only when combined with the proved guard-induced
depth restriction. No general algorithmic lower bound follows.

Accept the two targets at these stated mathematical levels. The small-tail
proposal's failed premise was that removing factorial stencil spacing
would also remove every factorial depth restriction. The exact guard
reintroduces one through its highest nonzero real finite difference. The
unguarded residue evaluator removes that premise constructively while
preserving and paying for the canonical reduction and quotient.

The next proof that could change the factoring disposition is a useful
separating-support theorem for an explicit `N`-only schedule or sampler of
unguarded quotients, together with its total paid work and all failures.
This review does not select or run a diagnostic. Neither accepted algebra
nor cheaper acquisition establishes that missing yield statement.

The delivery [manifest](W032-carry-quotient-review-evidence/manifest.json)
lists this report and every evidence payload, excluding only the manifest
itself. Its SHA-256 is printed by an external terminal check and repeated
in the handoff, avoiding a self-referential hash. The
[integrity verifier](W032-carry-quotient-review-evidence/verify_manifest.py)
checks file-set completeness, byte counts, hashes, and frozen input/source
manifests without executing any research algorithm.
