# W032 arrangement-cover review

**Disposition: accept the symbolic superset cover and its conservative cost
bound, with the explicit horizontal-boundary convention in section 4.
The connection to the original lift family imports the separately assigned
breakpoint identity; it is not re-proved here. Verified complete factoring
improvement: NONE.**

The construction removes the numerical factor `a0` from the specified
enumeration cost. It enumerates gcd arguments containing every actual lift
value, with possible extras. It does not determine orbit membership, count
uniform-lift successes, guarantee a useful factor, or improve a proved
factoring complexity bound. The simple slab implementation has
`O(R^6)` samples and soft `O(R^7*(bitlen(N)+R))` bit work, including base
acquisition and all sample gcds under the accepted arithmetic model.

There is one necessary completion of the literal enumeration wording:
boundary-coordinate division is only for nonhorizontal lines. If `i=0`
and `b_0=0`, the listed line is the entire top edge `z=N`, so “all
coordinates where it meets the edge” is not a finite list. Ignore this
overlap geometrically and keep the two square endpoints. This repairs
the literal instruction without changing coverage, sample counts, or
the bit envelope. No algebraic counterexample to the repaired cover was
found; the proof below treats every permitted parameter symbolically.

## Evidence, ownership, and imported dependencies

The full [assignment](W032-arrangement-cover-review-evidence/brief.txt) and
sixteen local inputs were frozen in the
[input manifest](W032-arrangement-cover-review-evidence/input-manifest.json).
The complete target is the
[frozen arrangement note](W032-arrangement-cover-review-evidence/inputs/research/findings/W032-lift-arrangement-cover.md),
SHA-256 `4fcfb67ec688954ac707661084b1d17ff7bf88f750276add4cdbf71f20b5d7c0`.
The five governing documents were read in full. STATE was inspected for
coordination, not used to enlarge this assignment.

The completed carry review is an accepted interface: exact unguarded
quotient, full denominator prefilter, linear coefficient recurrence,
shared monic multipoint acquisition, signed integer convolution, and
small-tail obstruction. Its supplied external manifest anchor
`788e44887bd326054d19e21cd46dee225c20bb777f1245357ea7feed4aea64eb`
matches, and every one of its 24 payloads was independently hash-checked;
see [intake](W032-arrangement-cover-review-evidence/accepted-carry-intake.json).
The report was read in full; its external source texts were not re-audited.
The parent's subsequently available carry intake and disposition were
[frozen separately](W032-arrangement-cover-review-evidence/supplemental-input-manifest.json)
and read. They agree with this dependency status.

The final stability check found two concurrent live edits: the carry note
added its accepted status and already-imported qualifications, and the
parent intake added a hash record for the separate sweep review. These
[later bytes](W032-arrangement-cover-review-evidence/observed-later-manifest.json)
are preserved without replacing the reviewed inputs. The arrangement target
and accepted carry-review report remained unchanged. The separate sweep
review itself was not read or adopted here.

The precise live dependency is equation (3) of the
[frozen breakpoint note](W032-arrangement-cover-review-evidence/inputs/research/findings/W032-lift-breakpoint-sweep.md):

```text
c(w) = c0 - sum_(i=0..m) w_i floor((b_i+(a0+i)w)/N),
                         w in {0,...,N-1}.                 (D)
```

That note's Taylor/lift derivation has its own symbolic review, LIVE when
this assignment was issued.
This review proves the new implication from (D) to a finite superset;
it does not certify the live dependency by association with the accepted
carry review. Likewise it does not duplicate the general Taylor,
monic-evaluation, or convolution audits. There is no new convolution
claim in the arrangement algorithm.

The separate frozen diagnostic uses `a0=1` and three input groups.
Its protocol was read only to preserve the scope boundary. Neither its
implementation nor its result files were inspected or executed. The
arrangement is not part of that diagnostic. No numerical evaluation,
parameter sweep, symbolic-program evaluation, research run, code/Lean
edit, project-check run, install, commit, or delegation occurred here.
Only this report and its assigned evidence directory were written.
Inline Python performed copying, metadata recording, and file hashing
only. The mathematics below is a prose proof, not a machine-checked proof
or a benchmark. There is no novelty claim or new external-literature audit.

## 1. Domain and supplied interface

Retain the breakpoint note's domain:

```text
N > 1 odd composite, R >= 2, m = 2R+1, L = 2R-2,
M = N^(2R), leastprime(N) > 2R+1,
a_i = a0+i, 0 < a0, a0+m < N, gcd(a_i,N)=1,
w_i = (-1)^(m-i) binom(m,i), 0 <= i <= m.
```

Here `w_i` are signed weights; `w` without a subscript is the lift
parameter. Denominator and point-unit hypotheses are paid checks, not
extra information supplied by a hidden factor. The accepted acquisition
returns exact canonical residues and their decomposition:

```text
r_i = 1+N^2 u_i,              0 <= u_i < N^L,
u_i = v_i+N^(L-1)b_i,        0 <= v_i < N^(L-1),
                             b_i integer, 0 <= b_i < N,
c0 = Delta^m u_i/N^L in Z,   |c0| < 4^R.
```

As usual, `Delta^m s_i` means `sum_i w_i s_i`. The weight identities are

```text
sum_i w_i = 0, sum_i i*w_i = 0,
sum_(w_i>0) w_i = sum_(w_i<0) (-w_i) = 2^(m-1) = 4^R.
```

The geometric coverage proof requires only positive integer `N`, integer
`m>=2`, `b_i` in the canonical range, and integer `c0`. The original
scalar interpretation and the sharper magnitude bound use the additional
accepted data above. No claim for `R=1` is made by this lift construction.

## 2. Cancellation and the exact superset statement

For any actual integer lift parameter, Euclidean division gives
`a0*w=N*t+z`, with integer `t` and `0<=z<N`. Then exactly

```text
floor((b_i+(a0+i)w)/N)
    = t + floor((b_i+z+i*w)/N).
```

The first weight identity cancels `t`, giving

```text
c(w) = C(w,[a0*w]_N),
C(x,z) = c0 - sum_i w_i floor((z+i*x+b_i)/N).          (1)
```

Define the square as `S=[0,N) x [0,N)`, and define its open chambers as
the connected components of `(0,N) x (0,N)` after removing the listed
lines. The assertion to prove is the set inclusion

```text
{c(w): integer 0<=w<N}
    subset {C(x*,z*): samples produced by the slab algorithm}.       (2)
```

Equation (1) does not require enumerating `t`, `w`, or the orbit
congruence `z=a0*x mod N`. Every sample output is an integer because
`c0`, the weights, and the floors are integers. Thus any proper
`gcd(C(x*,z*),N)` is a valid factor even if the sample's chamber contains
no integer point, or contains no point of the actual orbit. Such an
output must not be reported as an attained original quotient.

If all sample gcds are checked and none is proper, (2) rules out proper
filtered gcds in this one actual lift family. That implication is
one-way: an extra successful argument need not witness a successful
lift. A partial traversal, failed acquisition, or budget stop does not
certify family exhaustion. Counts of chambers, slab samples, or distinct
values are not counts of uniform integer lift parameters.

## 3. All floor boundaries and the one-sided representative

For `0<=x,z<N` and `0<=b_i<N`,

```text
0 <= z+i*x+b_i < (i+2)N.
```

The positive integer floor thresholds that can meet the square therefore
have exactly the advertised range `k=1,...,i+1`:

```text
ell_(i,k): z+i*x=d_(i,k),  d_(i,k)=kN-b_i.
```

The threshold `k=0` can occur only on the lower boundary: for `i>0`
it requires `x=z=b_i=0`, while for `i=0,b_i=0` it is the bottom edge.
It creates no interior discontinuity or missing open chamber. Negative
thresholds and thresholds `k>=i+2` cannot occur. Lines that touch a corner,
lie on the upper boundary, or do not enter the interior may be retained
in the initial list; they contribute no spurious interval if the strict
height filter is respected. There are at most
`J=(m+1)(m+2)/2=O(R^2)` records.

There is an explicit uniform perturbation for every integer point of
`S`. Given integer `(x,z)` there, put

```text
delta = 1/(2(m+1)),  x' = x+delta,  z' = z+delta.
```

Both new coordinates lie strictly between `0` and `N`, since the old
coordinates are at most `N-1`. Each integer numerator
`s_i=z+i*x+b_i` increases by `(i+1)delta`, which is positive and at most
`1/2`. The next larger multiple of integer `N` has distance at least one
from `s_i`. Consequently no numerator crosses its next threshold. If
`s_i` is already a multiple of `N`, the positive displacement selects
precisely the value of mathematical floor at that multiple. The displaced
numerator is not any integer, so the new point lies on no listed line.
All floors are unchanged, simultaneously for every `i`.

This proves the required representative even at line intersections,
the bottom and left edges, and the origin. It also shows why the signs
of the gradients matter: every change is positive because `i>=0`.
There is no tie-breaking order of floor changes and no zero-dimensional
or edge-only output missing from the integer domain. The argument does
not add the excluded edges `x=N` or `z=N` to that domain.

Floors are constant on a connected open chamber, as a floor could change
only on one of the listed threshold lines. Combined with the perturbation,
it remains only to show that the finite slab algorithm visits every chamber.

## 4. Complete slab algorithm, including degeneracies

Use exact rational records with positive denominators. The following is
a complete interpretation of the target's algorithm.

1. Generate the `J` line records. For equal slopes, compare intercepts.
   Distinct parallel lines have no pair intersection. Coincident records
   may be deduplicated, with that work paid; retaining them and later
   deduplicating heights is also correct. In this specific family no two
   distinct `(i,k)` records coincide: fixing `i`, different `k` give
   different intercepts, and different `i` give different slopes.
2. For `i!=j`, solve the intersection exactly as
   `x=(d_(i,k)-d_(j,l))/(i-j)`, `z=d_(i,k)-i*x`.
   Retain its x coordinate if the point belongs to the **closed** square
   `[0,N]^2`. Allowing boundary intersections is harmless and avoids an
   ambiguity in “inside.” Repeated intersections contribute repeated
   rational records before deduplication.
3. For every line with `i>0`, form its bottom and top crossing coordinates
   `d_(i,k)/i` and `(d_(i,k)-N)/i`, respectively, retaining those in
   `[0,N]`. For `i=0`, perform no boundary-coordinate division.
   Its height is constant: an interior horizontal line remains available
   for slab heights, and a boundary-coincident line is ignored as a cut
   of the interior. In particular `i=0,b_0=0,k=1` gives the entire top
   edge, not infinitely many cut coordinates. A generic bottom-edge
   overlap, if an implementation adds that boundary as a line, is treated
   the same way.
4. Add `0,N`, sort the rational x coordinates by exact cross-products,
   and deduplicate exact equals. Do not create slabs of zero width.
5. For each consecutive pair `l<r`, choose `x*=(l+r)/2`. Evaluate all
   heights `h_(i,k)=d_(i,k)-i*x*`. Keep only `0<h_(i,k)<N`, add `0,N`,
   sort exactly, and deduplicate. In every resulting positive-height gap
   choose its midpoint `z*` and evaluate all floors defining `C(x*,z*)`.
   Test its gcd and validate any reported proper factor.

Step 3 is the one local completion needed for the literal “all coordinates
where a line meets an edge” wording in target lines 56–59. The permitted
symbolic condition `b_0=0` exhibits the overlap; no numerical research
case is needed. Omitting horizontal edge solves repairs it. This report
does not edit the parent's source.

To prove completeness, take any open chamber. It is an open subset of
the plane, so it contains a point whose x coordinate is not in the finite
cut list. Let `(l,r)` be that point's slab. Within this slab a line cannot
enter or leave the square through the top or bottom, because every such
crossing is a cut. Two active nonparallel heights cannot change order,
because an intersection in the square is a cut. Parallel distinct heights
never change order. Coincident heights are a single geometric boundary.
Thus the active height order and every positive gap persist across the
whole slab. Each gap defines a connected band in the complement of the
lines, and its midpoint sample at `x*` belongs to the same chamber as
every point of that band. The chamber under consideration therefore has
a sample.

A chamber cannot be confined to a single cut x coordinate, since it is
open. Crossings at `x=0,N` or at square corners do not create additional
slabs; those endpoints are already present. Multiway intersection ties
are simply one deduplicated cut. Distinct nonparallel heights cannot tie
strictly inside a sampled vertical interval: that would make `x*` a cut.
Exact height deduplication also handles any retained coincident records.
Even if there are no interior lines, the square's midpoint is sampled.
No sample lies on a line or on a square boundary.

Together with section 3, this establishes (2). Orbit membership tests,
lattice feasibility, and a presumed distribution of sampled chambers
play no role in the proof.

## 5. Exact rational sizes and floor semantics

Write `ell=bitlen(N)` and `U=O(ell+log(m+1))`. All initial intercepts
have `U` bits because `|d_(i,k)|<= (m+1)N`.

The reduced denominator of an intersection x coordinate divides
`|i-j|<=m`; its z coordinate has the same denominator. A nonhorizontal
edge crossing has denominator dividing `i<=m`. Endpoints have denominator
one. After filtering to the square, a cut's numerator is at most `N`
times its denominator. Cut comparisons, intersection construction, and
square tests use `O(U)`-bit arithmetic, with constant-factor enlargements
for cross-products.

If adjacent cuts have denominators `q,s<=m`, their midpoint may be stored
with denominator `D=2qs<=2m^2`. Set `x*=A/D`. **All** heights at this
fixed x then have the common denominator `D`:

```text
h_(i,k) = (D*d_(i,k)-i*A)/D.
```

Represent the square boundaries with that denominator too. A height
midpoint has denominator `2D<=4m^2`; writing `z*=B/(2D)`, every exact
floor is the nonnegative integer division

```text
floor((z*+i*x*+b_i)/N)
    = (B+2i*A+2D*b_i) div (2D*N).                    (3)
```

The numerator and denominator in (3) have `O(U)` bits. There is no chain
of unrelated denominator products: form each slab midpoint from the two
original cuts, and use its common denominator for every height. Rational
reduction by gcd is optional and, if done, charged. This establishes the
target's `O(m^2)` midpoint-denominator claim and its constant-factor
height-midpoint claim constructively.

The floor range on the square is `0,...,i+1`. These nonnegative divisions
agree with mathematical floor. Subsequent weighted sums are signed
integer sums: do not reduce them modulo `N`, approximate them, or truncate
any purported rational value. A negative final `C` is legal; use
`gcd(|C|,N)`. At an actual threshold equality the original floor includes
the new integer level, as used in the perturbation proof. Samples themselves
never need a threshold tie convention.

## 6. Magnitude and the number of distinct outputs

From the acquired decomposition,

```text
c0 = Delta^m b_i/N + Delta^m v_i/N^L.
```

For `y_i=z/N+i*x/N+b_i/N`, the first two weight identities give
`sum_i w_i y_i=Delta^m b_i/N`. Applying
`floor(y_i)=y_i-frac(y_i)` in (1) proves the exact real identity

```text
C(x,z) = Delta^m v_i/N^L + sum_i w_i frac(y_i).        (4)
```

If `0<=s_i<h`, then each of the two nonnegative weighted sums formed
from the positive and negative weights is in `[0,4^R*h)`. Their
difference therefore has absolute value strictly less than `4^R*h`.
Use this first with `s_i=v_i/N^L<h=1/N`, and then with
`s_i=frac(y_i)<h=1`. The triangle inequality yields

```text
|C(x,z)| < 4^R*(1+1/N).                               (5)
```

This also applies to extra chamber values, and proves `O(R)` output
bits. It is not a claim that those values are actual quotient outputs.
The original `|c(w)|<4^R` is stronger on the actual family but is not
needed for the superset. Direct summation has only `O(R+log(m+1))=O(R)`
intermediate bits too: each floor is at most `m+1`, and total absolute
weight is `2^m`. Thus no large canceling intermediates are hidden in (5).

For completeness, the geometric region bound needs no arrangement oracle.
Insert distinct lines one at a time into the open square. The next line
meets at most the number of previous distinct nonparallel lines, splitting
its clipped segment into at most one more than that number of pieces.
Each piece can split at most one existing region. Parallel, concurrent,
boundary-only, or coincident lines only decrease this count. Starting
from the square gives at most `1+J(J+1)/2=O(J^2)` regions.

Each chamber has one floor vector, so there are at most `O(J^2)=O(R^4)`
distinct sampled floor vectors, and at most as many distinct `C` values.
Some different vectors can have the same weighted value. No efficient
deduplication is inferred from the cardinality statement. The literal
slab algorithm may revisit a chamber in many slabs and still pays every
floor evaluation and every gcd unless it implements additional paid
bookkeeping. In particular, the region bound does not turn its `O(R^6)`
sample traversal into an `O(R^4)` traversal.

## 7. Complete supplied-parameter cost

Use the accepted fast multiplication, division, and gcd cost model from
the carry review. Soft notation suppresses logarithmic factors in operand
length and list length. This is a mathematical algorithm bound, not a
claim that the repository implements all of these fast primitives.

There are `O(J^2)` pair/edge cut records. Their generation and sort cost
`O(J^2 log(J+1))` rational arithmetic/comparison operations. There are
`O(J^2)` nonempty slabs. Each computes and sorts `O(J)` heights and
samples at most `J+1` gaps, for `O(J^3)` samples total. The height work
costs `O(J^3 log(J+1))` operations. Each sample costs `O(m)` floors and
weighted-sum operations, plus one gcd. Hence the elementary operation
count, with gcd priced separately, is bounded by

```text
O(J^2 log(J+1) + J^3 log(J+1) + m J^3) = O(R^7).
```

The last bound absorbs the sorting logarithm because `J=O(R^2)` and
`log(R+1)=O(R)`. Exact rational arithmetic uses `O(ell+log(R+1))` bits;
weight arithmetic uses `O(R)` bits. Each gcd sees both the `ell`-bit
input and the `O(R)`-bit integer argument, even when that argument is
zero. Consequently the arrangement phase, with all repeated gcds and
factor validations, has the supported envelope

```text
soft O(R^7*(ell+R)).                                  (6)
```

There is no `O(R*a0)` loop. However, the following acquisition and
eligibility costs remain part of the consumer:

- Read `N,R,a0` and check the promised integer ranges, `R>=2`, and
  `0<a0<a0+m<N`. A canonical large `a0` has `O(ell)` bits. Its numerical
  magnitude need not be traversed, but its bits must be read. Noncanonical
  supplied integers require their actual reading/validation cost and are
  outside the advertised canonical input-width envelope.
- Check the **full** denominator branch through `2R+1`, as in the
  accepted carry review. This can use the paid `O(R)` small-integer gcd
  prefilter and its stated composite-input handling. Checking only the
  denominators of the shortened coefficient recurrence is insufficient.
  Every ordinary factor exit, full product gcd, and localization cost
  remains separate from a new-channel factor.
- Construct the `m+1=O(R)` actual canonical base points and test each
  `gcd(a_i,N)`. Do not delete failed points and splice a new progression.
  The least-prime condition does not certify an arbitrary supplied start
  as all-unit. The point checks cost soft `O(R*ell)`.
- Import the accepted shared recurrence/evaluation acquisition at modulus
  width `B=Theta(R*ell)`: soft `O(R^2*ell)` for this one stencil.
  Computing the exact quotient and splitting each `u_i` into `v_i,b_i`
  costs at most soft `O(R*(B+R))`. Generate and store all binomial weights
  with paid soft `O(R^2)` bit work. Retain integrality and canonical-range
  checks; a nonintegral purported `c0` is an error, never rounded.
- Process every sample, including duplicate values and gcd outcomes
  `1` and `N`. Use direct individual gcds in this bound; there is no
  unpriced batch-gcd localization. Validate `1<g<N` and `g|N` before
  reporting a factor. An early factor permits early termination for a
  splitter, but complete-family failure requires full traversal.

These base/check costs fit (6) for `R>=2` and canonical parameters. They
are included by domination, not omitted. Actual large lifted inputs
`a_i+12*N^(L-1)w` need not be materialized to evaluate the cover; (D)
is the imported symbolic bridge. If a future diagnostic reevaluates
them, it must charge their `O(R*ell)` widths and full acquisition work.

A streaming implementation retains the cut list, one height list, base
data, weights, and arithmetic scratch. A conservative space bound is
soft `O(R^4*(ell+log(R+1)) + R^2*ell)` bits. Retaining every sampled
value/certificate costs additional `O(R^6*(ell+R))` bits; retaining all
sampled floor vectors adds their actual `O(R)` records per sample.
A seen-set can save later gcds, but its keys, searches, comparisons,
insertion, and storage are paid. No seen-set is assumed in (6).

The parameters are supplied or chosen by an explicitly paid `N`-only
procedure. The statement is polynomial in `R,ell`, not automatically
polynomial in `ell` for unbounded `R` or indefinitely many starts.
With a stipulated `R=poly(ell)`, one traversal is polynomial in `ell`;
that does not imply that any traversal succeeds. A randomized start must
pay its sampling and rejected starts and still needs a useful-yield law.

## 8. Failure accounting and final disposition

The consumer must distinguish invalid parameters, denominator/nonunit
branches, ordinary preprocessing factors, failed base-point eligibility,
construction errors, gcd `1`, gcd `N` (including `C=0`), proper verified
gcds, and incomplete traversals. Failed or unstarted attempts cannot be
removed from a future trial denominator. The exact mathematical algorithm
has a finite paid traversal on its legal branch, but this review provides
no finite runtime measurements or empirical trial denominator.

Accept the common-slope cancellation, complete chamber superset,
one-sided boundary coverage, rational slab enumeration under section 4's
horizontal-edge convention, bounded rational widths, strict magnitude
estimate, and conservative full-work envelope. Accept `O(R^4)` as a
distinct-support upper bound, while charging the actual `O(R^6)` sample
implementation. None of these require orbit membership. The only local
repair is to make the boundary-overlap handling explicit; the target's
mathematical claim and advertised asymptotic envelope otherwise survive.

The saved work is specifically the enumeration of the large common
`a0` slope in the previous literal one-parameter sweep. For small `a0`
this conservative replacement may cost more; it is not a blanket primitive
speedup or a lower bound on any competing method. There is no complete
factoring improvement, all-algorithm lower bound, useful-factor existence
claim, or uniform-lift probability attached to the extra arguments.

The missing theorem is a useful-factor supply statement for the explicit
`N`-dependent candidate set under a bounded, paid `N`-only parameter
schedule or sampler. A proof of that statement, including all failures
and all attempted depths/starts, could change the factoring disposition.
A future finite diagnostic would require its own preregistration and
cannot be folded into or rerun as the live three-group sweep assay.
No such diagnostic is proposed or executed in this review.

The [delivery manifest](W032-arrangement-cover-review-evidence/manifest.json)
covers this report and every owned evidence payload except itself. Its
SHA-256 is checked externally in the terminal and supplied in the handoff.
The evidence records source stability and actual read scope; hash checks
establish byte identity, not mathematical correctness.
