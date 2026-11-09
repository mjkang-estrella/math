# W032: vary both the start and the step of the lifted stencil

Parent constructive derivation, 2026-10-08. **Accepted at the scoped paper/AI-review level** in
[W032-affine-lift-review.md](W032-affine-lift-review.md); no experiment or
Lean proof. Research has stopped for user-requested handover and is not resumed by
any prospective next-step text below.
Verified complete factoring improvement: **NONE**. The completed frozen
one-parameter assay is unchanged and will not be rerun.

## What the negative result changes

The two completed families had no useful gcd even after all their carry
values were tested. Fast enumeration alone did not supply a factor.
Their lift changed only the starting point; every stencil kept step one.
The following computation changes the step as well while preserving the
polynomial annihilation identity. It does not merely resample the old
parameter or assume independent output values.

Retain the accepted denominator guard, R>=2, m=2R+1, L=2R-2,
H=N^(L-1), a_i=1+i, and the acquired base data

    u_i=v_i+H*b_i in [0,N^L),
    c0=Delta^m u/N^L in Z,
    lambda_i=(-1)^(m-i)*binom(m,i).

For independent integer parameters 0<=s,t<N use actual unwrapped inputs

    a_i(s,t)=a_i+12H(s+i*t)
             =(1+12H*s)+i*(1+12H*t).                (1)

They form an arithmetic progression and remain the same units modulo N.
Thus the degree-at-most-2R scalar polynomial still has zero mth
difference modulo N^(2R+1). Input width is O(R logN+logR); no N^2
materialized stencils are needed by the consumer below.

## Exact new carry law

The lower normalized polynomial F has F'(a)=a/12 modulo N. Its Taylor
remainder at a shift divisible by H is zero modulo N^L, since
2L-2>=L. The same argument as the accepted common-lift identity gives

    u_i(s,t)=v_i+H*[b_i+a_i*s+i*a_i*t]_N.

The extra unwrapped increment a_i*s+i*a_i*t has degree two in i.
Its mth difference vanishes, since m>=5. Consequently

    c(s,t)=c0-sum_i lambda_i
                  floor((b_i+a_i*s+i*a_i*t)/N).      (2)

This is an integer, |c(s,t)|<4^R, and the original filtered top-digit
value is -c(s,t) modulo N. The t=0 edge is exactly the old sweep.
The rank-two lift changes a real computational restriction: two separate
affine coefficients of the stencil now vary, without sacrificing the
annihilation or recomputing all scalar powers. It does not establish
larger distinct support or a better success rate on any input.

## A polynomial-size superset of the N^2 outputs

Define C(s,t) by the right side of (2) for real coordinates in [0,N)^2.
All discontinuities lie on the lines

    a_i*s+i*a_i*t=kN-b_i,
    i=0,...,m,  k=1,...,a_i*(i+1).                  (3)

There are J=sum_i(i+1)^2=O(R^3) such records. The bounds include every
positive threshold in the square; excess boundary-only lines are harmless.
The k=0 boundary introduces no extra floor vector.

Every integer point has the same floors as an open chamber. Increase s
and t by delta=1/[2*(m+1)^2]. The ith numerator increases by
(i+1)^2*delta in (0,1/2], so it crosses no next integer threshold and
selects the correct side of each equality. Both coordinates stay inside
the square. This also handles the i=0 vertical lines and corner points.

Here is a literal sampler, without a lattice-feasibility oracle. Take s
as the vertical-slab coordinate. Collect all s coordinates of nonparallel
pair intersections inside the closed square, crossings with t=0,N,
the s coordinates of vertical lines, and endpoints 0,N. Ignore coincident
boundary overlaps and never divide by a zero coefficient. Sort/deduplicate
these exact rationals. At each consecutive midpoint s*, compute heights
of all nonvertical lines, retain those strictly between 0,N, add endpoints,
sort/deduplicate, and sample each height midpoint t*. A vertical line is
a slab cut, never a height. Test gcd(C(s*,t*),N) at every sample.

Line order and active heights cannot change inside a slab, so every
open chamber is sampled. There are O(J^2) cuts and O(J) height gaps per
slab: at most O(J^3)=O(R^9) samples. Direct evaluation of O(R) floors
at each gives the conservative bit envelope

    soft O(R^10*(logN+R)),                           (4)

including acquisition, line construction, sorting, exact arithmetic,
all gcds and validation. This is an upper bound for a concrete theoretical
algorithm, not an implemented performance result. Coefficients are at
most O(R^2); determinants and rational midpoint denominators are bounded
by fixed powers of R, so all geometric arithmetic has O(logN+logR)
bits. Carry sums have O(R) bits. Streaming slabs avoids storing every
sample. The arrangement itself has only O(J^2)=O(R^6) open chambers;
the simple sampler deliberately pays for duplicated chamber visits.

Continuous extra samples need not represent integer lifts. Their gcds
are still valid, but do not assign them actual (s,t) witnesses or an exact
uniform-lift probability. Using the fractional-part expression gives
|C|<4^R*(1+1/N) on the continuous square; the stricter |c|<4^R applies
to actual integer lifts. A complete failed superset traversal implies
failure of this two-parameter family; a partial traversal does not.

## Decisive question and costs that can erase the gain

For R=Theta(logN), enumerating this superset takes polynomial time while
the underlying lift family has N^2 inputs. That compression can again be
entirely unproductive. The new decisive question is whether the quadratic
phase term i*(i+1)*t changes the gcd support in a provable way; it must
not be replaced by an independence heuristic. If it only adds polynomially
many effectively ordinary gcd arguments, a large-factor yield barrier
can remain. The conservative R^10 overhead also prevents inferring a
practical gain from the number of underlying inputs avoided.

First audit the actual Taylor/annihilation identities and rational cover.
Do not launch a new test merely because the previous two families failed.
A later assay would need its own frozen N-only schedule and total budget;
no cases, depths or seeds for this construction have been selected here.
