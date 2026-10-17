# Family 158: completion screen and exact obstruction

Myeongjin Kang; no affiliation. 2026-10-16.
Original prose CC BY 4.0; original code MIT. External sources remain private.

Status: PRE-FREEZE SCREEN COMPLETE; NO NOMINATION; counted=false.
No full research target was frozen. Neither a new full-plane theorem nor a
counterexample to full-plane Borel completion is claimed. Campaign count stays
with the parent. This is a mathematical exclusion record, not an independent
proof or contribution verdict.

## 1. Source contract and the rejected positive route

At pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, family 158,
`The-Euclidean-plane-is-not-five-colorable-September-23-2026`,
`introduction.tex` Theorem `thm:transfer` says, for every positive integer k,
that existence of an arbitrary proper k-coloring of the Euclidean plane is
equivalent to existence of a weak measurable k-coloring. A weak coloring is a
measurable partition A_1,...,A_k with

    integral_{B_R} integral_{S^1} sum_i 1_{A_i}(x)1_{A_i}(x+u) d sigma(u) dx = 0

for every R>0. The source `transfer.tex`, Lemma
`lem:palettes-density-proper`, proves that each full-density-point set C_i is
unit-distance independent, the C_i are disjoint, and C=union_i C_i is conull.
Its following compactness proof colors every finite configuration by a common
translation into C and obtains an arbitrary proper coloring of the plane.
Upstream truth is stipulated, not audited here.

An initially plausible extension was to retain the colors on all C_i and
obtain a proper Lebesgue-measurable coloring agreeing with the input almost
everywhere. This is already proved in the closest primary literature:

* James Davies, *Measurable obstructions for unmeasurable colourings*,
  arXiv:2610.12301v1, Lemma B.1, proves the finite-small-translation and fixed-
  color compactness completion for conull measurable D-avoiding partitions.
* Mikhail Koshelev, Andrey Kupavskii, Vsevolod Voronov, *Ordinary and measurable
  colorings of Euclidean three-space*, arXiv:2610.18907v1, Lemma 7.1, gives the
  full weak-to-proper Lebesgue completion for every d>=1 and every k>=1,
  retaining every density-one color. It credits Davies for the completion.

For clarity, the decisive operation is the following. Given finite V and
prescribed x in V intersect C_i, density one makes the bad small translations
for each prescribed point have arbitrarily small relative measure. A finite
union bound retains positive measure; finitely many other vertices exclude
only null sets of translations. A remaining translation colors V properly
while retaining all prescribed colors. Compactness with those fixed-color
constraints extends to all points. Every final class is C_i plus a subset of
the null complement of C, so is Lebesgue measurable. This exact operation is
not available as a fresh campaign contribution.

The second primary explicitly does not assert Borel final classes. Its proof
also shows C_i is Borel, using continuous ball averages and a countable limit.
An arbitrary subset of the Borel null complement need not be Borel.

## 2. The still-unpaid Borel operation

Two questions must not be conflated:

(E) Does existence of a weak measurable proper k-coloring imply existence of
    some Borel proper k-coloring of the full plane?
(R) Can every given weak measurable k-coloring be changed on a plane-null set
    to become a Borel proper k-coloring?

The rejected Lebesgue route proves the Lebesgue analogue of (R). Neither
primary proof read establishes (E) or (R) with Borel in place of Lebesgue.
The prescribed density-point extension would be stronger than (R).
The known Borel seven-coloring handles existence (E) for k>=7, but does not
by itself prove (R), which must retain an arbitrary input almost everywhere.
Under the stipulated source lower bound, the only nonvacuous undecided
existence case below seven is k=6. No attempt to solve that famous endpoint
by merely deleting the word measurable was frozen here.

A positive argument needs a Borel selection of compatible color assignments
on the exceptional null set, using the full ambient unit-distance geometry.
Finite satisfiability and ordinary product compactness alone cannot do this.
Nor is projection of an arbitrary Borel subset of a product automatically
Borel merely because the second ambient factor is a compact circle.

## 3. A concrete null-circle obstruction to generic completion

The following standard irrational-rotation obstruction is included with a
full proof to identify the failed operation. It is not claimed as new.

Choose irrational alpha with 0<alpha<1/2, and set

    r = 1 / (2 sin(pi alpha)),
    S = {x in R^2 : |x|=r}.

Identify S with R/Z by t -> r(cos(2 pi t),sin(2 pi t)). Two points on S
have Euclidean distance one exactly when their parameters differ by +alpha
or -alpha modulo one: the chord formula is

    |x(t)-x(s)| = 2r |sin(pi(t-s))|.

The induced unit-distance graph on S therefore has components equal to
irrational-rotation orbits, with edges between consecutive iterates. Each
component is a two-sided infinite path, since alpha is irrational. Choice
of one orbit representative and parity of the iterate gives an abstract
proper 2-coloring.

There is no Borel proper 2-coloring. If A is one Borel color class and
T(t)=t+alpha, properness with exactly two colors implies T(A)=A^c and
T^2(A)=A. Normalized circle measure is T-invariant, so mu(A)=1/2. But T^2
is ergodic: if f=1_A is invariant, its nth Fourier coefficient obeys

    fhat(n) = exp(4 pi i n alpha) fhat(n).

For every nonzero integer n the multiplier is not one. All nonconstant
coefficients vanish, and completeness of the Fourier basis in L^2 forces
f to be constant almost everywhere. An indicator constant almost everywhere
has integral zero or one, contradicting mu(A)=1/2. The same proof excludes
circle-Lebesgue-measurable proper 2-colorings.

Now form a graph H on all of R^2 whose only edges are the unit edges with
both endpoints on S. This is a closed, locally finite, unit-distance
SUBGRAPH, not the full plane unit-distance graph. Let C=R^2 minus S and
prescribe color 1 on C. C is open and conull, and every point of C has
density one in C. Every finite family of edge and prescribed-color
constraints is satisfiable: the finite subgraph on S is a forest, and C
consists of isolated vertices of H. Indeed the full graph has an abstract
proper 2-coloring retaining all prescribed colors. That coloring is plane-
Lebesgue-measurable because S is plane-null and Lebesgue measure is complete.
It cannot be Borel, since restriction to the Borel circle would give the
forbidden Borel 2-coloring above.

Consequently even a closed unit-distance subgraph, a Borel conull
prescribed core, density one at every core point, and all compatible finite
extensions do not imply Borel completion. The compactness argument needs
more than these properties. This does NOT refute (E) or (R) for the full
plane: H deletes all edges incident to points outside S, and the full plane
has no 2-coloring. No scope substitution is made.

## 4. Why an elementary forcing construction also fails

One possible attempt at a full-plane counterexample would force all points
of S to use two colors by robustly forbidding every other color near S.
If that forcing leaves an entire open annulus around S with only two
available colors, it is impossible even at the finite graph level.

For every r>1/2 and every epsilon>0, the annulus

    {x : ||x|-r| < epsilon}

contains a finite odd unit-distance cycle. Let alpha in (0,1/2) satisfy
r=1/(2 sin(pi alpha)). Choose arbitrarily large odd primes q and integers
p nearest alpha q. For sufficiently large q, 1<=p<q/2, and p/q tends to
alpha. Since q is prime, gcd(p,q)=1. Put

    r_q = 1/(2 sin(pi p/q)),
    x_j = r_q (cos(2 pi j p/q), sin(2 pi j p/q)), 0<=j<q.

The q points are distinct, consecutive points including x_{q-1},x_0
have distance one, q is odd, and r_q tends to r. For large q all vertices
lie in the given annulus. Thus it cannot be properly 2-colored.

This rules out the robust open-annulus forcing variant. It does not rule
out all irregular/fractal constraints, and no such full-plane construction
was found. The precise unpaid operation is either an ambient Borel extension
mechanism, or an actual full-plane weak coloring whose exceptional constraints
force non-Borel behavior without also creating a finite obstruction in its
conull portion. Neither has been supplied.

## 5. Disposition

The Lebesgue completion branch is an exact primary duplicate. The Borel
branch has a real unpaid selection step, but no credible complete ambient
mechanism was found before freeze. Keep this as a pre-freeze screen and move
to a distinct source family. The null-circle example and annulus observation
are supporting obstruction analyses, not a replacement campaign result.
