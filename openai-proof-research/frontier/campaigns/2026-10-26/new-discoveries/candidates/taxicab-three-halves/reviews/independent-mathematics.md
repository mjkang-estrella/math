# Independent mathematical review: universal normed-triangle 3/2 bound

**Mathematical verdict: the proposed proof route is valid**, with the small V2 expansion correction below and the usual explicit nonnegativity of distance variables. This is a pen-and-paper mathematical review, not a Lean audit and not a novelty determination. **Discovery count remains zero pending formal verification and prior-art review.**

Reviewed source: `parent-inequalities/taxicab-proof-candidate.md`, including its simplex clarification, on 2026-10-26. The reviewer did not author or edit that candidate. The exact primary arXiv:1901.08758v1 definitions and Conjecture 1 were read, including equations (2), (5), and (6).

## Source bridge and geometry

The primary source uses taxicab vertex distance `|dx|+|dy|` and defines side distances by the supporting-line formula

`r(P, ax+by+c=0)=|a Px+b Py+c|/max(|a|,|b|)`.

This is explicit in its equations (5)–(6), despite the introduction's informal reference to segments. The proposed geometric inequalities are valid for these actual line distances. They would also hold for infimum distance to the opposite segment, since the particular comparison points used below lie on that segment.

Translate P to zero. For a genuine nondegenerate triangle with P in its affine interior there are positive barycentric coordinates λa,λb,λc summing to one, with weighted vector sum zero. In particular each λ is less than one, and the three vertex norms A,B,C are positive.

The opposite side contains b,c and

`q_a=(λb b+λc c)/(1−λa)=−λa a/(1−λa)`.

It follows that `r_a≤B`, `r_a≤C`, and `r_a≤λa A/(1−λa)`. The last inequality is equivalent to `r_a/(A+r_a)≤λa`. The three cyclic inequalities therefore give `Σ r_a/(A+r_a)≤1`. No rotation, anisotropic coordinate change, or purported taxicab isometry is used. Sorting vertex norms is just relabelling the vertices and their corresponding opposite-side distances simultaneously.

For a direct coordinate formalization, a source line function ℓ vanishing on b,c obeys

`|ℓ(P)|=|a(Px−Qx)+b(Py−Qy)| ≤ max(|a|,|b|) (|Px−Qx|+|Py−Qy|)`

for each Q on that line. Hence the endpoint inequalities follow immediately. The barycentric line identity `(1−λa)ℓ(P)=λa ℓ(A)` gives the weighted distance bound without dividing by `1−λa`. This avoids an implicit norm-convention change: the default Lean norm on `ℝ×ℝ` is the maximum norm, not the taxicab norm.

## Scalar reduction: all boundary cases covered

Use nonnegative u,v,w, with positive A≤B≤C and capacities `(u,v,w)≤(B,A,A)`. Suppose `u+v+w>t0=2(A+B+C)/3`. Then scale all three distances by the positive factor `t0/(u+v+w)<1`. The new point stays in the box and has sum t0.

The threshold satisfies `t0≥A+B≥2A`. Write

`D=B+2A−t0`.

Feasibility of the threshold point gives D≥0; the displayed threshold bound gives D≤A≤B. Its deficits `(B−u,A−v,A−w)` are nonnegative and sum D. If D>0, dividing them by D yields convex-combination weights for precisely

- `V1=(t0−2A,A,A)`,
- `V2=(B,t0−A−B,A)`,
- `V3=(B,A,t0−A−B)`.

Every coordinate of these vertices is nonnegative because D≤A≤B. Thus the threshold slice really is this simplex; no unstated polytope-extreme-point theorem or assertion about “no zero component” is needed. If D=0, the slice is the single point `(B,A,A)`, at which F is at least one. If the threshold box is empty, a point with larger sum was impossible already.

For `F=u/(A+u)+v/(B+v)+w/(C+w)`, each summand has second derivative `−2a/(a+x)^3<0` on nonnegative x. Thus F is concave there. It suffices to show F≥1 at the three vertices; Jensen's inequality then proves F≥1 throughout the slice.

## Independent vertex algebra

**V1.** Put `u=2(B+C−2A)/3`. Clearing strictly positive denominators shows F≥1 is equivalent to

`u(2A+B+C)≥BC−A²`.

The left side minus the right side is exactly

`(2B²+BC+2C²−5A²)/3≥0`,

since B,C≥A>0. This calculation is correct, including the case A=B=C, where u=0.

**V2.** Put `v=(2C−A−B)/3≥0`. It is enough to compare

`v/(B+v) ≥ (C−B)/(B+C) ≥ A(C−B)/((A+B)(A+C))`.

The first comparison, after cross-multiplication, has difference

`v(B+C)−(C−B)(B+v)=B(B+C−2A)/3≥0`.

**Correction to the candidate's prose:** this cross-product difference has the factor **1/3**. Omitting it does not affect the inequality, but the exact identity should be corrected before publication/formal transcription. The second comparison follows from C−B≥0 and `(A+B)(A+C)−A(B+C)=A²+BC>0`. These comparisons supply precisely the deficit left by the first and third summands at V2.

**V3.** Its first two summands equal `B/(A+B)+A/(A+B)=1`, and its last summand is nonnegative. Thus F≥1.

## Strict scaling contradiction

For each a>0, `x/(a+x)` strictly increases on nonnegative x. At least one distance is positive because the original sum exceeds t0>0. Scaling by a factor strictly between zero and one therefore strictly decreases F. The threshold proof gives `1≤F(scaled)<F(original)≤1`, a contradiction. Hence `u+v+w≤2(A+B+C)/3`.

The scalar claim should explicitly state u,v,w≥0 for clarity, as geometry provides it. Even if omitted, a violating sum together with the capacities and `t0≥A+B≥2A` forces all three coordinates positive, but that extra derivation would otherwise need to be included.

## Final mathematical conclusion and limits

Combining the verified scalar argument with the geometric bounds yields the source inequality for arbitrary triangle orientations in the taxicab plane. The same geometric reasoning works in any real normed space for an ordinary affine triangle, provided side distances mean actual infimum norm distances. No mathematical flaw was found in the candidate argument after the stated V2 correction.

This does **not** establish that the result is new. In particular the source itself cites Ghandehari–Martini's 2018 work on Erdős–Mordell inequalities in normed planes and spaces. A theorem in that literature may subsume the whole bound even though the 2019 taxicab paper records its arbitrary-triangle formulation as open. Novelty review is explicitly outside this mathematical approval, and no discovery is counted here.
