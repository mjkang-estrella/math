**EXCLUDED: exact public prior resolution found. See EXCLUSION.md. Credit 0.**

# Golden-ratio constant-range rigidity — proposed proof

**UNREVIEWED mathematical proposal. Credit 0. No Lean endpoint, manuscript,
acceptance, or global novelty claim.**

Source: Bényi–Ćurgus, *Floor, ceiling and the space between*,
arXiv:2507.14244v3, Conjecture 4.7; MathDB 369386.
Domain n is the strictly positive integers. Set

    F_a(n) = floor(a² n) − floor(a floor(a n)).

Proposed resolution: for positive irrational a, F_a(n)=1 for every n≥1
if and only if a=(1+sqrt(5))/2. The forward golden-ratio identity is known
(source Proposition 4.1), uncredited. The proposed new part is necessity.

## A domination lemma

Let a be irrational and C>0. Suppose for all n≥1,

    {n b} ≤ C {n a}.

Then b = r a + s for integers r≥0 and s, with r≤C.

Proof. Work in T²=(R/Z)² and let H be the closure of the positive orbit
of (a,b). This is a compact subgroup: closure of the positive powers in a
compact group agrees with the closure of all integer powers. Its projection
to the first circle is surjective by irrational rotation density.

Every point (u,v) in H whose canonical representatives u,v lie in (0,1)
satisfies v≤C u, by continuity of representatives away from the cut and
approximation by the positive orbit. The first projection has trivial kernel.
Indeed, suppose (0,v0)∈H with 0<v0<1. Choose orbit points with
0<{n_j a}→0, using irrational rotation density. The domination hypothesis
gives {n_j b}→0, so adding these points to (0,v0) gives H-points with
0<u_j→0 and v_j→v0 inside (0,1). The extended inequality v_j≤C u_j
contradicts v0>0.

Thus the first projection H→T is a continuous bijective group homomorphism
from compact to Hausdorff, hence an isomorphism of topological groups.
Consequently H is the graph of a continuous circle endomorphism. Every such
endomorphism is multiplication by an integer r (lift along R→T with value 0
at the origin; additivity follows because the lift's additive defect is a
continuous integer-valued function on connected R²; continuous additive real
maps are linear; periodicity makes the slope integral).

It follows that b−r a∈Z and {r u}≤C u for every u∈(0,1) for which
{r u}∈(0,1). A negative r contradicts the inequality as u→0+.
For r>0, take 0<u<1/r to obtain r≤C. For r=0 this bound is immediate.
This proves the lemma, using only standard compact-group and circle facts.

## Necessity in the source conjecture

Put u_n={a n} and v_n={a² n}. The condition F_a(n)=1 is equivalent to

    a u_n − 1 ≤ v_n < a u_n,

because F_a(n)=−floor(v_n−a u_n). In particular the domination lemma with
b=a², C=a yields a²=r a+s with integers 0≤r≤a and s. Since a is
irrational, r<a.

If r=0, then a²=s is a positive integer and v_n=0 for every n. The lower
inequality, together with density of u_n in (0,1), gives a≤1. Then 0<a²≤1
is an integer, so a=1, contrary to irrationality. Thus r≥1.

If r≥2, use density to let u_n approach 1/r from above. Then
v_n={r u_n}→0, and the lower inequality gives a/r≤1, contradicting r<a.
Hence r=1. Letting u_n→1− gives a−1≤1, so 1<a≤2; irrationality excludes
a=2. Thus s=a²−a is an integer strictly between 0 and 2, hence s=1.
The positive solution is a=(1+sqrt(5))/2.

Conversely, if a²=a+1, then for every n≥1, u_n∈(0,1) and v_n=u_n.
Since 1<a<2, −1<(1−a)u_n<0, giving F_a(n)=1 exactly.

## Outstanding gates and formal obligations

The argument is a complete proposed mathematical route, not yet independently
reviewed. Check especially the compact-semigroup closure, the one-sided cut
argument in the domination lemma, and closest prior theorems on nested Beatty
sequences/dilated-floor commutators. No novelty is inferred from MathDB's label.
The compact group/circle endomorphism steps require actual Lean proofs or pinned
Mathlib dependencies. Do not insert them as assumptions in an accepted endpoint.
No finite scan, helper, sufficiency case, or domination lemma gets separate credit.
