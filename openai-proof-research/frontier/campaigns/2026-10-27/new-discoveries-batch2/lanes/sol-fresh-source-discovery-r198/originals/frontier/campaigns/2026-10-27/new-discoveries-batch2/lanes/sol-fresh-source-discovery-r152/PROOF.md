# Complete ordinary proof, routine source adaptation; not nominated

Target: Adel P. Kazemi, *Total Dominator Coloring of the Hypercube
Q_(2^n)*, Contributions to Mathematics 13 (2026), 1–10,
DOI 10.47443/cm.2025.102, Conjecture 6.1, actual published p.10.
For every integer n>=2, it asserts
chi_td(Q_(2^n+1)) = 2^(2^n-n+1)+2.
Here the dimension is 2^n+1, not 2n+1.

This is a complete ordinary proof using the known total-domination value
in the source Theorem 1.3 (also Azarija–Henning–Klavzar 2017, Theorems
1 and 3). It is retained as an uncredited routine extension of source
Fact 5.1. No substantive novelty, priority, Lean or acceptance claim.

Put d=2^n+1>=5, V=2^d and g=V/(d-1)=gamma_t(Q_d).
The upper bound chi_td<=g+2 is immediate: give every vertex of a
minimum total dominating set its own color and color the remaining
vertices by the two parity colors. Every vertex sees a singleton class.

For the lower bound take an arbitrary total dominator coloring, whose
nonempty color classes form a partition. For a class C put
CN(C)=intersection over x in C of N(x). Call C active when CN(C)
is nonempty. Let a be the number of active classes and t the number
of inactive classes. The total dominator property says that the sets
CN(C), for active C, cover all V vertices.

First, a>=g: choose one representative from each active class. Each
vertex is adjacent to the representative of a class it totally dominates,
so the representatives form a total dominating set of size a.

Second, every active class satisfies |C|+|CN(C)|<=d+1.
For |C|=1 the sum is exactly d+1. For |C|=2, the two distinct vertices
have at most two common neighbors, giving a sum at most4<=d+1.
For |C|>=3, choose v in CN(C); then C is contained in N(v) so
|C|<=d. Three distinct vertices have at most one common neighbor:
two distinct centers with common neighbors in a cube are at distance2
and have exactly two common neighbors. Thus |CN(C)|<=1, proving
the bound. These are precisely the elementary common-neighborhood
facts in source Fact5.1(2)–(6).

Third, every independent set has size at most V/2. One coordinate's
perfect matching proves this. If an independent set S has size V/2,
all dV/2 edges meet S by degree counting; its complement is therefore
independent. Connectedness then forces S to be one of the two parity
parts. In a total dominator coloring an inactive class cannot be such
an S: all other classes are in the complementary parity part, so their
common neighborhoods lie in S, leaving every vertex outside S uncovered.
Consequently each inactive class has size at most V/2-1.

Suppose for contradiction that a+t<=g+1. Since a>=g, t<=1.
If t=1, the active classes contain at least V/2+1 vertices. Summing
the second bound and using the coverage of all vertices gives

  (d+1)a >= (V/2+1)+V = 3V/2+1.

But a<=g, while

  3V/2+1-(d+1)g = V(d-5)/(2(d-1))+1 > 0,

a contradiction for every d>=5, including d=5.

If t=0, all vertices lie in active classes, so instead

  (d+1)a >= 2V.

Yet a<=g+1 and

  2V-(d+1)(g+1) = V(d-3)/(d-1)-(d+1)
                         >= V/2-(d+1) > 0.

The last inequality is 2^(d-1)>d+1 for d>=5; it holds at d=5 and
propagates by doubling. This is again a contradiction. Hence every
total dominator coloring uses at least g+2 colors, proving the exact
displayed source conjecture for all n>=2. QED.

## Strongest objection and disposition

The only ingredients beyond the source's explicit Fact5.1 and known
gamma_t are representative selection, summation, and the elementary
maximum-independent-set equality case. This is a full bridge from the
source counting machinery to Conjecture6.1. Under this task's explicit
exclusion of routine classical/source adaptations it earns zero credit.
Question6.1 about well-total domination is separate and not nominated.
There is no mathematical residual gap in the displayed proof; the gap
to a qualifying discovery is substantive novelty, not a finite check.
