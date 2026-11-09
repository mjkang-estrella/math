# Sustained routes, with zero discovery credit

## 369819: equality for bipartite independent distance domination

The primary source is 2508.12804v1, Definition in Section 1, Theorem 2.1, Proposition 3.1 and Conjecture 5.1. An independent set S must put every vertex within distance d of S. The family B_d consists of P_d-coronas: attach a fresh path with d vertices to each vertex of an arbitrary bipartite core. The extremal assertion quantifies over all connected bipartite graphs and all d >= 2. Small n < d+1 cannot give equality, so they offer no substantive refutation.

First route: look for graphs where the independent restriction forces equality even though ordinary distance domination is smaller. Exact independent-set enumeration on the connected bipartite graph atlas through order 7 found only the stated equality types for d=2,3. The six-vertex equalities are P6 and C6. Seeded random connected bipartite graphs on 9 and 12 vertices found no equality in 600 generated graphs per order. This is bounded evidence only, not exhaustive coverage at those orders.

Second route: start at an equality graph and add edges that preserve bipartiteness. For a core vertex u, its terminal leaf in the attached path is distance d from u, and distance greater than d from every vertex outside its own block. These disjoint blocks force at least one dominator each; the terminal leaves themselves form an independent dominating set. This proves the known sufficiency direction, already Proposition 3.1, and is not new. Additional edges can destroy the disjoint private-neighborhood obstruction. The mutation script tests 278, 425 and 442 edge additions (one, two or three edges, bounded to 200 choices per size) to path-core coronas on 9, 12 and 15 vertices. Its only three surviving equalities still pass the disjoint pendant-path corona test. No noncorona witness emerged.

Third route: exploit the source's partition into d+1 independent d-dominating sets. Equality forces every part in every such partition to have size n/(d+1). This is necessary, but the construction in Theorem 2.1 depends on breadth-first distance levels, so equal sizes in one partition do not force pendant paths. Remaining lemma: a connected bipartite graph outside C_(2d+2), B_d and order d+1 has an independent distance-d dominating set of size strictly less than n/(d+1). No proof of the required strict structural improvement was obtained. Ordinary domination's existing equality characterization cannot be transferred without this lemma.

## 370010: mean subtree order after contraction

The source 2508.20593 distinguishes subtrees (acyclic connected subgraphs, not necessarily induced) from connected vertex sets. Its Conjecture 1.8 is the exact target. Its tree case is already known; it does not settle all connected graphs. Source Theorems 1.2 and 1.4 settle 370009 and are not new opportunities.

First route: exact enumeration with the matrix-tree determinant counts each vertex set by its number of spanning trees. The script checks all connected atlas graphs of order at most 6 and every edge contraction, suppressing loops and duplicate edges. The minimum difference was 1/3, attained at the path K2. No counterexample was found. This is diagnostic and not a Lean certificate.

Second route: reduce a bridge contraction to an explicit rooted generating-function inequality. Let A(z), B(z) count all nonempty subtrees on the two sides of a bridge ab; let a(z), b(z) count those containing their attachment vertices. Write juxtaposition for polynomial multiplication. Direct classification by whether a subtree uses the bridge gives

    F_G = A + B + ab,
    F_(G/e) = A + B - a - b + ab/z.

Here a and b are divisible by z, so the latter is a polynomial. At z=1 set S=A+B+ab and T=A'+B'+a'b+ab'. Then S*=S-a-b and T*=T-a'-b'-ab. Consequently

    mu(G)-mu(G/e) = [S(a'+b'+ab)-T(a+b)]/[S(S-a-b)].

The conjectured lower bound requires the numerator to be at least S(S-a-b)/3. All symbols on this line are evaluated at 1. This identity is proved by the subtree decomposition above; the inequality is NOT proved. Abstract nonnegative coefficient assumptions on A,a,B,b do not supply the rooted/unrooted correlations of actual graph subtree polynomials. The leaf case B=b=z reduces to

    A(1+a'+a) - (1+a)A' >= A(A+1+a)/3.

This isolates a precise remaining rooted inequality. Applying the known tree theorem to a spanning tree does not work: mean subtree order is not monotone under adding edges (the source explicitly discusses counterexamples). Applying the source's ordinary path-minimum bound to both G and G/e also does not control their difference. The full literal endpoint remains open in this lane.

## 369837: complex interpolation grids

The exact primary target is 2508.13554 Conjecture 6.3, not the pointwise Conjectures 6.1 or 6.2. The interval I is [-1,1]; the norm on the closed unit disc bounds the nth derivative of an entire function. Definition 6.1 requires conjugate partners for nonreal nodes and even multiplicities of real nodes. Hermite interpolation handles repeated nodes.

First route: normalize g(z)=((t-n)!/t!)z^t and divide by the nodal polynomial f. Its remainder is the interpolation polynomial, so differentiation of g-remainder gives the error. The initial diagnostic included odd grids with a lone real node; those trials violate Definition 6.1 and cannot support a source claim. A separate admissible run uses only n=2,4,6,8 and paired nonreal nodes: 600 seeded grids, every k<n, and n+1<=t<=n+12. No numerical violation appeared on a 1001-point mesh. The run excludes t=n (which always gives equality), and the mesh is not a certified supremum. The old broader log is retained with this correction.

Second route: test whether the live registry's explicit refutation of Conjecture 6.2 settles the uniform question. Its witness is -9/10 +/- (2/5)i and its shifted Schur ratio is 73/60. Reading its actual Lean statement shows it refutes a pointwise ratio, not Conjecture 6.3. In fact for n=2,k=1,t=3, f=x^2-2ax+(a^2+b^2), and the cubic's derivative error is x^2/2-(3a^2-b^2)/6. The uniform nodal bound is max(|-1-a|,|1-a|)=1+|a|, so a large pointwise ratio near a small f' does not itself violate the uniform bound. Do not reuse the registry witness as a claimed solution.

Third route: go beyond monomials by optimizing polynomial combinations whose nth derivative has disc norm <=1. The triangle inequality bounds a coefficient-l1-normalized combination by the worst monomial bound; it therefore cannot find anything new if every monomial satisfies the bound. A successful extension needs phase cancellation on the disc boundary, with an exact norm certificate and a certified real-interval maximum. Neither the requisite general inequality nor an exact violating polynomial was obtained. No neighboring Schur-ratio statement is substituted for the literal endpoint, and no Lean packet is claimed.
