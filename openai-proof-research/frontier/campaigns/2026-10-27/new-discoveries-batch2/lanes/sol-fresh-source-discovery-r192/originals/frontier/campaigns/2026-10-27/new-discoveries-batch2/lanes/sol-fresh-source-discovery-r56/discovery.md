# One fresh finite question; unresolved, credit 0

## Literal source and eligibility limits

TheoremDB P2806, “Log-concavity of bootstrap-percolation spanning-set counts,” live source downloaded 2026-10-29T15:37:26 UTC, https://theoremdb.org/statements/P2806/ . Its own statement fingerprint is c6d9e2373db08e9d7dafe73158015888ee04f0d96c9254b4b1952569ca4e89a2. Actual HTML bytes/hash are in http.jsonl, not inferred from that advertised statement hash.

Exact target: **for every pair of integers m,n >=2**, put nearest-neighbor edges on [m] x [n]. Begin with A and repeatedly infect every vertex having at least two infected neighbors. Let b_m,n(k) count initial k-subsets that infect the whole grid. Decide whether b(k)^2 >= b(k-1)b(k+1) for **every 1<=k<mn**. A single exactly certified violating triple would refute this yes/no question. This is not an open characterization question. No such triple was found or claimed.

Only ONE primary candidate question was screened; search-result leads were not separately developed as targets. This is a new family relative to the read campaign notes, not a credited-family variant. IMPORTANT source qualification limitation: the coefficient question is the registry's explicitly original CC0 prospecting question, not a conjecture stated by Balogh et al. The page says its packet has NOT passed editorial review. A named expert or journal source for this exact question was NOT established. Root must assess that limitation independently; no eligibility PASS is requested.

The actual referenced process paper is Balogh–Bollobás–Duminil-Copin–Morris, arXiv:1010.3326v2, dated 24 February 2011, later Trans. AMS364 (2012),2667–2701. Definitions pp1–2 and Theorem1/Remark1 p3 were read, not just the abstract. Theorem1: every fixed pair d>=r>=2 has pc([n]^d,r)=((lambda(d,r)+o(1))/log_(r-1)(n))^(d-r+1) as n→infinity. This probability asymptotic neither states nor supplies all finite adjacent coefficient inequalities. No assertion about the entire paper's unrelated technical lemmas is needed. The question page itself dates its status snapshot to August1,2026; that date is NOT our live retrieval date.

## Current registries, scope and chronology

Five current GitHub heads were fetched, all HTTP200:
- Omega dev 3b4135a35caa0ae817cf5eca51d605b098027fd2, 2026-10-29T15:32:31Z.
- Omega main d7af67136d4478875778ac6e75eb5fbb8b3693a5, 2026-07-11.
- OpenAI math 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a, 2026-10-26.
- MColbrook/AIM 8729eab98bafe409b66c5e39253bf56569a62327, 2026-10-22.
- Count-ex-machina dbf673741a54c7dc9d88a6aec0e8148a538f4a3a, 2026-09-09.

Omega compare from supplied r54 baseline0169726… to current3b4135… has3commits and1file (docs/develop/theory/CDSO_UNIVERSAL_VERTEX_ALL_CYCLOMATIC.md); it does NOT hit300file cap. Thus r54's freshly complete D5/Problems scope bytes12554/1551 can be reused with this verified documentation-only delta. The baseline itself was NOT cleared by its whole-dev capped comparison. No whole-dev coverage is claimed here either. Other four heads unchanged from r54. Frozen cached complete relevant scoped trees copied into this lane, with explicit reuse lineage in registry-screen.json. This does not amount to exhaustive semantic proof discovery.

Closest lexical registry body actually read: D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.lean, and its Problems/bresar-2024-direct-product-cycle-path-percolation.md. Its `claim`/`result` concern the MINIMUM percolating cardinality n on DIRECT products C_n x P_m for n>=3,m>=1. `dirProd.Adj` uses adjacency in BOTH coordinates. The proof uses the potential4|A|-D(A). Our Cartesian rectangular grid and ALL cardinality counts are different. This public complete result is not our target, is not a new candidate here, and gets no credit. Its actual pinned source/body/hash is archived. The registry body is public before this lane; no priority claim is made for any common helper.

Bounded web searches (2026-10-29) included exact bootstrap/spanning/log-concavity, bootstrap/matroid, and the P2806 slug. They returned the original record and the adjacent spanoid/weak-saturation literature, but no exact full resolution in inspected results. Searches are not exhaustive literature clearance. TheoremDB's original question is the primary statement, not its own unsupported absence assertion. No challenges/errors, repeated blocked access, account operations, browser tabs, or external mutations occurred. Search responses were read; raw HTTP artifacts, rather than search rankings, are preserved for cited primary bodies.

## Exact all-rectangle reduction: stable vacancy obstructions

Write N=mn and V for the grid. Let K be its downward-closed family of vacancy sets U whose initially infected complement V\U percolates. Define a_j=#{U in K:|U|=j}; then a_j=b(N-j), so log-concavity is equivalent for a and b.

A nonempty set F is a fort precisely when every v in F has at most one neighbor outside F, equivalently deg_F(v)>=deg_G(v)-1. Then U belongs to K iff it contains no fort. Proof: a contained fort cannot lose its first vertex, since before that deletion each of its vertices has at most one infected neighbor. Conversely if the process stops with nonempty vacant set F, its stopping condition gives exactly those inequalities. This proves the equivalence for every finite grid; no enumeration assumption.

Let H be the inclusion-minimal forts. Finiteness gives such a subfort inside every fort. Thus K is exactly the independent-set complex of the hypergraph H. Inclusion-exclusion gives the exact polynomial identity

    A(x)=sum_(J subset H) (-1)^|J| x^|union J| (1+x)^(N-|union J|).

The empty J contributes (1+x)^N. This is an exact identity for the source polynomial but gives no positive adjacent-layer certificate. The alternating signs cannot silently be discarded.

## First proof-route objections, certified on tiny actual source instances

Label the2x2 grid row-major a,b,c,d. The vacancy family consists exactly of empty set, four singletons and the two diagonals {a,d},{b,c}. Adjacent vacancy pairs are stable forts; a diagonal has both its vertices infect immediately. Hence A_2,2(x)=1+4x+2x². Its two maximal faces violate matroid basis exchange: after removing a from {a,d}, neither b nor c can be inserted. Therefore direct application of matroid independence log-concavity is not justified.

The multiaffine polynomial F=1+a+b+c+d+ad+bc also violates the necessary Rayleigh negative-correlation inequality at all variables1: F=7, F_a=F_d=2,F_ad=1, so F_a F_d-F F_ad=-3. The degree2 homogenization z0²+z0(a+b+c+d)+ad+bc has a principal Hessian block from ad+bc with two positive eigenvalues (each disjoint edge block has eigenvalues1,-1). Therefore its Hessian has at least two positive eigenvalues, violating the quadratic Lorentzian condition. These are obstructions to those stronger proof methods, not to scalar log-concavity.

For2x3, exact closure enumeration gives A(x)=1+6x+13x²+10x³. The cubic discriminant is -4, calculated exactly in check.py; a real cubic with negative discriminant has a nonreal conjugate pair. Thus the all-grid polynomial-real-rootedness route is also false. The actual coefficient inequality remains true on this instance.

## A materially different route: exact strip geometry and finite transfer

On the2xn ladder, n>=2, the four corner vertices have degree2 and every other vertex degree3. A vacancy set U belongs to K iff its induced graph is a forest and each component contains at most one corner.

Necessity: a cycle has degree at least2 at each vertex, meeting every threshold deg_G-1<=2, and is a fort. A path between two distinct corners also is a fort: endpoints have degree1 and internal vertices have degree2. Sufficiency: a fort in an induced forest would have a tree component with at least two leaves; every noncorner in a fort must have degree>=2, so both leaves must be distinct corners in one original component, a contradiction. Single-vertex forts are impossible because all grid degrees>=2. This establishes the exact strip criterion.

Processing columns, store each occupied (vacant) frontier vertex's component and whether that component already contains a corner. Reject an edge creating a cycle, or a merge creating two corners. Forgotten components are safe permanently because future edges meet only the current frontier. This proves the finite-state algorithm, not merely its finite testing. check.py implements the literal frontier union-find version.

By row symmetry the interior-column transition reduces to four states, ordered U,S1,D0,D1: U aggregates empty frontier and a single frontier vertex in a corner-free component; S1 is a single frontier vertex in a one-corner component; D0,D1 have both frontier vertices connected in a component with zero/one corners. U's two component types have identical future weights, which justifies aggregation. With x counting vacancies, the transition matrix is

    T = [[1+2x, 0, x², 0],
         [1+x,  x, 0, x²],
         [1+2x, 0, 0, 0],
         [1,   2x, 0, 0]].

After the first column v=(1,2x,0,0); last-column acceptance vector w=(1+2x,1+x,1+2x,1)^t. Consequently A_2,n(x)=v T^(n-2) w for every n>=2. The last column's two vertices are corners, so neither a full last column nor attachment to an already corner-bearing component is permitted. Those restrictions explain w.

algebra.py derives the exact bivariate generating function sum_(n>=2) A_2,n(x)z^(n-2)=P/Q:

    P = 1+4x+2x² + (4x³-x²-x)z
        -(6x⁴+3x³)z² -(4x⁶+2x⁵)z³,
    Q = (1-xz-2x³z²)(1-(1+2x)z-(x²+2x³)z²).

All signs in this displayed identity follow directly from finite matrix inversion, reproduced symbolically. This supplies an all-length recurrence, NOT its log-concavity proof. A coefficientwise TP2 shortcut for the displayed transition matrix fails: rows0,1 and columns0,2 have determinant -x²-x³. Reordering might alter individual signs, so no assertion that every equivalent transfer representation fails is made.

The forest criterion cannot be extended to arbitrary widths: the four central vertices in4x4 induce a cycle, but each has two infected neighbors outside that cycle and they all infect at the first round. Thus they form an admissible vacancy set. Replacing the strip criterion by an all-grid induced-forest condition loses genuine source sets.

## Full-scope balanced-coloring bridge, still UNPROVED

For every I subset W subset V put D=W\I and

    c_(I,W)(r)=#{X subset D: |X|=r,
                      I union X in K, I union(D\X) in K}.

For any j, partition ordered pairs of vacancy sets by their intersection I and union W. In both the equal-size pair case and the sizes(j-1,j+1) case, |I|+|W|=2j. Put q=j-|I|; then |D|=2q. Exact counting gives

    a_j² = sum_(I,W: |I|+|W|=2j) c_(I,W)(q),
    a_(j-1) a_(j+1) = sum_(I,W: |I|+|W|=2j) c_(I,W)(q-1).

Terms with impossible q are zero. Therefore a uniform inequality c(q)>=c(q-1), for every even-size D with q>=1, would prove the FULL SOURCE target, without a strip restriction. No such inequality is proved here. Failure of that stronger per-slice inequality would not alone refute the source, since the sum can still be nonnegative.

The fort description yields an exact reformulation: if I contains a fort then all counts vanish. Otherwise consider the hypergraph on D with edges F\I for minimal forts F contained in W. A permissible X is precisely a proper2-coloring with color class X: no projected edge may be monochromatic. Empty edges make the count zero; singleton edges also prohibit proper coloring. This follows by applying the fort criterion separately to I union X and I union(D\X).

Symmetry c(r)=c(|D|-r) follows by swapping colors, but symmetry does not imply the needed central inequality. For arbitrary hypergraphs even graph stars disprove it: the proper coloring count of K1,3 is x+x³, with zero central coefficient and positive neighbors. Thus a general hypergraph coloring or downward-closure argument does not resolve the bridge. The extra geometric restrictions imposed by rectangular-grid forts must do real work. The unproved step is to construct an injection from permissible (q-1,q+1) colorings to (q,q) colorings, or otherwise compare their exact counts uniformly, allowing projected hyperedges of arbitrary size. We do not assert the fort hypergraph is a matroid or balanced hypergraph.

## Exact checks and strongest falsifier

check.py independently enumerates every initial set on2x2 through2x8,3x3,3x4,4x4; verifies the strip transfer against enumeration; and computes strips n2..200. No scalar or binomial-normalized log-concavity violation on these inputs. All counts are integers. The numerical range is not an all-order theorem.

slices.py exhausts every disjoint intersection/difference choice for2x4 (6561),3x3 (19683),3x4 (531441), checking the stronger monotonicity c(r)<=c(r+1) before the center. No failure. slice_probe.py checks10000 fixed-seed candidate draws on each of3x5 and4x4, skipping odd |D|, with no central failure. Its draws are NOT10000 nontrivial successful slices; many vanish. No statistical inference or proof is claimed.

Strongest objection to a proposed full proof is that neither the transfer recurrence's adjacent coefficient signs nor the all-rectangle balanced-coloring inequality is proved. A single source triple with b(k)^2<b(k-1)b(k+1) would refute the source outright. A single fort-projection coloring slice with c(q)<c(q-1) would refute only the stronger bridge. The star example already proves that generic coloring symmetry is insufficient. These objections remain unresolved rather than being hidden behind finite evidence.

No PROOF.md, nomination, Lean or paper. Credit0, root counts6additional/36total unchanged. All writes confined to this lane; solo, no children/git/shared edits/external mutations. All computational helpers run under lane capped_run.py: hard AS512MiB,CPU210s,wall230s,BLAS1, sampled process-group RSS512MiB/CPU210s. Metadata/hash inventory scripts are likewise run capped. UTC and access provenance in provenance.json/http.jsonl.
