# Ordinary work beyond the parking witness

No mathematical programs, experiments, enumeration, solver, CAS or formal execution. Author reasoning only; no independent PASS or helper credit.

## 337260: a proposed all-k upper-half construction; full target still unpaid

Actual original1710.01939v1 is Kiss–Sandor–Yang, On generalized Stanley sequences. Read Conjecture1 and Theorems1–3 pp2–3, the base-four construction of Theorem2 pp5–7, and full probabilistic proof of Theorem3 pp7–8. Source uses nonnegative integers; the positive-integer literal is harmless for the construction below since every chosen element is positive. The source random proof chooses step sizes in a short interval so the candidate (k-1)-sets are disjoint. Inclusion probability of order (log n/n)^(1/(k-1)) makes the uncovered probability summable; merely removing log leaves a bounded failure probability, not eventual covering. Neither Borel–Cantelli nor first moment removes this defect. The unrestricted literal is not restricted to greedy Stanley sequences.

Here is a deterministic multiscale slab construction for clause(i). Put r=k-1>=2 and K=2^(r+1)+r. Let B range over powers of2 with B>=12r, and write N=B^r. For each index j in{1,...,r}, define the integer interval I_j(B) as {0,...,j-1} if j<r, and {r*floor(B/(2r)),...,r*floor(B/(2r))+r-1} if j=r. Define A_B to consist of those integers a in[N/4,2^r*N] admitting an integer representation
 a=sum(i=1..r) e_i*B^(i-1), |e_i|<=KB,
with e_j in I_j(B) for at least one j. Signed digit representations need not be unique; counting representations is an upper bound, so uniqueness is unnecessary. Set A=union_B A_B.

Given any sufficiently large integer n, choose the power-of2 B with B^r<=n<(2B)^r. There is a base-B expansion
 n=sum c_i*B^(i-1), 0<=c_i<B for i<r, B<=c_r<2^r*B.
Define d_i=floor(c_i/i) for i<r and d_r=floor(c_r/r)-floor(B/(2r)), and let d=sum d_i B^(i-1). All d_i are nonnegative and d_r>=B/(2r)-1>0, so d>0. For j=1,...,r put a_j=n-jd.

The coefficients e_i=c_i-jd_i satisfy |e_i|<=KB: for i<r this follows from0<=c_i<B and0<=d_i<=B; for i=r use0<=d_r<=2^rB/r and c_r<2^rB. For the designated coordinate i=j<r, Euclidean division gives0<=e_j<j. For j=r, e_r=(c_r-r*floor(c_r/r))+r*floor(B/(2r)), in I_r(B). Thus each a_j has the required slab representation.

It remains crucial to ensure localization and positivity, not just the algebraic AP relation. For a_r, its leading coefficient is at least B/2-r. The absolute total contribution of all lower coordinates is at most
 rB*sum(i=0..r-2)B^i <=2r*B^(r-1).
Consequently a_r>=(B/2-3r)*B^(r-1)>=N/4 for B>=12r. Since d>0, a_r<...<a_1<n<2^rN. Therefore every a_j belongs to A_B, and a_r,...,a_1,n is a k-term progression in increasing order. A is an AP_k-covering sequence.

For each fixed j at most j coefficient values are available in its distinguished coordinate and at most2KB+1 in every other coordinate. Hence
 |A_B|<=r(r+1)/2*(2KB+1)^(r-1)=O_k(B^(r-1)).
If A_B intersects[1,x], localization gives B^r<=4x. Summing over powers of2 B up to(4x)^(1/r) is a geometric sum with ratio2^(r-1)>1, giving A(x)=O_k(x^((r-1)/r)). This proves the proposed upper half for all k, including k3. It does not prove clause(ii), and the full literal is a conjunction.

Failed variants: an unlocalized union of signed-digit slabs contains every fixed integer at large scales, since all high digits can vanish. The lower cutoff N/4 is essential; shifting the top step by floor(B/(2r)) keeps the last AP endpoint above this cutoff while leaving its distinguished top coefficient in an interval of bounded size. This repairs that failure. Ordinary random alteration is also insufficient: a positive density of uncovered targets would require too many repairs.

Remaining lower-bound gap: two selected members of A determine a progression and its endpoint, so counting supplies only a square-root lower bound for every k. To reach exponent(r-1)/r for r>2 one needs a structural upper bound for covering efficiency of r-term APs that does not assume A is random, evenly distributed, AP-free or greedy. Those assumptions are absent. Dense short blocks invalidate naive uniform-density progression bounds. No such lemma is proved. No full candidate/helper credit, prior clearance, final-source comparison or independent validation is claimed for this construction.

## 338136: three balanced-connectivity routes and precise obstruction

Actual1801.01795v2 (12Aug2018) read Corollary1.4, Section7.2, Lemma7.3 and its counting proof, and exact Conjecture7.4(1)(2). Literal matches the printed degree EQUALITY, not merely separate upper bounds. Both all-vertex in/out balance and O(k) maximum degree are deliberate. Source Section7.2 notes unions of k Hamiltonian cycles require connectivity of order k^2 in general, far stronger than the given k.

Route1, compress the sparse source subgraph. If H has at most kn+Ck^2 arcs and all in/out degrees>=k, then sum_v(d^+(v)-k)=sum_v(d^-(v)-k)<=Ck^2. Thus at most2Ck^2 vertices have any positive excess. This reproduces the quadratic exceptional count. It gives no O(k) count and no pointwise O(k) maximum: a single vertex can carry the whole Ck^2 excess. Averaging cannot reverse this inequality. Need an exchange that concentrates moderate excess on only O(k) vertices while separately bounding each degree.

Route2, use a bounded integral circulation with lower degrees k. In/out balance is an integral flow constraint. But feasible local degree constraints do not enforce global connectivity: a disjoint union of two Eulerian k-regular directed blocks satisfies them and fails strong connectivity. Adding arcs to join blocks consumes degree capacity and may spread exceptions. For k-arc-connectivity the omitted constraints are all directed-cut lower bounds; for k-vertex-connectivity the analogous constraints must hold after every deletion of fewer than k vertices. An integral degree-feasible circulation theorem alone is not a full bridge.

Route3, shortcut paths/ears or union branchings. Semicompleteness supplies one orientation between a pair, not the orientation and disjointness required to shortcut every linkage simultaneously. Deleting v along u->v->w may destroy a path witnessing connectivity through a tight separator, and a shared replacement edge cannot serve k internally disjoint paths. Unions of k in/out branchings retain a core hub and do not make all noncore degrees EXACTLY k; cancellation may break another root path. The needed lemma is a bounded-core, cut-preserving balanced exchange with enough slack simultaneously across every relevant cut/deletion set. None is constructed.

Source Lemma7.3 forces Omega(k) exceptions in its tournament family; this is compatible with the conjecture and is not a refutation. Its proof is read and not silently strengthened to Omega(k^2). Full target parked at the cut-preserving exchange lemma. No routine-adaptation exclusion from sparse total-edge bounds or stronger-connectivity Hamiltonian packing is justified.

## 378927: exact source-owned correction

Actual Kuehn–Osthus author primary maxcut3.pdf Section2 p3 prints the obstruction itself, attributed to Keevash–Sudakov. Take r3,ell6, four distinguished vertices among n vertices. For each pair{i,j} form H_ij of all triples containing both. Each has m=n-2 edges. In every partition into3 classes two distinguished vertices share a class. Their H_ij has ZERO rainbow edges, while (2/9)m-o(m)>0 for sufficiently large m. This is an asymptotic family, not a finite endpoint misunderstanding. It fully negates the arbitrary-ell literal. Source Problem4 asks the DISTINCT TWO-hypergraph question; the source itself explicitly says the arbitrary-ell extension fails. This is public/source correction0, not a new discovery. It also explains why a naive random-concentration extension fails: pairs of edges sharing two high-degree core vertices have persistent covariance. No claim this resolves the two-hypergraph question.
