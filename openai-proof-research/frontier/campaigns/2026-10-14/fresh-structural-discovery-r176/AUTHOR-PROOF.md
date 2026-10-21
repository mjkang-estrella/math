# Author proof for frozen S176A

This is a discovery proof submission for independent review, not a correctness or contribution grade. The immutable statement is STATEMENT.md, SHA256 d31fdccc24ab795b16c233db8c6ac69dab4fa5a5a90597299e6a5c547b144621. Source labels refer to the nine authenticated Source181 objects at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Those results and their operative proofs are stipulated true. We prove the additional algorithmic and compatibility assertions below. We use no oracle for longest cycles, expansion, or hypergraph matchings.

## 1. Representation, paid path operation, and verifiable outputs

Graphs have explicit finite vertex sets and assigned edge sets, exactly as in source preliminaries. At every recursive call they are simple; temporary pair quotients have their loops and extra parallel representatives removed before recursion. An indexed collection retains different indices even when its vertex sets overlap. All edge sets retain original-edge representatives.

We use the polynomial implementation of the classical Lovasz path-and-cycle construction, followed by the parity augmentation in source cor:endpoint-paths (BM Corollary22). For clarity about computational content: Lovasz's original Theorem1 proof recurses on the nonnegative integer 2e-a, where a is the number of nonisolated vertices. It optionally subdivides one edge, deletes the edges from a chosen vertex to its even neighbors, and recurses once. Its reconstruction follows distinct neighbor sequences along the returned paths and performs local edge replacements, without branching over decompositions. The parameter decreases; subdivision increases order by at most one per step and does not increase edge count after the subsequent deletion. Thus there are O(e) recursive steps, graph sizes remain O(n+e), and each reconstruction is polynomial. Subdivision suppression preserves simplicity of the output parts. These are the finite operations in the original proof, not an algorithm inferred solely from the existential theorem statement. Adding the parity vertex and then deleting it gives at most n simple paths, each original vertex an endpoint at most twice, in polynomial bit time.

The original PDF is accessible in the web reader, but direct download returned403 and its OCR is imperfect; private/reading-record.md gives this limitation. The above classical operation is not a proposed new contribution. It is also an operative dependency of the stipulated source.

Checking explicit partitions, path simplicity, edge-disjointness, endpoint loads, part counts, and integer/rational order bounds is polynomial: scan vertex lists and edge tables. A local randomized procedure below returns only after its stated output certificate has been checked. A failed attempt returns no graph to recursion. Checking these output certificates never requires checking expansion.

All large-scale cutoffs and constants below are absolute, fixed once. They can be chosen as integers satisfying the finitely many eventual inequalities in the source proofs and the additional explicit power/log inequalities below. These inequalities have strictly positive power margins. This specifies computable fixed constants, not advice depending on the input graph. Their values and the polynomial exponent are not optimized.

## 2. A polynomial routing specialization with teams

Let P be a simple graph of order r>=2 with cut expansion at least a positive rational h. Demands have distinct ends; each vertex is an endpoint at most k times; teams have at most b demands; each demand has a forbidden set of at most z vertices, concerning interiors only. Put

    L = ceil(32(r/h) ceil(log2(2r))),   t = floor(h/16).

Suppose

    h>=32,   k+2<=h/8,
    16 k r L/h + z + bL <= h/4.                         (R)

There is a deterministic polynomial-time procedure producing edge-disjoint simple routes of length at most L, avoiding the prescribed sets internally, with disjoint interiors within each team.

Process demands in any fixed order. Let F be all used edges and let c(v) count prior routes in whose interior v lies. Call v saturated when c(v)>=t. For the current demand xy, delete F and prohibit internally the saturated vertices, the demand's forbidden set, and all previous internal vertices in its team. Keep x and y even if in that union. Use a shortest xy path in this graph, aborting if none of length<=L exists.

We prove it cannot abort under (R). Internal counters never exceed t: a vertex is prohibited as soon as it reaches t, and endpoint use does not change this counter. Consequently

    d_F(v) <= 2t+k <= h/8+k <= h/4.

There are at most kr/2 demands altogether. Total internal occurrences are at most krL/2. Since t>=h/32, the saturated set has size at most16krL/h. The other forbidden vertices number at most z+bL. Let W be their union after removing x,y. It has size<=h/4.

For any nonempty U in V(P)\W with |U|<=r/2, the usable boundary in P-F-W has size at least

    h|U| - (h/4)|U| - |W||U| >= (h/2)|U|.

The last deduction uses simplicity, so each removed vertex costs at most one edge at each vertex of U. Thus a ball of size<=r/2 grows by a factor at least1+h/(2r) at its next step. Singleton cuts imply h<=r-1. Since ln(1+h/(2r))>=h/(4r), after ceil(8(r/h)ln(2r)) steps any ball has size>r/2. The balls from x and y intersect, yielding a walk and then a simple path of length at most twice this radius, which is less than L. Its interior avoids W and therefore all required restrictions. Shortest-path search implements the step in polynomial time. The construction proves all output claims by induction over the demands.

This is a specialization to a stronger expansion/load range. It does not algorithmize every parameter allowed in source lem:routing. The saturation principle is already present in CFS Lemma5.1; the contribution proposed here is its compatibility with both specific uses in the full source induction and the other algorithmic changes.

For source batch resolution, r<=D^1.02, h=D^.90/4, k=D^.01, b=D^.30, z=2D^.30. Here L=O(D^.12 log D), and the two potentially largest terms in (R) have orders D^.25 log D and D^.42 log D, both o(D^.90).

For source small residue, use r_i<=r<=D^1.02, h=D^.74, k=O(r/D^.90), b=1,z=0. The potentially largest term is

    kr_i L/h = O(D^(.12+1.02+.28-.74) log D)
             = O(D^.68 log D) = o(D^.74).

The constants may depend on the fixed sampling probability and expansion constant, exactly as in the source. The other conditions in (R) also hold above one absolute cutoff. Therefore this polynomial routing procedure replaces Aharoni-Haxell in both uses actually needed, without altering their output contracts.

## 3. Constructive overlapping boxes

We need an algorithmic either/or version of source lem:split-vertex-expansion, not a longest-cycle algorithm. Given a graph H of sufficiently large order u, put

    alpha=1/(32 ceil(log2 u)^2),   q=alpha^2 u/100.

In polynomial time we can produce either a simple cycle longer than q or a nonempty U of size<=u/2 satisfying |N_H(U)\U|<alpha|U|.

If H is disconnected, take any component of size<=u/2. Otherwise run DFS and stop at the state where unexplored and finished counts are equal to t. The stack is a path P of order L0=u-2t; no edge joins unexplored and finished vertices. If L0<alpha u/3, then t>u/3 and the unexplored set has external neighborhood contained in P of size<alpha t. It is a suitable U.

Otherwise L0>=alpha u/3. Let j=floor q; choose the cutoff so that j>=1 and j+1<=L0/2. Split P consecutively into X,J,Z with |J|=j and both outer segments of order>=L0/4, as in the source's rounding calculation. Search in H-J for a shortest X--Z path. If found, its interior avoids X,J,Z, so its union with the corresponding subpath of P is a simple cycle of length at least j+2>q. If not found, partition H-J into its component containing X and all other components, and take the smaller side U. Both sides have size>=L0/4 since one contains X and the other Z. Its external neighborhood is contained in J. Thus

    |N(U)\U| <= j <= alpha^2 u/100
                    < alpha L0/4 <= alpha|U|.

Every operation is DFS, BFS or component finding. The threshold uses a rational alpha with O(log u) bits; no real logarithm evaluation is needed.

Now let an input G have order N and average degree<=D. Put T=D^1.02. On a current assigned graph of order u>T run this either/or procedure. If it finds a cycle, remove that cycle and retry on the same vertex set. Otherwise use the source overlapping split U union N(U), V\U, with the same one-time assignment of edges within the overlap. Stop at order<=T. For all sufficiently large D, q(u)>D^1.01 uniformly for u>T: ceil(log2 u)<=2log2 u and u/log^4u is eventually increasing, so the source's uniform power margin applies with a different constant.

Every removed cycle therefore costs at least D^1.01 original edges, so their number is at most N/(2D^.01). Every split has overlap<|U|/(32log^2u). The exact potential f in source eq:split-potential and its subadditivity proof apply unchanged. Hence total leaf order<=N(1+2/log D), leaf orders are positive and<=D^1.02, and their vertex sets cover the input. We have not asserted that the final small boxes contain no long cycle; that assertion is unnecessary for either the output contract or subsequent work.

There are at most O(N) splits: each leaf has positive order and the sum of leaf orders is at most2N. There are at most |E(G)| cycle deletions. Thus the total number of either/or calls and their bit complexity are polynomial in the explicit input size. This proves the full first operation of source lem:scale-split effectively.

## 4. Polynomial expanding-piece extraction with a larger residual

Let H be a current assigned graph on u vertices inside a box of order y<=D^1.02. Set s=ceil(D^.90). If u=1, keep no piece. Otherwise compute the rational symmetric matrix

    M = L_H - 2s(I - 11^T/u).

There is a deterministic polynomial-bit-time test either certifying M positive semidefinite or supplying a rational vector v with v^TMv<0. For example use rational symmetric elimination with congruence transformations, treating a negative diagonal as a witness and a zero diagonal with a nonzero off-diagonal by a two-coordinate witness; otherwise take a positive pivot and its Schur complement. Fraction-free elimination and determinant bounds give polynomial bit sizes, including the transformations of a witness. Since M1=0, subtracting v's mean retains negativity and gives v perpendicular to1.

If M is positive semidefinite, apply its inequality to a centered cut indicator. For |A|<=u/2,

    e_H(A,V\A) >= 2s |A|(u-|A|)/u >= s|A|.

So H is a certified expanding piece of cut expansion>=s>=D^.90.

Otherwise v has Rayleigh quotient for L_H below2s. Subtract a median from v and split into the positive and negative parts f_+,f_-. Each support has size<=u/2. Their energies sum to at most v^TL_Hv; their squared norms sum to the norm squared of the median-shifted v, at least ||v||^2. Thus one nonzero nonnegative part f has Rayleigh quotient<2s. Sweep its positive squared values. The identities for U_t={v:f(v)^2>t} are

    integral |U_t| dt = sum_v f(v)^2,
    integral |boundary U_t| dt = sum_uv in E |f(u)^2-f(v)^2|.

Cauchy-Schwarz bounds the latter by

    sqrt( sum_uv(f(u)-f(v))^2 * sum_uv(f(u)+f(v))^2 )
      <= sqrt(2 Delta(H) f^TL_H f ||f||^2).

Some sweep cut therefore has

    |boundary U|/|U| < 2sqrt(Delta(H)s) <=2sqrt(us)
                     <=3D^.96

for sufficiently large D. Sorting rational f(v)^2 and evaluating each cut finds such a cut, without evaluating a square root. Its smaller side is U because its support has size<=u/2. Delete this cut to the residual and continue inside both sides.

Each charged vertex belongs to a smaller side at most log2 y times. The union of residual cut edges therefore has at most3D^.96 y log2 y edges. Its average degree is at most

    6.12D^.96 log2 D <= D^.98                              (S)

above a fixed cutoff. Terminal nonsingleton pieces have disjoint vertex sets, order at least D^.90 and at most D^1.02, and cut expansion at least D^.90. Retain the full box vertex set in the residual, including isolated vertices. The algorithm takes at most y-1 splits plus y terminal tests and is polynomial.

This is the one changed output of the source scale lemma: residual average degree D^.98 replaces D^.95. The exact algorithm avoids a sparse-cut oracle; the slower scale schedule below pays for this change.

## 5. Sampling, folding and local retries

The following procedures return explicit certified objects. A proof that an unobserved expansion event has constant probability is used to bound their expected work, not to certify their returned graphs.

**Folding.** Perform source heavy-neighbor removal and path trimming using the polynomial path operation in Section1. Fix all resulting demands. In each batch choose independent uniform pairings within its active sets, using one dummy vertex for an odd set, as in source lem:pair-folding. Compute the actual number Z of loops plus pairs of colliding nonloop edges. Source eqs:fold-first-errors through fold-cross-errors prove

    E Z <= (332/245) sum_i |X_i|.

Accept when Z<=2 sum_i |X_i|. Markov gives acceptance probability at least1-166/245=79/245. Remove actual loops and all but one edge per nonloop parallel class; this removes at most Z edges. Repeat a failed pairing choice, keeping the original batch unchanged. Each attempt is polynomial and the expected number of attempts is at most245/79. Empty active families use the identity quotient. Every accepted quotient has the exact order and representative properties of source lem:pair-folding. This does not rely on a certificate for the pairing probabilities.

**A small-residue attempt.** Given a simple graph G on R and a specified spanning subgraph T, use exactly the construction in source lem:small-residue, with its fixed eta,c and with the routing algorithm of Section2. Split T's edges randomly into three classes, randomly label vertices for three disjoint reservoirs, choose bounded-load outside representatives greedily, assign every nonreserved edge to a complement, partition into paths and close them, and take unused outside representative edges singly. A failure of a required degree/size check, greedy choice or routing aborts this attempt. At completion check the exact assigned-edge partition, at most9r completed parts, at most three residual simple graphs with disjoint vertex sets, total order<=eta r, and each order<r. These are polynomial tests. No recursive call is made in an attempt.

If T has cut expansion at least cD^.90 and D^.90<=r<=D^1.02, the source edge-splitting and vertex-sampling proofs give their good events with probability1-o(1), uniformly over this range. On those events the representatives exist by the source degree argument, and Section2 verifies that all greedy routes exist. Thus an attempt succeeds with probability at least3/4 above a suitable absolute cutoff. In a stand-alone use with a genuinely expanding supplied T, independent retries have constant expected number. Its output is valid even on an outcome outside those sufficient events, because the complete output certificate is checked.

**A selected-piece attempt.** For source batch resolution first form all quotients and compute their recursive partitions. This fixes every switch demand, team and forbidden set. For one selected expanding piece R, independently of that fixed data, split E(R) into two random classes P,T. Try all its demands with the routing procedure of Section2 in P. If successful let U be the used edges, and make one small-residue attempt on G=R-U with specified subgraph T. On any failure discard this entire local attempt and resample P,T from the original R. Accept only when both the routing and small-residue certificates pass.

When R has cut expansion>=D^.90, the two classes each have expansion>=D^.90/4 with probability1-o(1), by source lem:edge-split. On that event Section2 supplies all fixed demands. The unused graph R-U contains T unchanged because every route used P. Conditional on this fixed routed graph and T, the new independent small-residue randomness succeeds with probability>=3/4. The combined local success probability is therefore at least1/2, uniformly over all possible fixed demands satisfying the batch bounds. The expected number of these combined attempts is at most2. This conditioning is on a good split; it does not assert that conditioning a random graph on acceptance preserves its original sampling distribution.

The whole combined attempt is essential. If T were bad, retrying only the inner small-residue routine could have no termination guarantee. Similarly, globally restarting a recursive decomposition on any bad sample would not have the expected-time estimate proved here. We retry locally on the original piece, and never recompute the already completed recursive quotient partitions.

For an unselected piece, use the small-residue procedure with T=R and c=1. For a selected piece use the combined attempt with c=1/4. Across different pieces independent random bits may be used. We do not need a simultaneous good event over every piece in the graph.

All fair-bit sampling is effective. Uniform finite choices can use rejection from a power-of-two range, with mean less than two trials; each individual trial is finite. The fixed rational reservoir probability may be replaced by a fixed dyadic probability no larger than the source p and at least half of it. The source proof applies to this smaller fixed probability with the same eta conclusion and possibly a larger cutoff. Random permutations give the uniform pairings. Thus each local attempt has expected polynomial bit cost, and its expected total cost until acceptance is its mean attempt cost divided by its uniformly positive success probability. This identity follows by conditioning after the first failed attempt, so it does not require attempt cost and success to be independent.

## 6. Integer scales and preservation of the source's induction

We prove an effective version of source prop:induction-bound with the same potential

    phi(1)=1/2,
    phi(x)=max(1/2,1-1/sqrt(log2 x)) for x>1.

For n above a fixed cutoff set M0=ceil(log2 n), D0=2^M0, and

    M(j+1)=floor(99 M(j)/100),  D(j)=2^M(j).

Let m be the first index with M(m)<M_*, where M_* is a sufficiently large absolute integer; write D_*=2^M_*. Keep stages0,...,m-1. Choose M_*>=100. Then, at any processed stage,

    .98 M(j) <= M(j+1) <= .99 M(j).

The deterministic procedures of Sections3--4 supply prospective boxes, expanding pieces and residual graphs at every stage. Initial average degree is<n<=D0; by (S) the next input has average degree<=D(j)^.98<=D(j+1). Hence every call has its required input bound. This supplies the full prospective layer data in polynomial time. There are at most M0 stages, each of polynomial aggregate size as bounded below.

Fix

    K=1000, P0=4(K+1), eta=1/(100P0).

Then1.02(.99)^K<.001 and .98(.99)^K<.001. The prefix lemma in source lem:prefix-choice concerns only a nonnegative finitely supported sequence and an integer K; its proof applies with this value unchanged. Choose its index i with S_i>0 and sum_{j=0}^{i+K}S_j<=P0 S_i, unless all S_j vanish.

Put C0=2 for the box bound and C2=200C0. The scale recursion gives

    sum_{l=0}^j 1/M(l) <=100/M(j).

Therefore, for M_* sufficiently large, the source product estimate gives

    n <= N_j <= n(1+C2/M(j)) <=2n.                     (L1)

The same bound holds for the descendants of any fixed box, relative to its order and the relevant subproduct. The long-cycle count through stage j is at most100n/M(j), using D^(-.01)<=1/log2 D. Choose C2>=100, as above.

If all piece layers vanish, or if the prefix index has i+K>=m-1, use all stages. All boundary edges are taken singly, at cost<D_*n. In the latter case the total piece order is<=P0S_i<=2P0n. Small-residue processing contributes at most9P0S_i parts and residual total order<=eta P0S_i=S_i/100<=n/50. All these graphs have order<n, and Section5 gives their certified construction before any residual recursion. These terminal cases cost at most

    T(D_*)n + Cn/4,   T(D_*)=100+D_*+18P0,

including the inductive cost of their residual graphs. If C>=4T(D_*), this is<=Cn/2<=Cphi(n)n. Graphs below the fixed cutoff use every edge singly; enlarge C to cover those finitely many orders. The edgeless case returns immediately.

For the nonterminal case t=i+K<m-1, put D=D_i, w=M_i and H=C2(.98)^(-K). The lower inequality for the integer scales implies M_t>=(.98)^K w. Thus

    N_t <=(1+H/w)n,  long-cycle count<=Hn/w.            (L2)

Inside an indexed level-i box Y of order y<=D^1.02, the total descendant order T_Y lies between y and(1+H/w)y<=2y. Each descendant has order at most D^(1.02(.99)^K)<D^.001. Its boundary graph has average degree<=D_t^.98<=D^(.98(.99)^K)<D^.001. Hence their union F(Y) satisfies2|E(F(Y))|<=2yD^.001.

Use exactly the source batches and active sets with

    a=D^.01, L0=D^.03, B0=D^.30, sigma=D^.90.

Group descendant indices into batches of order sum<=B0; each descendant has order<=B0/2, so the number of batches is at most1+4y/B0. Their union vertex sets cover Y, their assigned edge sets partition F(Y), and their total orders are at most T_Y. At most2yD^(-.009)<=y/w vertices have degree>a in F(Y). There are at most y/sigma expanding pieces in Y, so all skipped intersections of size<L0 have total size at most

    y(D^(-.87)+4D^(-.15)) <= y/w.

Thus the source multiplicity argument, using one occurrence of each good piece vertex for the lower bound and total batch excess for the upper bound, gives

    S_i-4n/w <= Sigma <= S_i+Hn/w.                     (L3)

Here Sigma sums active-set orders over all indexed(W,R). This is not a per-batch degree assumption: good means degree<=a in the entire F(Y), exactly as required for the source's injection of demand endpoints into original edges.

The heavy-neighbor and pair-folding procedures of Section5 construct the simple quotients Q_W with unique original representatives. Every quotient has

    1<=q_W=|W|-sum_R floor(|X_WR|/2)<=B0,
    sum q_W<=N_t-Sigma/3
            <=n-S_i/3+A1 n/w,   A1=H+4/3.             (L4)

Apply induction to every quotient first. The resulting cycles determine all switch demands. Their per-vertex load in a fixed R across ALL batches is<=a by source eq:batch-global-load, since each demand-end occurrence uses a distinct incident edge of F(Y). Each team has size<=B0 and its forbidden set has size<=2B0. Heavy-neighbor remnants have singleton teams with no larger forbidden sets. Therefore Section5's selected-piece attempt applies to this entire collection. Once accepted, all quotient cycles lift to simple cycles by the exact source simplicity proof: interiors avoid the representative endpoints, routes of one team have disjoint interiors, and different routers inside Y have disjoint vertex sets. Distinct indexed boxes have disjoint assigned edges. We do not claim that they have disjoint vertices.

Each accepted piece attempt both provides its used routes and partitions the remaining R edges into completed parts and small residual graphs. All unselected pieces of the prefix are processed at their own scales by the stand-alone procedure. The resulting residual graphs H' have total order

    sum |V(H')| <=eta sum_{j<=t}S_j<=eta P0 S_i=S_i/100. (L5)

No cycle or edge can be double-counted: long cycles, prefix pieces and boundary batch graphs are an assigned-edge partition; each used router edge moves from its piece into exactly one lifted or closed cycle; the small-residue procedure handles only unused piece edges. Original batch edges are exactly the trimmed singles, remnant-path edges, pairing error edges and retained quotient representatives. Their four destinations partition those edges. The remaining original edges are exactly the assigned residual edges. Recurse on these residuals to finish the partition.

## 7. Part count and termination on every accepted execution

The source counting formulas now apply with the constants just specified. Set

    A2=max(9P0+8,9H).

Completed parts outside recursive work number at most A2(S_i+n/w): heavy-neighbor/pair-folding cost is at most8Sigma, piece small-residue cost at most9P0S_i, and long cycles at mostHn/w. Quotient orders obey(L4), residual orders obey(L5). All quotient orders and residual orders are<n. Consequently induction bounds the total part count by

    A2(S_i+n/w)+C S_i/100
      +C phi(B0)(n-S_i/3+A1n/w).                      (C1)

As phi>=1/2, the coefficient of S_i is at most A2-47C/300, nonpositive for C>=7A2.

Here D may slightly exceed n, unlike the literal source schedule. But D<=2n, hence log2 n>=w-1. Since .30w=log2 B0, for all sufficiently large w the nonconstant branch applies and

    phi(n)-phi(B0)
      =1/sqrt(.30w)-1/sqrt(log2 n)
      >=(1/sqrt(.30)-sqrt(w/(w-1)))/sqrt(w)
      >=(1/2)/sqrt(w).                                (C2)

After eliminating the S_i term, the remaining overhead in(C1) over Cphi(B0)n is at most C(A1+1)n/w when C>=7A2. Choose M_*>=4(A1+1)^2; (C2) absorbs it. Thus every returned partition has at most Cphi(n)n<=Cn parts. A bad expansion sample that nevertheless passed the explicit output tests has the same count: this proof uses its certified output contracts, not hidden expansion, in all deterministic counting steps.

The constants are selected in this order: fixed exponents and K; then P0,eta,C0,C2,H,A1,A2; then M_* large enough for all source sampling lemmas with c in{1,1/4}, all greedy routing inequalities, all DFS/spectral/scale power margins, and(C2) and its absorption; finally C>=max(7A2,4T(D_*)) and large enough for the finite base range. Increasing M_* does not change the preceding constants. This avoids circular dependence on C.

Local randomized retries terminate almost surely by the uniform positive conditional success probabilities of Section5. Each call has only finitely many local procedures. Every recursive child has strictly smaller order, so induction gives almost-sure termination of the entire algorithm. All terminating executions return certified partitions with the deterministic bound just proved.

## 8. Polynomial bit complexity, including recursion

All stages and certificates are effective on integers or rationals. Each D_j=2^M_j has O(log n) bits. Comparisons with fixed rational powers use integer powers: for example x<=D^.30 iff x^10<=D^3, and d<=D^.01 iff d^100<=D. Integer root ceilings compute s. Routing uses a rational lower bound comparable to its indicated h, for example floor(D^.74)/2 or floor(D^.90)/8; decreasing h by these fixed factors only changes constants in the already verified strict power margins. The length bound uses ceil(log2(2r)), computable from binary length. The counts and certificates never require numerically evaluating phi. Rational matrix elimination in Section4 has polynomial bit complexity and produces polynomial-size witnesses. The polynomial Lovasz subroutine may introduce auxiliary vertices, but only internally; their number is polynomial and all are removed before outputs are used.

At each stage(L1) gives total box order<=2n, and there are at most M0 stages. A box partition tree has O(n) leaves/splits in total, and every cycle deletion removes original assigned edges. A simple polynomial upper bound therefore covers all prospective-layer computations, prefix selection, batching, all fixed path decompositions and representative maps. There are polynomially many batches/pieces/demands. Each pairing retry and each piece retry has uniformly bounded expected repetitions, with expected polynomial attempt cost. Critically, piece attempts do not invoke the recursive algorithm. Thus there are absolute A,a such that expected nonrecursive bit cost of a call of order n is at most A(n+1)^a.

For the recursion, include among the requirements on the fixed base cutoff, before choosing C, that B0< n/2, eta<1/2, and w>=A1. From(L4)--(L5), total child order in the nonterminal case is at most

    n + A1 n/w - (1/3-1/100)S_i <=2n.

Each quotient child has order<=B0< n/2; each residual child has order<=eta r<=eta n<n/2. In the terminal case the child sum is<=n/50 and the same maximum-order bound holds. Ignore edgeless children, returning their empty partitions without recursion; in particular no order-zero child is needed.

Choose a fixed integer p>=max(a+2,4). For every realized list of nontrivial children of orders n_j,

    sum_j n_j^p <=(n/2)^(p-1) sum_j n_j
                <=2^(2-p)n^p <=n^p/4.                (T)

The recursive calls occur on arbitrary simple graphs, so their expected costs are bounded uniformly by induction, conditional on all prior randomness. Combining the expected local-work bound with(T), and enlarging a universal constant B for the finite base range, proves E T(n)<=B(n+1)^p. Vertex labels can be locally relabelled and maps retained; O(log n) bits per original identifier and polynomial map operations are absorbed by increasing a. Explicit output has at most |E(G)| edge occurrences and O(n^2 log(n+1)) bits, also within this bound.

Uniform sampling of finite choices has finite expected bit complexity; the expected local-retry calculation already includes those rejection steps. No exponential seed enumeration is hidden in the polynomial claim. This proves the expected Turing-bit-time assertion of frozen S176A, with q=p.

## 9. Comparison boundary and independent obligations

The new assertion is algorithmic: an explicit zero-error expected-polynomial algorithm for the source's full unrestricted graph class. Source181 gives the existence theorem and all structural vertex savings. BM supplies genuine expansion, sampling and iterative path/cycle machinery. CFS already supplies greedy saturation. Lovasz supplies the constructive path operation. Short-cycle algorithms, including LSY, already supply fast explicit partitions with a linear number of leftover edges; they do not bound the total number of cycle parts linearly in dense graphs. The present proof retains the source's linear PART count, permits long cycles, and adds no short-cycle claim.

The specific combined bridge offered for review is: a constructive cycle-or-separator alternative; a rational spectral extraction with loss D^.98; integer scales whose gap and inverse-log potential still pay that loss; greedy routes in BOTH source parameter regimes; and locally checked retries scheduled outside recursion. None of those ingredients in isolation is asserted new to the literature. This proof offers no claim of optimal runtime or constant and no directed, weighted or multigraph extension. The r33/r52 directed target and r175 spectral target remain unchanged.

Independent adversarial correctness review and separate primary-literature substantial-contribution review remain required. In particular reviewers should check the classical path-construction implementation, spectral sweep certificate, changed scale accounting, and independence/order of the local retries. No executable implementation or downstream formal support/manuscript/release is supplied by this discovery task. No acceptance or count is assigned.
