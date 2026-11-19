# Eventual stability for frustrated cycles

## Exact scope and status

We prove the proposition `Frustrated.Conjecture19` already present in the inherited Pilot.lean, without changing that file. The production theorem is `Frustrated.conjecture19_proved` in EndpointV5.lean. It compiled and passed a separate kernel check; the critical transitive axiom audit compiled and passed a separate kernel check. This is an implementation result, with zero acceptance credit. Source-binding, significance, comparison with 105 credited scopes, independent fidelity review and independent extracted replay remain separate inherited/future gates. No public claim of novelty or publication is made.

The source is T. Kittipassorn and G. Meszaros, *Frustrated Triangles*, arXiv:1411.1749v2, Conjecture 19 on page 18. Documentary source URLs: https://arxiv.org/abs/1411.1749 and https://arxiv.org/pdf/1411.1749 . The owned PDF SHA256 is 79a754bb8827bbb63a00ae99b06b20d0b60950517c00d1ecfbbc546648aaa17a. The inherited acquisition reports completion 2026-11-14T05:49:49.331539+00:00. This session made no requests. Page 18 was freshly rendered and visually inspected. Binding to MathDB 329202 and earlier ordinary/source/substantial qualification are inherited, not independently reissued here. No final journal equivalence is asserted.

## Definitions and theorem

Let G be a loopless undirected graph on n vertices. An ambient simple k-cycle uses k distinct vertices, whether or not its consecutive pairs are edges of G. Count the cycle if an odd number of its consecutive pairs belong to G. Let f_k(G) be the count modulo rotations and reversal; an injective ordered tuple contributes to exactly one such cycle, with 2k tuples per cycle for k >= 3. Thus these are neither contained graph cycles nor arbitrary closed walks.

Write S_{s,n} for a star with s edges and n-s-1 isolated vertices. A cut graph has precisely those pairs with endpoints on opposite sides of a partition; either part may be empty. Distance means the number of unordered pairs whose edge status differs. It is not a number of vertex switches.

For every fixed integer k >= 3 and t >= 0 there is a single integer N(k,t) >= t+2 such that, for all n >= N(k,t) and every G on n vertices,

    f_k(G) < f_k(S_{t+1,n})

implies that G or its whole complement differs from a cut graph on at most t unordered pairs. The page-18 odd-n aside is excluded: it is false for even k, for example G=K_n, k=4, t=0 and odd n >=5. The theorem above retains the complement alternative exactly as in Conjecture 19.

## Structural reduction

Switching at U toggles precisely the pairs crossing the cut U. Each cycle crosses the cut an even number of times, so switching preserves f_k. Whole complementation preserves f_k for even k; for odd k it replaces f_k by T_k-f_k, where T_k=(n)_k/(2k).

Put s=t+1, D=k*s*2^(k-3), M=16D. For n >= 2(k+1), a path-extension double count gives

    8 f_4(G) (n-4)_{k-3} <= 4kn f_k(G).

Each star edge belongs to (n-2)_{k-2} ambient unoriented cycles, so f_k(S_{s,n}) <= s*n^(k-2). Bounding the displayed falling factorial uniformly below shows f_4(G) <= D*n^2 under the strict threshold.

A vertex u belongs to at most 4Dn frustrated 4-cycles. Switch at its original neighborhood; u becomes isolated. On the other n-1 vertices let d_w be the row degrees. The exact number of frustrated 4-cycles through u is

    sum_w d_w*(n-2-d_w).

Consequently the directed discrepancy from each row's preferred constant bit is at most 16D when n >=4. If two rows prefer different bits, their symmetric off-diagonal pair creates an error in at least one direction. If h rows prefer one, this gives h*(n-1-h) errors. For n-2>16D all preferences must agree. Thus the switched graph H is sparse, or its complement on the other vertices is sparse, with at most M edges.

The second alternative is realized on the WHOLE vertex set as Q=switch(complement(H),{u}). Complementing H makes u universal; the additional switch isolates it again. No n-1 incident errors are hidden. The inherited whole_sparse_normal_form proves the resulting sparse edgeCount bound; EdgeCardBridge proves that edgeCount equals the unordered Sym2 graphEdges cardinality used below.

For odd k, the second branch is impossible eventually: undoing its final switch gives a graph A switching equivalent to G with sparse whole complement. Both f_k(A)<s*n^(k-2) and f_k(complement A)<=M*n^(k-2) contradict T_k>(M+s)*n^(k-2) for large n. For even k, Q has the same count as G. Hence a sparse error graph E with at most M edges is obtained from G, or, when necessary for even k, from its whole complement, by switches preserving the relevant threshold.

## Full uniform sparse expansion

Let m=|E|, and for an error-edge subset F let N_k^tuple(F) count ordered injective k-tuples whose cycle support contains F. Write A(E) for the number of two-edge subsets whose edges meet. For each tuple the odd indicator has the exact finite expansion sum_{nonempty F} (-2)^(|F|-1). Summing gives

    2k f_k(E) = sum_{nonempty F subset E} (-2)^(|F|-1) N_k^tuple(F).

The inherited doubled expansion has scale 4k. SignedExpansion proves the division to 2k and the exact partition into singletons, adjacent pairs, and ALL remaining supports. For k >=4, put a=(n-2)_{k-2} and b=(n-3)_{k-3}. SingletonSum and AdjacentSum evaluate the first two contributions exactly:

    2k f_k(E) = 2k*(m*a-2*A(E)*b) + R_E.

Here R_E includes every disjoint pair and every support of size at least three, with its actual sign.

A completable support with at least three edges contains two disjoint edges. Indeed, otherwise the loopless pairwise-intersecting classification makes it a star or a triangle. A simple cycle uses at most two incident edges at a vertex, while a simple cycle of length at least four cannot contain a triangle. This argument includes supports forming an entire k-cycle. Disjoint edges have four distinct incident vertices. The inherited four-vertex completion bound then gives

    N_k^tuple(F) <= k^4*n^(k-4)

for every remaining support; impossible supports contribute zero. At most 2^M supports occur, and each absolute coefficient is at most 2^M. Therefore the single uniform bound is

    |R_E| <= C*n^(k-4),     C=2^(2M)*k^4.

No support-size truncation, sign assumption, density limit, or n-dependent hidden constant is used. FullRemainder proves both the unsigned majorant and the absolute signed bound, and SignedExpansion connects it to the actual graph count.

For a graph whose edges all meet a common vertex, no higher support completes and no disjoint pair occurs. The exact formula, for any center label, is

    f_k(E)=m*a-2*choose(m,2)*b.

CanonicalStar proves |E(S_{m,n})|=m when n>=m+1, including m=0, and specializes this formula to the source star.

For k=3, disjoint pairs cannot complete, and supports larger than three cannot complete. The remaining triple support has coefficient +4 at tuple scale. ThreeCorrection proves that exact correction and its nonnegativity. In ordinary unoriented notation it is the familiar +4 times the number of triangles, because a completed triangle has six ordered tuples. Thus

    f_3(E)>=m*(n-2)-2*A(E)>=m*(n-2)-2*choose(m,2)=f_3(S_{m,n}).

The formal endpoint uses the checked exact tuple correction and its nonnegativity; it does not require introducing a separate triangle-count definition or an unproved triangle-count bridge.

## Sparse minimum and the strict threshold

For k>=4, assume n>=2k and n>C*2^(k-3). The uniform falling-factorial inequality gives C*n^(k-4)<b. If not every pair of error edges meets, A(E)<choose(m,2). The evaluated expansion then exceeds the star formula: the adjacency deficit contributes at least 2*(2k)*b, while |R_E|<b.

If every pair meets, the error graph is a star or a triangle plus isolates (the empty case is separate and immediate). For a star R_E=0. For a triangle, every higher support is its triangle and cannot complete a k>=4 cycle, so R_E=0 as well. These give exactly the star formula. Hence f_k(E)>=f_k(S_{m,n}) uniformly for every m<=M, with no graph-dependent threshold.

The exact star formula gives

    f_k(S_{j+1,n})-f_k(S_{j,n})=(n-2-2j)*(n-3)_{k-3}.

This is positive for j<=M once n>2M+2 and n>=k. If m>=t+1, monotonicity and the sparse minimum contradict f_k(E)<f_k(S_{t+1,n}). Thus m<=t. SharpThreshold proves this both for k=3 and for all k>=4 using actual finite graph quantifiers.

## One common threshold and the edit witness

For k=3 take Ns=2M+4. For k>=4 take

    Ns=2M+4+2k+(2^(2M)*k^4)*2^(k-3).

Take No=max(2k,(2^k*(2k))*(M+s)+1), and then

    N=t+2+Ns+No+2*(k+1)+M+5.

These constants depend only on k,t. EndpointV5 chooses these thresholds before quantifying over n,G; all structural, sparse, star-existence and odd-complement bounds hold for n>=N. Its proof tracks the two switches in the complement branch, composes their cut bits by xor, and commutes whole complementation with switching. NearCut follows by toggling exactly the sparse error pairs, at most t of them. Empty cut parts and t=0 remain included. QED.

## Certificate and limits

The complete local production dependency closure comprises 60 Lean modules, including 45 rebuilt inherited modules and 15 new modules. The literal appendix, source/import/hash map, pinned helper/PINS record, command list and build instructions accompany this paper. There were 92 fresh formal calls including 17 failures, all preserved; no scientific experiments or network/search calls occurred. Every new production module was compiled and separately kernel checked. AuditV5 confirms the unchanged endpoint type and critical transitive axioms: only propext, Classical.choice, Quot.sound.

This manuscript and production certificate are not independent statement-fidelity review or a clean extracted replay. Existing process defects remain unwaived, including the new display/screening defects detailed in PROCESS-INVENTORY-v5.md. Existing source/significance/registry qualification remains inherited. Future independent review includes 105 credited scopes; zero credit or ledger/count action is claimed here.
