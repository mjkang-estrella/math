# T106O133 independent correctness review r1

Reviewer: Factory Droid / claude-opus-5-5, first independent CORRECTNESS review, 2026-10-20.
Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, stipulated true including operative proof operations
(AGENTS.md). This dispatch supersedes the NOT-DISPATCHED header of `proof-r1-brief-prepared.txt`;
its mathematical scope and independence rules were applied unchanged.

Scope of this verdict: correctness of the unchanged frozen Theorem A, Corollary B (decision and
promised search) and the density form, relative to the pinned source operations. No
contribution, acceptance, count, novelty or priority judgment is made. Upstream truth was not
audited.

## Verdict

**PASS for the full frozen scope.** Theorem A (every fixed integer k >= 1 and every fixed real
delta > 0), Corollary B for all finite loopless H, G with H non-bipartite and H -> G (decision
PCSP(H, G), and promised search under polynomial-time Turing reductions) and the density form all
follow from the pinned source 106 construction and analysis with the stated two-threshold change.
No blocking gap was found. Section 7 records non-blocking remarks about presentation.

## 1. Inputs authenticated before semantic use

- Author detached anchors, all exact (SHA256): FINAL.json 28c1114b...d832, packet/MANIFEST.json
  a14d03fc...cdaa, REPORT.md 86aa4c95...9643, frozen-statement.md 72654d28...1256,
  proof.md eb3ea4c6...c32c. The full author root (56 files) was fingerprinted before reading and
  again before sealing; there was no difference (`input-fingerprints.json`).
- Source 106: I fetched my own copies of all 11 files (README.md, main.tex, references.bib and
  sections/*.tex) from pinned raw URLs. Their git blob SHA-1 values equal the entries of the
  complete tree `sources/preprints-tree.json` (13223 entries, SHA256 eeecc1da...e09b). I read the
  author's private source copies only as listed hashes; the review is based on my own copies.
- Companion 105: build/00-introduction.tex fetched at the pin, blob 0f3d5a76...f686 matches the tree.

## 2. Frozen statement checked (exact text reread; not weakened)

Theorem A: for every fixed integer k >= 1 and real delta > 0, there is a deterministic
polynomial-time R_{k,delta} from explicitly encoded 3-CNF formulas to nonempty finite simple
undirected unweighted graphs, with SAT => G -> C_{2k+1} and UNSAT => alpha(G) < delta|V(G)|.
Constants and degree may depend on (k, delta). Corollary B as in KOWZ Conjecture 1.2 (wording
checked against the author's retained arXiv 2003.11351v3 extraction, lines 281-284: "Let H and G
be any non-bipartite loopless graphs with H -> G. Then PCSP(H, G) is NP-hard"). The frozen form
says "H non-bipartite and H -> G"; G is then non-bipartite automatically, so the scope is identical.

## 3. Source interface (pinned labels, my own reading of every source line)

Every occurrence of a fixed threshold or of three-colourability in source 106 sections was
located by search and by full reading:

| source place | content | role after modification |
|---|---|---|
| construction.tex 77-82 `eq:clique-test` | dist(x,Tx) <= 1/8 | replaced by rho |
| construction.tex 124-129 `eq:edge` | dist(x,Ty) <= 1/8 | replaced by rho |
| construction.tex 149-150 (`prop:encoding`) | exact comparison with 1/8 | exact comparison with rho (below) |
| construction.tex 172-201 `lem:completeness` | 3/8 > 1/3, three arcs | replaced by new colouring (Section 4) |
| lists.tex 11 | "set L = 64" | L = L_k = 8k+4 |
| lists.tex 15-24 `eq:independent-separation` | dist(A,TA) > 1/8 | dist(A,TA) > rho |
| lists.tex 26-40 `eq:bumps` | slope 32, 64-Lipschitz | slope 1/rho, (2/rho)-Lipschitz |
| coefficient.tex 11-13 | beta, K from `lem:influences` with L = 64 | with L = L_k |
| parameters.tex 10-12 | delta < 1/3, L = 64 | delta_0 <= 1/4, L = L_k |

No other section (preliminaries, alignment, alignment-proof, the remainder of lists and
coefficient, parameters 13-87) contains a fixed numerical threshold. `thm:junta` (prelim 60-67)
and `lem:influences` (prelim 91-99) are stated for every finite L >= 0. `lem:alignment` and its
proof (alignment-proof.tex, which states it "has no graph-theoretic or analytic hypotheses")
depend only on (s, d, eta).

Properties of f actually consumed downstream (my enumeration, matching the author's table):
values in [-1,1]; f(Tx) = -f(x); f = 1 on A; f constant across zero links; f L-Lipschitz within
each grid copy for d_infinity. These enter through: McShane extension, clipping and
odd-symmetrisation (lists 42-61: needs the grid data L-Lipschitz and odd, T a d_infinity isometry);
`eq:compatibility` (zero-link constancy, 2L/D); `eq:subchain-functions` and `lem:subchain-lists`
(sL-Lipschitz, `thm:junta` with sL); `lem:separated-lists` (locality only); `prop:aligned-bound`
(L-Lipschitz in z for `lem:influences`, `coeff:mean-zero` from oddness, `coeff:one-step` L/m,
`coeff:deletion-error` 2L/D, `coeff:grid-error` 2Ls/P, and "F_b = f = 1 on locations of A" at
coefficient.tex 278-282); proof of `thm:main` (parameters 49-87: q > 1/delta, 8 eps < delta,
4^r d^2 sigma < eps).

## 4. Independent verification of the new deductions

Notation: N = 2k+1, rho = 1/(2N) = 1/(4k+2), L_k = 2/rho = 4N = 8k+4.

**4.1 Encoding.** Finite distances are n/D with integer n (construction 146-148), so
dist <= rho iff n(4k+2) <= D, an exact integer comparison. The rest of `prop:encoding` (tuples,
grids, integer shortest paths with infinity stored separately, common denominator C_0,
C_0 N^{r-1} >= 1 vertices, no loops or multi-edges, Label Cover in polynomial time for fixed
sigma, constant-size trivial branches) does not involve the threshold. Output is nonempty in
every branch (one vertex, K_q, or C_0|C|^{r-1} >= 1). The edge rule is symmetric because T is an
involutive dist-isometry (construction 73-75, 128-129). Distinct vertices with equal location x are
adjacent iff dist(x,Tx) <= rho, which is excluded outside the clique branch. Deterministic, and
time/size polynomial with constants depending on (k, delta) only. VERIFIED.

**4.2 Completeness.** Trivial branch: no clauses -> one vertex -> C_N. Empty-clause branch is
UNSAT only. Otherwise value 1 gives phi: X -> T nonexpanding for dist with phi(Tx) = phi(x)+1/2
(`lem:completeness` first paragraph, threshold-free and stipulated). Clique test: dist(x,Tx) >=
1/2 > rho, so it fails. Edge x~y: d_T(phi(x), phi(y)+1/2) <= dist(x,Ty) <= rho (the distance is
finite, so nonexpansion applies). Claim, verified with lifts: a' in [i/N,(i+1)/N), a lift b' of
phi(x) with |b' - a' - 1/2| <= 1/(2N); since 1/2 = k/N + 1/(2N), a'+k/N <= b' <= a'+(k+1)/N, hence
(i+k)/N <= b' < (i+k+2)/N (strict because a' < (i+1)/N). So c(b) - c(a) is k or k+1 = -k mod N;
c is well defined on T since integer shifts change floor(N b') by multiples of N. With
psi = -2c, differences are -2k = 1 - N == 1 or 2k == -1 mod N. For N >= 3 these are the two
neighbours in C_N, so psi is a homomorphism (G_phi has no loops). All endpoints are safe for every
k >= 1. VERIFIED. Control (not proof): `arc_check.py` checks this implication in exact rationals
on grids containing all arc endpoints and all boundary distances, k = 1..7; ALL_OK. A
negative control with threshold 1/(2N) + 1/200 at k = 2 finds 150 violations, as expected.

**4.3 Soundness interface.** Unsatisfiable: Label Cover value <= sigma. The empty-clause and
clique branches output K_q with alpha/|V| = 1/q < delta_0. Otherwise:
- (S1) dist(A,TA) > rho: for distinct selected vertices by the missing edge, for x vs itself by the
  failed clique test (which holds at every point), finitely many strict inequalities including
  infinite distances. VERIFIED.
- (S2) f = bump(dist(x,A)) - bump(dist(Tx,A)), bump(u) = (1-u/rho)_+, bump(inf) = 0.
  [-1,1]-valued (difference of two [0,1] values). Odd (T^2 = id). f = 1 on A: first bump 1;
  dist(Tx,A) = dist(x,TA) >= dist(A,TA) > rho for x in A, and bump(u) = 0 for u >= rho, so the
  strict inequality suffices even though the bump radius equals the threshold. Zero-link
  constancy: x -> dist(x,A) and x -> dist(Tx,A) are 1-Lipschitz for the extended pseudometric
  (same component on both ends of a zero link, so finiteness agrees). Within a copy: all points are
  in one component, Tx and Ty share a copy, dist <= d_infinity, each bump is (1/rho)-Lipschitz in
  u on [0, inf) and identically zero where infinite, so |f(x)-f(y)| <= (2/rho) d_infinity(x,y).
  VERIFIED, with L_k = 8k+4.
- The source bump radius 1/32 (a quarter of the threshold) is not used anywhere else: no
  downstream step uses disjointness of bump supports or a margin between radius and threshold.
  I checked this specifically in lists.tex 26-73 and coefficient.tex 45-286.

**4.4 Parameter order with L_k.** Rational 0 < delta_0 <= min(delta, 1/4), rational
0 < eps < delta_0/8; beta, K = `lem:influences`(L_k, eps); m with L_k/m < beta/2; lambda with
lambda K < eps; s >= 2 with (1-p_m)^s < eps; gamma with s(2gamma)^2/beta^2 < eps; even P with
2L_k/D < gamma and 2L_k s/P < eps; d = max{1, J(sL_k, gamma)(m+1)^s}; (r, mu) =
`lem:alignment`(s, d, eps); rational sigma with 4^r d^2 sigma < eps; only then `thm:label-cover`;
integer q > 1/delta_0. Each choice depends only on earlier ones and (k, delta), so all are fixed
finite data. This satisfies `eq:parameter-bounds` and `eq:source-soundness` exactly as in source.
The source restriction delta < 1/3 is used only to choose delta_0 and in no inequality; delta_0 <=
1/4 satisfies it. VERIFIED.

**4.5 Theorem A soundness assembly.** `lem:good-pairs`: unaligned probability <= 4^r d^2 sigma +
eps < 2 eps; `prop:aligned-bound`: <= 6 eps at aligned pairs (its hypotheses are no clique branch,
nonempty independent set, `eq:parameter-bounds`, and the f/F properties of 4.3); exact
uniformity of the sampling law from multiplicities. So |A|/|V| <= 8 eps < delta_0 <= delta, and
the empty set also satisfies the strict bound because |V| >= 1. VERIFIED.

**4.6 Corollary B.** H loopless non-bipartite: a shortest odd closed walk is a cycle of length
2k+1 >= 3 (a repeated vertex would split it into two shorter closed walks, one odd; length 1 is a
loop). So C_{2k+1} -> H. Take c = |V(G)| and delta = 1/c. SAT: G_phi -> C_{2k+1} -> H.
UNSAT: a homomorphism g: G_phi -> G has independent fibres because G is loopless; one of the c
fibres has size >= |V|/c > alpha(G_phi), a contradiction. Hence a polynomial-time many-one
reduction from 3SAT to PCSP(H, G) (the YES and NO sets are disjoint because H -> G). VERIFIED.
Search: one oracle query on X followed by a polynomial-time check of the returned map against
X and G decides the promise problem. On X -> H every valid answer is a homomorphism to G; on
X -/-> G no answer passes the check. The author's "run for its time bound" phrasing and the oracle
phrasing both work. VERIFIED.

**4.7 Density form.** For every non-bipartite H and fixed delta > 0, R_{k,delta} with
C_{2k+1} -> H gives SAT => X -> H and UNSAT => alpha(X) < delta|V(X)|. VERIFIED (see remark R1).

## 5. Checks requested in the brief, item by item

- Exact rational threshold and clique test, deterministic multiplicity expansion: 4.1.
- Preprocessing and nonempty outputs in every branch: 4.1, 4.2, 4.3.
- Endpoint-safe half-open arc colouring for every k >= 1: 4.2.
- Bump radius and slope, oddness, boundedness, zero-link constancy, extended-pseudometric
  infinities, f = 1 on A, within-copy L Lipschitz control: 4.3.
- Every downstream list, coefficient, junta and alignment dependence on L, and no hidden fixed
  thresholds: Section 3 and 4.4.
- Choice order, alphabets, fixed real delta, strict soundness < delta: 4.4, 4.5.
- Arbitrary H/G sandwich, fibre counting, promised search and polynomial bounds: 4.6, 4.7.
- Author line citations checked: lists.tex 42-61 (McShane), parameters.tex 10-37 and 49-87,
  KOWZ lines 281-284, and every LaTeX label cited in proof.md exists at the pin with the stated
  content.

## 6. Requested comparison checks (correctness-relevant only)

- The proof does not route through any 2-to-1, Rich 2-to-1 or FMW statement. It uses only
  source 106 `thm:label-cover` (ordinary projection Label Cover), `thm:junta`, `lem:influences`
  and 106's own proved lemmas. The literature status therefore does not affect correctness.
- Rich premise: pinned 106 introduction lines 106-112 and pinned 105 introduction lines 75-81
  both state explicitly that the Rich 2-to-1 condition is not part of 105's ordinary 2-to-1
  theorem. So the pinned 105 statement does not as stated meet the Rich premise of
  arXiv 2605.09815v2 Theorem 1.8. I did not test whether it could be strengthened, which is outside
  correctness scope. No equivalence or difference is assumed.
- FMW supplement (Remark 1.13): not located or read by me. FMW and other general threshold
  applications were not examined beyond this; that question belongs to contribution review.
- Pinned companion titles (749 top-level preprint directories) were scanned for
  odd/cycle/homomorphism/promise/colouring/independent/games keywords. No title states an
  odd-cycle or PCSP(H,G) result; only titles were scanned (not an absence certificate).

## 7. Non-blocking remarks

- R1 (density form, large delta). For delta > 1/|V(H)| the YES set {X -> H} and NO set
  {alpha < delta n} of the density promise problem can overlap. NP-hardness via a many-one
  reduction is still exactly what is proved. Taking delta_0 <= min(delta, 1/|V(H)|) also makes
  every UNSAT output non-H-colourable, so the outputs land in the disjoint parts. This is not a
  gap; it is a reading note.
- R2. proof.md Section 6 says "c >= 3 because G is non-bipartite". This is true but not needed.
- R3. The finite data (J from Austin, (r, mu) from alignment via compactness) are existential
  constants, exactly as in source; the frozen statement asserts existence for each fixed (k, delta)
  and no uniformity in k, so this matches.
- R4. Chronology preserved: the author did the threshold audit and completeness calculation before
  freezing (working-notes Steps 3-5). No claim is made here that no derivation preceded the freeze.

## 8. Read extents and limits

See `reading-limits.md`. Artifact checks in this packet are not the mathematical judgment; the
mathematical judgment is Sections 3-7.
