# T133E independent proof review, round 1 (correctness only)

## Verdict

**PASS_FULL_T133E.**

Every quantifier of the unchanged frozen statement (scope-freeze.md, SHA256 3b7f81a5eccb420aec318e3bd26e1c72c9193b184cdb507ad350095c7797ba74) is proved by candidate.md (SHA256 a5cebc35180338943c8a8bd330d2147875034a67a126f6bfeabf5c637425f49a), using the pinned source at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb as stipulated-true input and the classical Gabber–Galil frame bound as a paid classical input. I re-derived each new step below and found no gap that blocks the full target. There are no required objections. The optional objections are presentation and citation improvements. None of them changes a quantifier, a constant, or the polarity of the reduction.

This verdict concerns correctness only. Contribution, routine-encoding risk, novelty and campaign eligibility are separate questions. Nothing here bears on them. Parent alone decides acceptance.

## Target audited

Language E consists of the triples (G,H,k) with these properties:

- G and H are explicit adjacency matrices of finite, simple, undirected, uncolored, connected graphs of the same positive order.
- Each graph has maximum degree at most 101.
- Each graph has $h\ge 1/200000$, where $h(G)=\min_{0<|S|\le n/2}|E(S,V\setminus S)|/|S|$, and $h=\infty$ for a singleton.
- k is a binary integer with $k\ge2$.
- $G\equiv_k H$ under joint-update k-WL, with common color names and separate tuple histograms.

Malformed or out-of-class inputs are rejected. The claim is that E is EXPTIME-complete under deterministic polynomial-time many-one reductions, both for binary k and for unary k. Every hardness output must satisfy all graph restrictions, on yes and no instances alike. I checked that the candidate proves exactly this language. It does not prove a fixed-k, colored, regular, all-mates, or existential-family substitute.

## Source interfaces actually checked

All of the following are in the pinned variable-dimension manuscript, read from the author's authenticated private copy of the canonical blobs.

- `def:joint-wl` and `lem:wl-game` (sec. 02). Joint update with one z for the whole replacement vector; common names; histograms equal at every round. The game has k+1 slots, discards are free, the bijection is announced before Spoiler chooses a vertex, the same vertex may occupy several slots, and the winning condition is partial isomorphism (equality and adjacency) at every finite play. This matches the scope wording exactly. The reached-history principle is stated at the end of sec. 02.
- `lem:dimension-cap` and `prop:membership` (sec. 02). For equal positive order $n\ge2$ and $k\ge2$, $G\equiv_kH\iff G\equiv_{\min(k,n)}H$. The refinement decides in time $2^{O(n\log n)}L^{O(1)}$ after capping, and the binary comparison happens before any table is allocated.
- `prop:game-reduction` (sec. 07, lines 17–53). For $r\ge3$ and $K=r+1$, it has two hypotheses. (1) Partitions $V(W^\epsilon)=\coprod_B V_B^\epsilon$ with a fixed bijection $\Psi_{B,\xi_B}$ per offset, depending only on that offset and the graphs, whose unions over compatible offsets are induced-subgraph isomorphisms. (2) Nonempty, pairwise disjoint (for fixed $B,\epsilon$) query sets with zero decoding and shared-readout agreement at every reached history of any winning K-slot strategy, including at full occupancy. The conclusion is consistency $\iff$ Duplicator wins $\iff W^0\equiv_rW^1$. Its proof (lines 87–119) uses only hypothesis (1) to build the whole announced bijection. It uses at most r occupied slots, hence $|U|\le r$ active blocks, together with extensions to $U\cup\{B\}$ from `prop:exact-projection` for $|U|\le K$ (sec. 04, lines 171–186).
- `lem:block-fibers` (sec. 04, lines 136–160). $\mathcal Z_B^0$ is a vector space, and $\mathcal Z_B^1=\mathcal Z_B^0+\xi$ for every $\xi\in\mathcal Z_B^1$. Projections onto each name are full. Each block has at most six bits and at most four names.
- Section 06 construction (lines 84–167): spines, prefix forests, anchors, equality matchings and sorts. `graph:colored-promises`, `graph:readout-walk`, `graph:colored-translations`, and the incidence count inside the proof of `graph:uncolored-lifts` (lines 354–358).
- `prop:computation-images` (sec. 03, lines 405–413). This gives $r=2(p(m)+2)\ge8$, polarity "consistent iff $w\in L_0$", and polynomial generation. `prop:uniform-construction` (sec. 08) gives $|V(Y^\epsilon)|=O_M(b_*^8)$ and $s=O_M(b_*^8)$ with $b_*=r+2$, and its steps 1–3 build Y and the sort enumeration in polynomial time without witnesses. The proof of `thm:main` and `cor:unary-dimension` (sec. 08) supply the polarity chain and the unary transfer pattern.

The candidate's §2 summary of these interfaces is accurate. I found no mismatch between what T133E uses and what the source states.

## Re-derivation of the new steps

### A. Classical frame and its exact adjacency convention

HLW Construction 8.1 (expanders.txt lines 3420–3430) uses $T_1=\begin{pmatrix}1&2\\0&1\end{pmatrix}$, $T_2=\begin{pmatrix}1&0\\2&1\end{pmatrix}$, $e_1$ and $e_2$. Its neighbors are $T_1v$, $T_2v$, $T_1v+e_1$, $T_2v+e_2$ and the four inverse images. The text states that the 8-regular graph may have multiple edges and self-loops. The candidate's $T_0..T_3$ are exactly $T_1v$, $T_1v+e_1$, $T_2v$, $T_2v+e_2$ (my diagnostics check this for m=2..40). Theorem 8.2 states $\lambda(G_n)\le5\sqrt2$ for every positive integer n, where $\lambda=\max(|\lambda_2|,|\lambda_n|)$ (line 802). The operative form is Theorem 8.3: for real f with $\sum f=0$, $\sum_z f(z)\sum_i f(T_iz)\le\frac{5\sqrt2}{2}\sum f^2$.

With $A=\sum_i(P_i+P_i^{T})$, this says $f^{T}Af\le5\sqrt2\,\|f\|^2$ for $f\perp\mathbf 1$. A fixed point of $T_i$ contributes 2 to $A(v,v)$, which matches the candidate's "loops counted twice", and $L=8I-A$ has zero row sums. For $f=\mathbf 1_X-(|X|/N)\mathbf 1$:

$$f^{T}Lf=\mathbf 1_X^{T}L\mathbf 1_X=\sum_i 2\,|\{v\in X:T_iv\notin X\}|,$$

which is exactly the number of non-loop arcs crossing the cut. This uses $|\{u\notin X:T_iu\in X\}|=|\{u\in X:T_iu\notin X\}|$, which holds because $T_i$ is a permutation. Hence

$$|\partial X|\ge(8-5\sqrt2)\,|X|\,|X^c|/N\ge\tfrac{8-5\sqrt2}{2}\min(|X|,|X^c|)>0.4645\min(|X|,|X^c|).$$

So $h(F)>2/5$ in the min-form used later, and F is connected. This holds for every $m\ge2$, including m=2, where $T_0$ and $T_2$ are the identity. Exact enumeration gives $h(F)=2$ for m=2,3,4.

### B. Simple output despite loops and parallel arcs

Each arc (v,i) receives its own $a_{(v,i)}$ and $b_{(v,i)}$, with edges $q_v a$, $ab$ and $b\,q_{T_iv}$. A loop $T_iv=v$ gives two different edges $q_va$ and $bq_v$, because $a\ne b$. Parallel arcs, for example $T_0v=T_2v$ at $v=(0,0)$ or when m is even, use disjoint internal vertices. Y edges, station attachments, frame edges and private leaves are disjoint edge families. Therefore X is simple.

Degrees are as follows:

- original vertices: 20, since $\deg_Y\le3$ plus one station edge
- non-root stations: 100, and the root $q_{(0,0)}$: 101, since the base degree is 8 plus a fiber of at most 64
- $a_{(v,i)}$: 30, 32, 34 or 36, and $b_{(v,i)}$: 31, 33, 35 or 37
- leaves: 1

All leaf counts are nonnegative. The maximum degree is 101 and the root is unique. Connectivity follows from connectivity of F, since each cell is connected through its station.

### C. Offset-local degree invariance and equal order

For $\xi_B\in\mathcal Z_B^1$, the colored translation (`graph:colored-translations`) is a sort-preserving isomorphism of the induced block parts that fixes the anchor. I verified the external incidences directly from the construction (sec. 06, lines 111–153):

- Only anchors and proper-channel roots have neighbors outside their block.
- An anchor keeps its fixed anchor-path neighbors.
- Each proper root $f_{Bc,q}(u)$ has exactly one opposite root $f_{Cc',q}(u)$. Full projection makes the matching perfect, and this holds in both versions.

Hence $\deg_{Y^0}(v)=\deg_{Y^1}(\text{image})$ using only $\xi_B$. The source's own count at lines 354–358 states the same. Leaf counts $19-\deg_Y$ therefore agree, and $\Psi_{B,\xi_B}$ is a bijection $V_B^0\to V_B^1$. Station leaf counts agree because the version cardinalities of each sort agree, and port and dummy cells are identical. Equal order follows by choosing any legal offset per block. No compatibility is needed for this.

### D. Hypothesis (1): compatible unions and whole-bijection extension at full occupancy

Ownership is fixed and independent of valuation. Original vertices go to their block. A non-dummy station goes to the block of its sort, which is the block of every vertex in its fiber. Dummies go to one fixed block. Ports go to the owner of the tail station. Leaves go with their owner.

Edges between X parts are of two kinds. Y cross edges are handled by the source union lemma. Frame edges have fixed endpoints. A station–fiber edge always lies inside one part, and $\Psi$ preserves the sort and therefore the station. Leaves are adjacent only to their owner. Hence edges and nonedges are preserved for any family of offsets that agrees on shared names. Since no new cross-part edge involves a movable vertex, no frame edge couples two offsets.

The source proof of `prop:game-reduction` then applies verbatim. A slot request occurs with at most $r=K-1$ occupied slots. Every marked vertex lies in exactly one part, so at most r blocks are active. For each inactive B, exact projection gives an extension to $U\cup\{B\}$ with $|U\cup\{B\}|\le K$. The pieces form one bijection announced before Spoiler moves. One selection activates at most one block, including frame and leaf vertices. Exact dimension r is preserved, and no spare slot is consumed.

### E. 3-slot root/port/station identity, without hidden spare pebbles

At any reached history of a winning K-slot strategy:

1. **Degree.** Discard all pairs except (y,y') and request one slot. The announced bijection must map N(y) onto N(y'), otherwise Spoiler wins, choosing the preimage when needed. This uses 2 slots.
2. **Root.** By (1), the root is answered by the root, the unique vertex of degree 101.
3. **Station identity.** Suppose (q_v,q') is marked. q' is a station by degree. Discard all other pairs, mark the root (slot 2), and walk along a fixed word from (0,0) to v in $T_i^{\pm1}$, using slot 3 for the next vertex and then discarding the previous one. Each step's target is the unique neighbor of the current vertex with a prescribed degree:
   - station to $a_{(u,i)}$ (degree 30+2i)
   - station to $b_{(T_i^{-1}u,i)}$ (degree 31+2i, unique because $T_i$ is a permutation)
   - a to b, b to its head station, b to a, and a to its tail station (degrees 100/101)

   These degrees are pairwise distinct, so a loop arc and parallel arcs cause no ambiguity. By induction, using adjacency to the current walker response and the degree invariant at the new reached history, each response carries the identical label. At the end, the walker vertex equals $q_v$, and equality with the retained pair forces $q'=q_v$. At most 3 pairs are ever live. The auxiliary degree tests are separate continuations that discard everything except one pair. The number of rounds is unbounded, and no quantifier-depth bound is used.
4. **Sort identity.** Suppose (y,y') is marked with y an original vertex. Then y' is original by degree. Discard the other pairs and mark y's unique degree-100/101 neighbor. The response is y''s station, and by (3) it carries the same label. So y' lies in the same fiber, which means the same sort and block. This uses 2 slots, and (3) adds no more than 3 in its own continuation.

All four facts hold at histories where all K slots are occupied, because each test starts by discarding.

### F. Hypothesis (2): zero decoding and 4-slot readout transfer

The spine sort (B,0) in version 1 is exactly $\{s_B^1(z):z\in\mathcal Z_B^1\}$. With $\mathcal D_B^\epsilon(z)=\{s_B^\epsilon(z)\}$, which are nonempty and disjoint, E.4 gives zero decoding.

For simultaneous zero marks at $B\ne C$ sharing $\rho$, the route of `graph:readout-walk` exists in $Y^0$ between $s_B^0(0)$ and $s_C^0(0)$. Retain the two endpoint pairs, walk the intermediates with at most two consecutive live pairs (4 slots), and use adjacency to the retained endpoints at the first and last steps. Each response is an original vertex of the prescribed sort (E.4). Adjacency among original vertices in X equals adjacency in Y. So the responses form a sort-prescribed walk in $Y^1$ from $s_B^1(\zeta_B)$ to $s_C^1(\zeta_C)$. The converse half of the lemma gives $\zeta_B|_\rho=\zeta_C|_\rho$. The 4 walking slots are not added to the test slots, because each test is a different continuation from a reached history.

`prop:game-reduction` with $r\ge8$ then yields: consistent $\iff X^0\equiv_rX^1$.

### G. All-cut Cheeger bound with unequal cells

Cells $C_v$ contain $q_v$, its fiber, the ports of the arcs with tail v, and all their leaves. They partition V(X), and each cell is connected. Sizes:

- station plus leaves: at most 94 (root) or 93 (other stations)
- fiber: at most $64\cdot20$
- ports with leaves: $\sum_i(29+2i)+(30+2i)=260$

So every cell has size at most 1641 < C=2048.

Take $0<|S|\le N/2$, and let I, J and M be the cells inside S, outside S, and mixed. Each mixed cell contributes a distinct internal cut edge, so $|\partial S|\ge|M|$. Suppose $|M|<h_0|S|/(4Cd)$ with $h_0=2/5$ and $d=8$. Then $C|M|<|S|/80$. This gives $|I|>|S|/(2C)$, and using $|V\setminus S|\ge|S|$, also $|J|>|S|/(2C)$. Frame expansion in min-form gives at least $h_0|S|/(2C)$ arcs between I and $J\cup M$. At most $8|M|<h_0|S|/(4C)$ of them touch M, so more than $h_0|S|/(4C)$ arcs run from I to J. Each corresponds to a distinct edge $b_{(v,i)}q_{T_iv}$ with exactly one endpoint in S. Both cases give

$$h(X)\ge h_0/(4Cd)=1/163840>1/200000.$$

This holds on both versions and for every source instance. It needs only bounded connected cells, not equal cell sizes.

### H. Complexity

**Hardness.** The source compiler (`prop:computation-images`, sec. 08 steps 1–3) gives Y and s in polynomial time. Here $m=\max(2,\lceil\sqrt s\rceil)$ satisfies $m^2\le4s$, so the order is at most $2048m^2=O_M(b_*^8)$ and the matrices are polynomial. The output is $(X^0,X^1,r)$ with r in binary, and r is polynomial in |w|, so unary output is also polynomial. All promises hold on every input, and the polarity is $w\in L_0\iff$ consistent $\iff(X^0,X^1,r)\in E$.

**Membership.** First check the syntax, symmetry, zero diagonal, equal positive order, degree at most 101 and connectivity. Next check $200000|\partial S|\ge|S|$ over all $0<|S|\le n/2$, which takes time $2^n\cdot\mathrm{poly}$. Order 1 is accepted when $k\ge2$. Then cap the binary k at min(k,n) before any allocation (`lem:dimension-cap`) and run `prop:membership`, in total time $2^{O(n\log n)}\mathrm{poly}(L)\le2^{\mathrm{poly}(L)}$. For unary k, convert to binary first.

## Required objections

None. I found no blocking defect, missing quantifier, interface mismatch, or constant error.

## Optional objections (non-blocking)

1. **Classical citation.** §3 cites "$\lambda_2\le5\sqrt2$" from HLW. HLW states Theorem 8.2 for every positive n, attributing it to Gabber–Galil [GG81], but notes that its own text proves "a slightly weaker bound" in full (line 3434). The candidate's constants need only $\lambda_2\le8-2h_0$ with $h_0=2/5$, that is $\lambda_2\le7.2$; the slack down to 1/200000 tolerates about 7.34. A final write-up should cite the primary Gabber–Galil and Jimbo–Maruoka bound for the stated constant. Alternatively, it could note that the classical statement, not HLW's in-text proof, is the paid input. The operative statement used is the quadratic form of Theorem 8.3, and it would help to say so.
2. **Rayleigh step.** §3 says "for an indicator". It should say the centered indicator $\mathbf 1_X-(|X|/N)\mathbf 1$, and it should record the identity crossing arcs $=\mathbf 1_X^{T}(8I-A)\mathbf 1_X$ under the loops-counted-twice convention (section A above).
3. **§6 wording.** "Total station-plus-leaf count is at most 102 but in fact at most 94" is confusing. The precise figures are $94-f$ (root) and $93-f$ (non-root), where f is the fiber size. The bound 1641 is unaffected.
4. **§5 induction.** The forced-walk sentence should be stated as an explicit induction on the word length. The invariant is that the walker response has the identical label. The step uses adjacency to the previous response plus the degree invariant at the new reached history. Separately, the final equality step uses the retained station pair.
5. **§5 hypothesis (2) wording.** "Their source readouts are equal" holds trivially for two zero queries. The interface demands only zero queries, which is what the source lemma's hypothesis requires. It may help to say so explicitly.
6. **Diagnostics scope.** The author's diagnostics and my own (below) do not instantiate the real computation compiler and do not play the growing-dimension game. They are implementation checks only.

## Reading limits (this reviewer)

- **Fully read (variable-dimension source):** sections 02 (228 lines), 06 (548), 07 (311) and 08 (320).
- **Partially read (variable-dimension source):** section 03 lines 1–80, 226–305 and 400–429; section 04 lines 80–229; section 01 lines 1–50. Statements only.
- **Not read:** section 05, the exact-projection proof (sec. 04 lines 230ff), the remaining compiler and buffer proofs, and figures. These are stipulated source truths that are not used beyond their statements.
- **Companions:** not semantically read. A text search over all four companion trees for "expander", "Cheeger", "edge expansion", "bounded degree" and "maximum degree" found no expander statement. Companion overlap is a contribution question, outside this role.
- **Primary text (HLW):** expanders.txt lines 3395–3474 and 3560–3669 (Construction 8.1, Theorems 8.2, 8.3, 8.7 and 8.8, and the start of the proof), plus the definition of λ at line 802. I did not verify the harmonic-analysis proof; it is a paid classical input.
- **Other primaries:** the Lasserre, WL-dimension and uncolored-CFI primaries were not read. They bear on contribution, not on correctness.
- **Author material read:** candidate.md, scope-freeze.md, comparison.md, reading-limits.md, checkpoint.md, progress.md and verify.py, plus the parent intake.json identity block and proof-r1-brief.txt. I did not read or infer anything from any parallel review directory.
- **Retrieval route:** I read only the author's private copies of the canonical blobs. The author verifier, replayed below, authenticated them against Git blob SHA-1, the tree entry SHA and the pinned raw URLs. I made no independent network retrieval.

## Validation performed

- **Author packet integrity.** The external anchors match: MANIFEST.json 591ac5cc…, candidate.md a5cebc35… and scope-freeze.md 3b7f81a5…. The author verify.py, run with the canonical tree (eeecc1da…, 13223 entries), returned PASS with 64 payloads and 44 canonical blobs. The record is in author-integrity-replay.json. The packet is preserved unchanged, and my verifier rechecks this.
- **Independent diagnostics (diagnostics.py, results in diagnostics-results.json, about 9 minutes, pure Python).** These are implementation checks only and are not part of the proof:
  - HLW convention equality for m=2..40.
  - Exact h(F) for m=2..4, and a power-iteration $\lambda_2$ sanity check for m≤16.
  - Toy affine blocks of the source shape. I built Y exactly per sec. 06 and X exactly per candidate §3–4, then checked:
    - simple, connected, unique root, degree classes and equal order
    - sort sizes at most 64 and equal across versions
    - every single-block $\Psi$ is degree-preserving and onto its part
    - compatible unions are induced isomorphisms (positive), and incompatible unions are rejected for the edge/nonedge reason (reason-checked negative)
    - the readout-walk lemma, both directions and both versions
    - color refinement on the pair individualizes every frame vertex and separates sorts
    - cells are at most 1641
    - exhaustive whole-cell cuts on a 16-cell instance, plus random, mixed and BFS cuts, all at least 1/163840
- **Not performed:** a full compiler instance, the growing-dimension WL game, or an exhaustive vertex-cut enumeration of any output. Finite checks do not replace the proof above.
