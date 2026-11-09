A 45-letter word refuting the toroidal-grid representation conjecture

DRAFT • 4 November 2026 • MathDB 369421

AI-assisted research and writing: this draft and its dossier were prepared by an OpenAI Codex implementation agent from the frozen discovery, review and root-replay materials. No human authorship or affiliation is asserted. This is an unpublished draft for root review; it awards no accepted credit.

Abstract

An explicit 3-uniform word represents the Cartesian product C<sub>3</sub> □ C<sub>5</sub>. Its length is 45, and its two-letter subwords alternate exactly on the 30 edges, failing to alternate on all 75 nonedges. Consequently R(C<sub>3</sub> □ C<sub>5</sub>) ≤ 3, refuting Conjecture 1 of Alshammari, Kitaev and Pyatkin [1]. The dossier supplies complete pair evidence and reuses a byte-identical Lean certificate. The significance is modest: a small certificate at the first new parameter case. We claim neither a new search method nor priority. The accepted journal manuscript is embargoed and unread, so retention in that body remains qualified.

1. Definitions and the exact question

All graphs here are finite and simple; words are linear, finite sequences. For distinct vertices x and y, let w|{x,y} be the word obtained by deleting every other letter. They alternate if consecutive letters of this subword are unequal. A word represents a graph G precisely when this alternation is equivalent to xy being an edge for every distinct pair. It is k-uniform if every vertex occurs exactly k times. A graph is k-representable if such a representing word exists. Following the source, its representation number R(G) is the least positive such k, and is infinity when no representation exists. In particular, complete graphs admit one-copy words; zero is excluded from the minimum.

For m,n ≥ 3, the toroidal grid TGr<sub>m,n</sub> = C<sub>m</sub> □ C<sub>n</sub> has vertices (r,c) with 0 ≤ r &lt; m and 0 ≤ c &lt; n. Vertices are adjacent when their row is equal and their columns are consecutive modulo n, or their column is equal and their rows are consecutive modulo m. Thus both coordinates have wrap edges. The source assumes m ≤ n without loss of generality; our example obeys this convention.

Section 4 of [1], printed pages 9–10, gives 3-representants for TGr<sub>3,3</sub> and TGr<sub>3,4</sub>, with a column-major letter convention for those displayed words. Figure 2 explicitly depicts TGr<sub>3,5</sub> and TGr<sub>4,4</sub>. The surrounding text says, “However, no 3-representation for larger toroidal grid graphs are known. So, we would like to pose the following conjecture.”

<b>Conjecture 1 [1] (verbatim, with mathematical typography).</b> “If n, m ≥ 3 and m + n ≥ 8 then R(TGr<sub>m,n</sub>) ≥ 4.”

The following source remark identifies TGr<sub>4,4</sub> with the 4-dimensional cube, notes a known 4-representation and describes three-representability as open. That last historical remark has since been superseded by [6]; it does not affect the statement refuted here. MathDB 369421 records the same universal lower bound. Its cached open label is not evidence of novelty.


--- PAGE BREAK ---


2. The word and a direct finite proof

<b>Theorem.</b> The graph C<sub>3</sub> □ C<sub>5</sub> has a 3-uniform word representation. In particular, Conjecture 1 is false.

Label vertex (r,c) by 5r + c, so each displayed integer is a single letter, including the two-digit labels. Take the following word w (line breaks have no meaning):

0 8 4 5 9 11 12 13 10 1 2 6 11 0 1

14 5 10 3 4 7 0 8 9 6 5 12 11 2 1

7 6 13 12 3 2 8 14 10 13 4 3 7 9 14

The occurrence positions, numbered from 1, are shown below. They certify directly that w is 3-uniform on the full vertex set.

letter | positions | letter | positions | letter | positions

0 | 1, 14, 22 | 5 | 4, 17, 26 | 10 | 9, 18, 39

1 | 10, 15, 30 | 6 | 12, 25, 32 | 11 | 6, 13, 28

2 | 11, 29, 36 | 7 | 21, 31, 43 | 12 | 7, 27, 34

3 | 19, 35, 42 | 8 | 2, 23, 37 | 13 | 8, 33, 40

4 | 3, 20, 41 | 9 | 5, 24, 44 | 14 | 16, 38, 45

<b>Alternation test.</b> If a has positions p<sub>1</sub> &lt; p<sub>2</sub> &lt; p<sub>3</sub> and b has q<sub>1</sub> &lt; q<sub>2</sub> &lt; q<sub>3</sub>, then the pair alternates if and only if either p<sub>1</sub> &lt; q<sub>1</sub> &lt; p<sub>2</sub> &lt; q<sub>2</sub> &lt; p<sub>3</sub> &lt; q<sub>3</sub> or the same inequalities with p and q exchanged. This is immediate by sorting the six positions: the induced word must be ababab or bababa. Equivalently, simply filter w to these two letters and compare successive letters.

<b>Proof.</b> Construct the edge set by taking the unordered pairs joining (r,c) to (r,c+1 mod 5) and to (r+1 mod 3,c), then removing duplicates. This gives the Cartesian torus including its wrap edges. Check the position table using the preceding criterion. The edge subwords appear in Table 1; the complete outcome for every unordered pair appears in Table 2. Each entry agrees with the adjacency definition. There are 105 pairs, of which 30 alternate and 75 do not. The full dossier records each induced subword and, for every nonedge, a location of two equal successive letters. Hence w represents the graph.

Since a positive 3-representation exists, the defining minimum satisfies R(C<sub>3</sub> □ C<sub>5</sub>) ≤ 3. At m = 3 and n = 5, both parameters are at least 3 and m + n = 8. The conjecture would give 4 ≤ R ≤ 3, a contradiction. This proves its negation; an equality R = 3 is not needed. □

The verifier is deliberately elementary: for a &lt; b, set s = [x for x in w if x in (a,b)], test all consecutive entries of s for inequality, and compare the result with membership in the independently constructed edge set. The dossier also evaluates the strict-position criterion. Neither check consults a solver or a Lean result.


--- PAGE BREAK ---


3. Complete pair certificate

<b>Table 1.</b> All edges and their induced alternating subwords, arranged in two columns. Spaces distinguish individual vertex labels.

edge | induced word | edge | induced word

0, 1 | 0 1 0 1 0 1 | 5, 6 | 5 6 5 6 5 6

0, 4 | 0 4 0 4 0 4 | 5, 9 | 5 9 5 9 5 9

0, 5 | 0 5 0 5 0 5 | 5, 10 | 5 10 5 10 5 10

0, 10 | 0 10 0 10 0 10 | 6, 7 | 6 7 6 7 6 7

1, 2 | 1 2 1 2 1 2 | 6, 11 | 11 6 11 6 11 6

1, 6 | 1 6 1 6 1 6 | 7, 8 | 8 7 8 7 8 7

1, 11 | 11 1 11 1 11 1 | 7, 12 | 12 7 12 7 12 7

2, 3 | 2 3 2 3 2 3 | 8, 9 | 8 9 8 9 8 9

2, 7 | 2 7 2 7 2 7 | 8, 13 | 8 13 8 13 8 13

2, 12 | 12 2 12 2 12 2 | 9, 14 | 9 14 9 14 9 14

3, 4 | 4 3 4 3 4 3 | 10, 11 | 11 10 11 10 11 10

3, 8 | 8 3 8 3 8 3 | 10, 14 | 10 14 10 14 10 14

3, 13 | 13 3 13 3 13 3 | 11, 12 | 11 12 11 12 11 12

4, 9 | 4 9 4 9 4 9 | 12, 13 | 12 13 12 13 12 13

4, 14 | 4 14 4 14 4 14 | 13, 14 | 13 14 13 14 13 14

<b>Table 2.</b> The complete upper triangle of the alternation matrix. For row a and column b &gt; a, 1 means alternation and 0 means failure. Dots suppress the diagonal and lower triangle. These entries also equal the torus adjacency matrix; thus zeros check nonedges, not just absence from an edge list.

a \ b | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14

0 | . | 1 | 0 | 0 | 1 | 1 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | 0

1 | . | . | 1 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0

2 | . | . | . | 1 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 1 | 0 | 0

3 | . | . | . | . | 1 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 1 | 0

4 | . | . | . | . | . | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | 0 | 1

5 | . | . | . | . | . | . | 1 | 0 | 0 | 1 | 1 | 0 | 0 | 0 | 0

6 | . | . | . | . | . | . | . | 1 | 0 | 0 | 0 | 1 | 0 | 0 | 0

7 | . | . | . | . | . | . | . | . | 1 | 0 | 0 | 0 | 1 | 0 | 0

8 | . | . | . | . | . | . | . | . | . | 1 | 0 | 0 | 0 | 1 | 0

9 | . | . | . | . | . | . | . | . | . | . | 0 | 0 | 0 | 0 | 1

10 | . | . | . | . | . | . | . | . | . | . | . | 1 | 0 | 0 | 1

11 | . | . | . | . | . | . | . | . | . | . | . | . | 1 | 0 | 0

12 | . | . | . | . | . | . | . | . | . | . | . | . | . | 1 | 0

13 | . | . | . | . | . | . | . | . | . | . | . | . | . | . | 1

14 | . | . | . | . | . | . | . | . | . | . | . | . | . | . | .

Each entry of both tables is regenerated from the literal word by verify.py. All 75 zeros have an explicit failure certificate in verification.json: first_block is a one-based index j in the six-letter induced subword with s[j] = s[j+1]. All graph edges are obtained independently of this matrix. This gives a reproducible exhaustive finite proof rather than a sample of favorable pairs.


--- PAGE BREAK ---


4. Formal correspondence and trust limits

The reused packet contains Definitions.lean, Witness.lean and Audit.lean. Its endpoint is <b>Toroidal.mathdb_369421 : ¬ Toroidal.Conjecture1</b>. The archive is copied byte for byte; its SHA-256 is:

9f16ff5afa9a23b693443c0916507a8103bef5f23e431ca6c39e8cb4e7318200

Definitions.lean uses Vertex m n = Fin m × Fin n. CycleAdj tests either modular successor direction, and Adj takes the disjunction of equal-row/cyclic-column adjacency and equal-column/cyclic-row adjacency. For the conjecture’s parameters these are exactly simple cycle factors. Alternates filters the list to two letters, zips it with its tail and requires unequal entries in every zipped pair. This is linear-word alternation. Represents requires every vertex to occur k times and, for all distinct ordered pairs, equivalence of alternation and adjacency. Symmetry means the unordered-pair certificate checks the same relation.

The formal representationNumber is a value in WithTop Nat: it returns the least positive k for which a representing list exists, using Nat.find, and returns top if none exists. This captures both the minimum and the infinity convention. Conjecture1 quantifies over all natural m and n with guards 3 ≤ m, 3 ≤ n and 8 ≤ m + n. It is not a conjecture restricted to the graph checked here.

Witness.lean contains the coordinate form of w. The current ordinary verifier parses those coordinates and recovers the displayed word exactly under (r,c) maps to 5r+c. The theorem witness_represents establishes Represents 3 5 3 witness by kernel decide. The existence lemma and number_le_three pass from that finite certificate to the minimum, using Nat.find_min'. The final theorem specializes Conjecture1 at (3,5) and derives the impossible inequality 4 ≤ 3 in WithTop Nat. There is no solver-correctness assumption or unproved graph bridge.

Audit.lean enumerates local Toroidal declarations, including generated proof constants, collects their transitive axioms, and rejects local axioms, unsafe or partial declarations, implemented-by replacements and extern metadata. The frozen independent audit log contains 23 local declarations and no flags; the present verifier recounts these log entries. Endpoint dependencies are propext, Classical.choice and Quot.sound.

The independent review reports fresh strict compilation and explicit-module leanchecker checks for each of the packet’s three modules. The root’s separate replay-result.json records PASS for its own extracted rebuild and checker runs, with a separate metadata audit and source scan. The recorded toolchain is Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52, with mathlib pinned to d13f23b723b8a846827a245b89c10fc7d3f11612. These are inherited replay receipts, not new executions in this manuscript lane.

This lane performs a fresh safe-extraction test without executing the packet: it verifies the archive hash, accepts exactly the expected flat regular filenames, rejects links and unexpected paths, bounds member sizes, and creates files exclusively in a fresh local directory. No Lean, lake, leanchecker or SAT/ILP solver was run here. The packet is not repacked or edited.

Trust remains in the interpretation of the source, the Lean kernel and installed toolchain, and the cached upstream oleans used by the earlier replays. A full upstream source rebuild is not claimed. The ordinary proof and pair checker allow the finite claim to be assessed without trusting the discovery solver. Formal correctness does not establish literature novelty, priority, or exact retention in an unread accepted manuscript.


--- PAGE BREAK ---


5. Related work, retention and significance

The grid and cylinder constructions in [1] address zero or one cyclic coordinate, respectively. They do not add both families of wrap edges. The isolated toroidal examples there are the smaller cases (3,3) and (3,4). Thus the proposed lower bound begins at the next parameter sum, attained by (3,5) and (4,4); the certificate refutes the full universal claim at the first new case in the triangular-factor branch.

Broere and Zantema [2], Theorem 10, prove that for k &gt; 1 a k-representable graph G has a (k+n−1)-representation after Cartesian product with K<sub>n</sub>. Taking a 2-representation of C<sub>5</sub> and n = 3 yields 2 + 3 − 1 = 4 copies for C<sub>5</sub> □ K<sub>3</sub>, isomorphic to our graph. That upper bound does not give the present three-copy word. Broere’s thesis [3], Example 6.5 and Figure 27, already supplies a 3-representation of (K<sub>3</sub> □ K<sub>2</sub>) □ K<sub>2</sub>, namely C<sub>3</sub> □ C<sub>4</sub>; it is a relevant predecessor.

Kitaev and Pyatkin [5] study chessboard graphs. Their two-row rook construction and their other stated results do not treat this torus. Rook adjacency must not be substituted for cycle adjacency, and deleting graph edges arbitrarily does not preserve a representing word. Halldórsson and Kitaev [6], Proposition 3.2, state that Q<sub>4</sub> is not 3-representable; together with its known 4-representation, C<sub>4</sub> □ C<sub>4</sub> really needs four copies. This supersedes the source’s historical open remark but does not refute the toroidal conjecture. We do not independently replay that exclusion here.

<b>Existing methodology.</b> Akgün, Gent, Kitaev and Zantema [4] give a general positional SMT encoding and a representation-number tool. Their representation-number census covers connected graphs through nine vertices. That tool is generic and shares a coauthor with [1]. Solver search for uniform representations is therefore established methodology. The discovery dossier reports a separate total-order SAT model on letter occurrences; the current certificate is checked independently of any solver. We make no new-method claim, and no separate result or credit is assigned to search or the Lean bridge.

<b>Accepted-manuscript qualification.</b> The author publication list, entry 176, identifies [1] as to appear in Journal of Automata, Languages and Combinatorics and links its PDF to arXiv:2507.16469. Strathprints record 95696 gives acceptance on 26 February 2026, keeps the toroidal-conjecture sentence in its abstract, and links arXiv as an access document. This is positive author-side and institutional linkage. However, the accepted author manuscript is staff-only under an embargo to 2099 and was not read. We refute the conjecture in the read arXiv version; exact retention in the accepted body is unverified.

<b>Bounded prior-art screen.</b> The dossier preserves the independent review’s source bodies, searches and receipts, and the root’s later registry-refresh.json, whose verdict is CLEAN after hit review. The root screened complete relevant path lists at OpenAI/math head 4eaee87548250b2682affda7d05d947c05554bae and Omega head d9880e9f2c329bb3db982f33791419d5d90126b9. This was a path/topic screen, not a full-body survey. No target certificate was located in that bounded investigation. We assert no priority and no exhaustive novelty clearance; no new network search was performed for this draft.

The mathematical significance is modest: a short, fully checkable counterexample settles an explicit universal conjecture. It supplies neither an infinite family nor exact representation numbers for further tori. The root ruling permits packaging with qualifications; this draft awards zero accepted credit, and root alone decides acceptance.


--- PAGE BREAK ---


6. Dossier and reproducibility

The full dossier includes this manuscript source and PDF, the exact cached MathDB raw line with a SHA-256 receipt, the source PDF and HTML, related source bodies and access receipts, the original Lean archive, safe extracted sources, prior review and root replay evidence, and fresh ordinary pair checks. Frozen inputs are hashed before and after work. REPRODUCE.md gives offline commands, resource limits and the distinction between current checks and inherited formal replays.

Running verify.py with python3 -I regenerates all mathematical counts and both certificate tables from the literal word. The word has 3 × 5 = 15 letters in its alphabet and 3 × 15 = 45 positions. There are 15 × 14 / 2 = 105 unordered pairs; each vertex has degree four, giving 15 × 4 / 2 = 30 edges and 105 − 30 = 75 nonedges. Direct enumeration independently obtains these counts. Numerical metadata such as dates, identifiers, source theorem labels and software versions are checked against the frozen inputs, rather than treated as mathematical computations.

For a standalone manual check, use the position table and test the two strict interlacing orders for every a &lt; b. Compare the result with equal row and cyclically consecutive columns, or equal column and distinct rows. For C<sub>3</sub>, every pair of distinct rows is cyclically adjacent. This recipe covers every wrap edge and every nonedge, and it has no dependence on search history.

The paper and dossier remain DRAFT. The documented AI assistance, unread embargoed accepted manuscript, generic SMT predecessor and limited prior-art screen are substantive qualifications. There are no invented human authors, affiliations, publication claims or priority claims. Only the refutation of Conjecture 1 is proposed for root’s consideration.

References

[1] Nawaf Shafi Alshammari, Sergey Kitaev and Artem Pyatkin. On the representation number of grid graphs and cylindric grid graphs. arXiv:2507.16469v1 (2025), Section 4, printed pages 9–10. To appear in Journal of Automata, Languages and Combinatorics, per the frozen author and repository records. https://arxiv.org/abs/2507.16469

[2] Bas Broere and Hans Zantema. The k-cube is k-representable. arXiv:1808.01800, downloaded version, Theorem 10. https://arxiv.org/abs/1808.01800

[3] Bas Broere. Word-representable graphs. Master thesis, Mathematics, Radboud University Nijmegen, 18 September 2018. Example 6.5 and Figure 27. Source copy and original URL receipt are in the dossier.

[4] Özgür Akgün, Ian Gent, Sergey Kitaev and Hans Zantema. Solving Computational Problems in the Theory of Word-Representable Graphs. Journal of Integer Sequences 22 (2019), Article 19.2.5. https://cs.uwaterloo.ca/journals/JIS/VOL22/Kitaev/kitaev11.pdf

[5] Sergey Kitaev and Artem Pyatkin. On the representation number of chessboard graphs. Acta Informatica 63, article 33 (2026). DOI: 10.1007/s00236-026-00547-w. https://doi.org/10.1007/s00236-026-00547-w

[6] Magnús M. Halldórsson and Sergey Kitaev. The first savings in word-representations of hypercubes. HAL hal-05800339v1, deposited 14 October 2026. Proposition 3.2. https://hal.science/hal-05800339v1

Retention evidence: Sergey Kitaev’s publication list, entry 176 (frozen author-list body and receipt); Strathprints record https://strathprints.strath.ac.uk/95696/ (frozen repository body and receipt). No DOI is supplied for [1]–[4] or [6], because none is asserted from the verified inputs.
