# REVIEW: independent adversarial qualification of MathDB 362080

Claude Opus 5.5, high effort. Credit 0; campaign count 58/80 unchanged. Root alone adjudicates.

## Recommendation: EXCLUDE AS ROUTINE OR CORRECTION (routine branch; moderate-to-high confidence)

The theorem is true. I reconstructed it independently, and the author's proof is correct. It should not be credited, for this reason:

The lower bound reduces completely to a primary theorem I read in full. Hickingbotham and Wood, Lemma 24 and Theorem 25, are stated for arbitrary connected factors, in the very paper the source cites for its grid
bound (source reference [14]). Two short reviewer lemmas connect them to the target: an edge partition of the tree, and a relaxation of source Lemma 9 that lets pieces share vertices. The upper bound is a centroid recursion
extending the source's star bag, with the standard product bound (their Lemma 19). The full bridge, with every hypothesis paid, is in BRIDGE.md. The author's hand-off congestion count, which the author calls the only step that is not boilerplate, is unnecessary. This is the 336276 pattern, where the "substantive" step turned out to be avoidable.

This is a routine-application judgment. It is NOT an authenticated earlier solution, NOT a novelty finding, and NOT a mathematical objection. The user may overrule it. If so, the defensible unit is the all-trees theorem with the general all-connected-graphs form as a remark.

## Theorem verified

For k >= 1, every tree T on n >= k+1 vertices: c_k n^(k-1) <= tw(F_k(T)) <= 2 n^(k-1) - 1, with c_k depending on k only (PROOF.md: c_k = 3/(64 k^(2k+2)(k+1)3^k); BRIDGE.md, k >= 2: (1/2)(12k^2)^(-(k-1))).

## Gates (separate)

| Gate | Result |
|---|---|
| Literal | PASS. MathDB range 1<=k<=n-1, k fixed, Theta uniform over trees. Typo "$G$)" harmless. The "references" field saying "solved ... proved by Caputo, Liggett and Richthammer" is an extraction artefact: in source p.4 that sentence is about Aldous' spectral gap conjecture. |
| Original source | PASS. arXiv 2402.17962v3 read in full; Conjecture 20 viewed on p.20: 2<=k<=n-2, fixed k, trees. The literal widens to k=1 and k=n-1, both trivial for fixed k. |
| Final / correction | Bounded. The live arXiv record lists v1, v2, v3 (17 Apr 2025) and no journal reference. No final identified; absence not proved. |
| Ordinary proof | PASS. Independent proof written before the author file was opened; no gap. Author proof audited line by line; no error. |
| Prior (exact solution) | No earlier proof found in 2 searches and 3 GETs. Not a worldwide check. |
| Routine reduction | COMPLETE bridge supplied (BRIDGE.md), resting on a primary theorem read in full. Two short reviewer lemmas are not independently reviewed. |
| Novelty | Not cleared and not refuted. No claim either way. |
| Significance | FAIL under campaign policy (routine application). Judgment call. |
| Family | PASS: bounded nonoverlap with supplied scopes (family-comparison.json). |
| Formal | Not dispatched and not recommended. Endpoint assessed below. |
| Process | Disclosed items below; no breach of frozen, protected or guard boundaries observed. |
| Acceptance | Not earned. Credit 0. |

## Adversarial questions

**Q1. Is the general bound correct, and is the tree theorem a parameter instance?** Correct, and with a better form than the author's: c_k n^(k-1) <= tw(F_k(G)) <= 2(tw(G)+1) n^(k-1) - 1 for every connected G (PROOF.md). The lower bound uses no property of G beyond connectivity; the upper uses only tw(G). The two bounds match for every bounded-treewidth family, so trees are not the unique meeting point the author suggests; at K_n the upper bound also matches the true order n^k.
Decision: not a parameter instance of an existing law, because no published general law was found. In the 336276 sense it is one: tree structure does no work in the lower bound, and the same proof gives a law in which trees are the case tw(G)=1. I do not rest the exclusion on this; I rest it on the bridge. The general law appears nowhere in what I read; that is bounded evidence, not proof that it is new. It follows by the same bridge through a spanning tree.

**Q2. Is there a shorter route?** Yes.
- Route II (PROOF.md, BRIDGE.md) removes the hand-off entirely and gives better constants. T splits into k edge-disjoint subtrees; a relaxed Lemma 9 yields a product of k trees as a minor of F_k(T); Lemma 24 iterates.
- For k=2 the bound follows from the well-known tw(G box H) >= n for connected G,H with at least n vertices (Kaul intro, attributed there) plus the relaxed lemma.
- Minor monotonicity holds: if S is a minor of T then F_k(S) is a minor of F_k(T) (branch set of A: one token in each fibre over A). But a star-or-path dichotomy gives only about n^((k-1)/2), since n <= leaves * diameter. The spider with sqrt(n) legs of length sqrt(n) defeats it, so this alone does not suffice.
- Kaul Theorem 3, tw(G box H) >= (1/2)(tw G + 1)(tw H + 1) - 1, does not suffice: tree factors contribute only factor 2 per step.

**Q3. Source Lemma 9, spectral bound and star bramble.** All read and viewed.
- Lemma 9 (p.6) requires vertex-disjoint subgraphs. Only one piece can contain a hub, so on the spider it gives at most about 2 n^((k-1)/2). Author's claim verified.
- Spectral bound (Theorem 7 with Aldous identity, p.4): order n^(k-2) on the path and n^(k-3/2) on the spider. Author's claim verified. Reweighting cannot help on the path: with weighted degree normalised to 1, the linear test function gives lambda_2 <= 12/(n(n+1)). The author only recalled this; it is now proved.
- Star bramble (Proposition 8, p.5): B_i = {{s,i}: s<i}, disjoint and pairwise touching through {0,i}~{i,j}. On the path they touch only for adjacent i,j. Author's claim verified.
- Where the author is wrong: "the literal is not a short consequence of" the source's tools is true of Lemma 9 and Theorem 10 as printed, but not of Lemma 24 behind Theorem 10. "Shares no step with the source's lower bounds" overstates the distance.

**Q4. Prior work (2 searches, 3 GETs).** Search 1 (token-graph treewidth, separators, symmetric powers, double vertex graphs) found only the source and unrelated connectivity results. Search 2 found the product literature. Hickingbotham and Wood read at the relevant section. Kaul 2607.16778 read through Theorem 5 of its introduction: no token graphs, bounded nonmatch. Not covered: MathSciNet, zbMATH, citing-work indexes, registries (closed), the J. Graph Theory final of [14], Kozawa-Otachi-Yamazaki (bibliographic hit only), the "Grid Minors and Products" paper (third-party review snippets only), and the broader symmetric-power and reconfiguration literature beyond one query. No specific applicable unread proof was identified, so there is no HOLD.

**Q5. Family comparison.** All 57+39 supplied scopes compared. No treewidth, tree decomposition, bramble, separator, pathwidth, symmetric power or double vertex graph appears anywhere. The nearest neighbours differ in object and conclusion: 353203 (token addition/removal reconfiguration of power domination, K_{s,t}), 343536 (equitable partitions of grids), 366974 (positive matching decomposition of cycle products), 369421 (toroidal representation number). The supplied file has 57 records and omits 382297, the 58th result; its scope is known from the denials file (bunkbed on tournaments) and is unrelated.

## Author audit

No errors in Sections 3-4. Specifically: (U1)-(U3) correct; recursion closes with C_k=2k-1, since (C_{k-1}+2)=C_k and 1+C_k/2<=C_k; separator orientation correct; the side-grouping gives |A|,|B| >= 5N/18; pairs |P| >= N^2/32 using k^2 N/n <= N/8 at n >= 8k^2; hand-off invariants correct; load count correct in both cases (A: k(k-1)n^2; B: k n^2), total k^3 2^k n^(k+1).
Constants depend only on k. No tree shape is used. The range below n=8k^2 is not stated by the author, but for fixed k it is absorbed by tw >= 1. k near n: fixed k only, and for growing k the claim is not asserted. The author's upper constant 2k-1 is weaker than the 2 here; harmless.
The author's own significance doubts were correct and its self-test did not find the bridge.

## Strongest case FOR credit

A deliberate printed conjecture for a natural family, left open by authors who cited the very paper containing Lemma 24. It is proved in full, uniformly over all trees, with explicit constants. The source's printed lemmas do not reach spiders. No earlier proof was found. The shared-vertex relaxation of Lemma 9 appears in nothing I read. The statement is elementary and Lean-feasible, and the inherited record notes that 19 of the 57 accepted results are refutations or counterexamples, several small, so smallness alone has not been disqualifying.

## Strongest case AGAINST credit

The lower bound is three short steps ending in repeated use of a published lemma stated for arbitrary connected graphs, in the paper the source already uses for the same purpose. The source's Theorem 10 uses Corollary 26, whose sketch iterates Lemma 24; nothing about paths is needed. The upper bound is the source's star bag plus a recursion and a standard product bound. There is no new invariant, extremal structure, or parameter interaction. Tree structure plays no role in the lower bound. The author's distinctive step is unnecessary. Precedents 336276, 368315 and 352895 point the same way, and 328851 is the closest in form: a full printed conjecture reduced to an earlier primary theorem, excluded as a complete routine application.

## Why not the other recommendations

CREDITABLE would ignore a complete bridge to a read primary theorem, which is the campaign's explicit exclusion standard. PARK fits an unresolved specific prior or reading question; none remains here, and the unread JGT final does not bear on the exclusion unless its Lemma 24 differs materially.

## Formal assessment (no Lean run; dormant plan not offered because the significance gate fails)

Author endpoint is acceptable, but a stronger literal is better: no n0, for all k>=1, all n>=k+1, all trees on Fin n, explicit c and C, stated as "there is a decomposition of width at most 2n^(k-1)-1, and every decomposition has width at least c n^(k-1)". This avoids treewidth as a defined infimum except as a corollary and removes threshold clutter. Mathlib has no treewidth, so the TreeDecomposition definition needs fidelity review. The author's estimate of 1500 to 2500 lines is plausible and untested.

## Process disclosures

- Interrupted once and resumed. Confirmed nothing state-changing had been in flight; no action repeated.
- One runner display (hw_section_lower_bounds) was oversized and persisted by the harness outside the lane. I did not open it; re-read a capped range instead. Lane copies of its output and receipt exist.
- scopes_accepted57 exited 1 on a documentary KeyError; receipt retained; repaired with a changed script.
- Derived text and PNG extraction files in review-work/ were written by runner children, not write_lane.py: pdftotext and pdftoppm output (authorized PDF processing) and hw.txt (my own HTML-to-text conversion).
- Sampled runner telemetry only. Native, transient and writer peaks are unknown; no universal resource claim.
- Visual inspection covers source pp.4,5,6,20. Pages 1 and 2 were rendered but not viewed. HW statements were read as LaTeX alttext in HTML, not as page images. Scope comparison read first ~150 characters plus tags for each row and a full-text keyword scan, not every full record.
- Reconstruction is independent verification, not invention: TASK disclosed the mechanism. Route II, the upper constant, and the bridge are reviewer-derived.

Unless overruled, do not route to formal work. Stop at handback.
