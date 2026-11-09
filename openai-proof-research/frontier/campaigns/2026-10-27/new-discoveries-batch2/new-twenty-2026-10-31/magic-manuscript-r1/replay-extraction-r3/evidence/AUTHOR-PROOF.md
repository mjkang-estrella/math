# MathDB 381805: formal candidate, no credit assigned

The graph is C7 on vertices 0 through 6, with four additional leaves 7 through 10 adjacent to vertex 6. Thus it is exactly G(7;0,0,0,0,0,0,4), with p=q=11. No isolated vertices, duplicated edges, or unrelated components are used. Give its vertices labels

    vertex: 0 1 2 3 4 5 6 7 8 9 10
    label:  3 2 4 5 8 6 1 7 9 10 11

The seven cycle edges have endpoint sums 5,6,9,13,14,7,4. The four leaf edges have endpoint sums 8,10,11,12. Together these are exactly 4 through 14. Label each edge uv by 26-f(u)-f(v). These are exactly 12 through 22, bijectively. Every vertex-edge-vertex total is 26. Consequently the minimum super edge-magic total constant is at most 26, whereas the conjectured value is 2q+(n+3)/2=27. This suffices to refute the asserted equality; the exact minimum is not claimed.

The primary source is Nayana Shibu Deepthi, arXiv:2212.05329v1, Conjecture 1.6 and Lemma 1.1. The actual journal PDF, Ars Combinatoria 159 (2024), 73–85, DOI 10.61091/ars159-08, retains it as Conjecture 1 on p.75. Both PDFs and dated HTTP/hash receipts are in sources. The journal's definition is an actual bijection V union E onto 1..p+q, with vertices exactly 1..p. The formal proof encodes that definition, rather than assuming the consecutive-sum lemma. It also proves exact family membership, vertex count and unordered-edge count, and takes the infimum over ALL such labelings.

Scope caution for root: some leaf counts are zero. The source conjecture does not require positive k_i, and its Section 3 explicitly allows k-c=0. This is a natural member of the stated cycle-with-leaves family, rather than an endpoint change to the labeling definition. Nevertheless, source-fidelity/significance review should explicitly adjudicate this point. Do not credit the result if root finds an intended positive-leaf restriction excluding this graph. A diagnostic MILP on the all-positive family G(7;1,1,1,1,1,1,8) found no labeling with consecutive-sum minimum 4; this does not prove any all-positive theorem and is not an extra result.

The source's Theorem 2 / arXiv Theorem 2.1 covers concentrated excess c only below 2n(k+1)/(n-3). Our k=0,c=4,n=7 lies outside its c<3.5 hypothesis. The uniform-family corollary and the other two constructed families likewise do not cover this witness. Thus this is not a parameter instance of a proved source theorem.

## Formal evidence

Magic381805.source_refutation : not Magic381805.SourceConjecture.

SourceConjecture quantifies over finite simple graphs with an odd cycle and exactly the specified number of pendant vertices at each cyclic vertex, restricted to super edge-magic graphs. IsFamily lists cyclic adjacency, rules out chords, requires every off-cycle vertex to be a degree-one neighbor of one cycle vertex, and counts its leaf fibers. IsSuperEdgeMagic uses an equivalence on vertices plus the actual unordered edge set and Fin(p+q), the complete vertex-label range, and the edge-total equation. All labels are shifted by one from Fin values. strength is Nat.sInf over the actual admissible constants. There are no assumed semantic lemmas.

The source-only ZIP is magic-proof-source.zip. The final packet extraction and replay are packet-extracted/ and packet-replay/. Run its replay.py with explicit --source, --output (fresh), --packages and --lean-bin. The replay uses Lean 4.34.1, serial -j1, warningAsError, no network, per-process 2-CPU affinity, CPU 120s, wall 140s and sampled RSS ceiling 6 GiB. The 37 mathematical module-origin declarations, including generated declarations and instances, all have bodies and no unsafe/partial flags; transitive axioms are confined to propext, Classical.choice and Quot.sound. leanchecker Magic also passes. See packet-replay/replay-result.json. The mathlib revision metadata was read and verified against d13f23b723b8a846827a245b89c10fc7d3f11612. Cached upstream oleans remain trusted; no upstream source-to-olean attestation or full upstream rebuild is claimed. leanchecker uses the same kernel installation.

The first full-import attempt exceeded a stricter sampled TOTAL-RSS guard and was killed; narrower imports fixed it. Initial audit attempts had a type-inference error in the harness, now corrected. Those failure logs are preserved. Only packet-replay/ is the final replay claim.

## Bounded prior-art comparison

OpenAlex exact-title, author-publication and citation queries are saved with receipts. The 2024 journal body was read, including definitions, conjecture and its three proved subfamilies. Later author bodies saved/read at their relevant main statements include the odd-cycle-composition h-vector paper, 2025 matrix-tree enumeration paper and 2026 uprooted-tree/parking-function paper; these concern ring Hilbert data or enumeration rather than minimum magic constants. Their theorem statements do not supply a subsumption bridge. The cactus-ring publisher route returned 403 and was not retried: that body remains unread. The single returned journal citation is a different group/Yang-Baxter topic and has not been body-cleared. This is bounded evidence, not a comprehensive bibliographic clearance.

Live GitHub /commits/HEAD receipts show OpenAI 4eaee87548250b2682affda7d05d947c05554bae and Omega b260643d3d496ad9cd04bfc3557fc9b7499de976. A truncated root recursive listing was NOT treated as complete: complete separate D5 (13342 entries) and Problems (1635 entries) trees were subsequently obtained. Target ID/name path screens are negative. OpenAI's complete cached preprint scope was hash-bound and reused under its unchanged head. No all-proof semantic registry review is claimed. Campaign ID/title/source-history searches found no matching old mathematical exclusion for this route, but an index non-match is not global novelty.

No publication, external messages, browser tabs, shared ledger edits, or count changes occurred. Independent adversarial review, source/significance adjudication and root acceptance remain required. Credit is zero until root accepts.
