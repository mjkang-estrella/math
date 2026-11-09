MathDB 339235 — mathematical certificate, NOT an acceptance or novelty certificate.

Source: Lau–Shiu–Ng, arXiv:1805.04888v1, Conjecture 3.2.
For every even n >= 4, the local antimagic chromatic number of M_(2n) is conjectured to equal 4.

Take n=6. Index the edges by the cycle (0,1),(1,2),...,(10,11),(11,0), then (0,6),...,(5,11).
Assign the labels 17,13,7,8,3,15,6,18,4,5,12,2,10,1,9,16,14,11 in that order.
Every integer from 1 to 18 occurs once. The vertex sums are
29,31,29,31,25,29,31,25,31,25,31,25.
Every edge has different sums at its ends. Therefore a local antimagic labeling uses exactly three colors, so the minimum cannot equal four.

Mobius.LocalAntimagicChromaticNumberEq is the attained-minimum definition: an admissible labeling attains k, and every admissible labeling has at least k colors. The endpoint negates the full universal conjecture, using n=6. There is no bounded-surrogate theorem or extra hypothesis. The vertex set has 12 vertices, and adjacency_literal, simple_edges_nodup and no_loops_and_in_range certify the precise simple cycle-plus-antipodes graph. Label length and bijection are supplied by List.Perm with range' 1 18. No out-of-range index contributes to any vertex sum.

Lean 4.34.1, only Init imported. No mathlib needed. Run in this directory:
  lean -j2 -M3500 -DwarningAsError=true -o Mobius.olean Mobius.lean
  LEAN_PATH=. leanchecker Mobius
  LEAN_PATH=. lean -j2 -M3500 -DwarningAsError=true Audit.lean
Put the pinned Lean bin directory on PATH. Audit enumerates every Mobius-prefixed declaration, including generated declarations, and rejects transitive axioms outside propext, Classical.choice, Quot.sound. 19 declarations audited in this packet.

Trust: prebuilt Lean core dependencies and the installed kernel are trusted; no complete upstream rebuild is claimed. Independent fidelity and novelty review, manuscript and root acceptance remain outstanding. A 2022 follow-up arXiv:2203.06594v1 claims M8 has value four but uses 132 rather than 156 in its proof. This packet uses M12 and does not rely on that proof. Significance and possible source-correction exclusion are explicitly unresolved.
