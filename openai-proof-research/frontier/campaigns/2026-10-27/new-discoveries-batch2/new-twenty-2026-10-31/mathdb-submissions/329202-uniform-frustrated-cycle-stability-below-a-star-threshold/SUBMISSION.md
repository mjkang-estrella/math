# MathDB 329202: Uniform frustrated-cycle stability below a star threshold

- Problem: https://mathdb.com/p/329202
- Source: K; i; t; t; i; p; a; s; s; o; r; n; /; M; e; s; z; a; r; o; s; ,;  ; F; r; u; s; t; r; a; t; e; d;  ; T; r; i; a; n; g; l; e; s; ,;  ; o; w; n; e; d;  ; a; r; X; i; v; 1; 4; 1; 1; .; 1; 7; 4; 9; v; 2; (; 8; A; p; r; i; l; 2; 0; 1; 5; ); ,; C; o; n; j; e; c; t; u; r; e; 1; 9;  ; p; r; i; n; t; e; d; p; 1; 8; ;;  ; e; x; a; c; t;  ; p; r; o; o; f; -; e; m; p; t; y;  ; r; e; t; r; i; e; v; e; d;  ; M; a; t; h; D; B; 3; 2; 9; 2; 0; 2;  ; r; e; c; o; r; d; .;  ; I; n; t; e; r; n; a; l;  ; F; e; b; r; u; a; r; y;  ; d; a; t; e;  ; i; s;  ; n; o; t;  ; a; r; X; i; v;  ; r; e; v; i; s; i; o; n;  ; d; a; t; e; .;  ; F; a; l; s; e;  ; o; d; d; -; n; /; e; v; e; n; -; k;  ; a; s; i; d; e;  ; e; x; c; l; u; d; e; d; .
- Outcome: **PROVED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `Frustrated.conjecture19_proved : Frustrated.Conjecture19`, `Frustrated.independent_expanded_endpoint`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `PAPER-v5.md`, `LEAN-SOURCE-APPENDIX-v5.md`
- Lean source: `mathdb-329202-proof-packet.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Positive bounded prior-method and endpoint comparison supports substantial uniform stability argument; not inferred from open label, formalization, finite tests or keyword absence. remaining_literature_limits: 1996extrema and changed2019final comparisons remain bounded unread limitations;no whole-target counterpart positively established.; Owned v2 primary only;no journal-final identity guarantee.; Dated catalogue statements,not all manuscriptproof bodies/worldwidepriority.; Owned retrieved target,not live canonicalpage observation. not_claimed: False odd-n/even-k remark; Worldwide priority guarantee; Historically spotless process; Publication/upload
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Proved: for every k >= 3 and t >= 0 there is a common bound N(k,t) such that every graph on at least N vertices whose f_k count is below that of the (t+1)-edge star plus isolated vertices is within at most t edge flips of a complete bipartite graph, empty parts allowed, or is so after complementing; f_k counts vertex-injective k-cycles in all cyclic orders with an odd number of edges present, not only contained cycles. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

For every integer k>=3 and t>=0, there is one N(k,t)>=t+2 such that every n>=N and every finite simple undirected graph G on n vertices with f_k(G)<f_k(the(t+1)-edge star plus isolated vertices on n vertices) has G or its WHOLE complement within at most t unordered-pair edge flips of a complete bipartite graph, allowing empty cut parts. Here f_k counts ambient injective k-vertex cyclic orderings modulo rotations and reversal with an odd number of present G-edges; it does not count only graph-contained cycles. Includes genuine quotient/counting, exact threshold, common N, k3/t0, complement and unordered edit bridges. False separate odd-n/even-k remark excluded.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER-v5.md. The complete Lean source is in mathdb-329202-proof-packet.zip.
