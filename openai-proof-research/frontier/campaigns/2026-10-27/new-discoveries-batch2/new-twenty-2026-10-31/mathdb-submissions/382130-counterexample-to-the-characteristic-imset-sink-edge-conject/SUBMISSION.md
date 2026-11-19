# MathDB 382130: Counterexample to the characteristic-imset sink-edge conjecture

- Problem: https://mathdb.com/p/382130
- Source: R; e; s; t; a; d; h; ,;  ; D; i; a; m; e; t; e; r; s;  ; o; f;  ; t; h; e;  ; C; h; a; r; a; c; t; e; r; i; s; t; i; c;  ; I; m; s; e; t;  ; P; o; l; y; t; o; p; e; s; ,;  ; a; r; X; i; v; 2; 3; 0; 2; .; 0; 3; 6; 4; 7; v; 2;  ; (; 6; M; a; r; c; h; 2; 0; 2; 3; ); ,;  ; C; o; n; j; e; c; t; u; r; e; 1; ;;  ; e; x; a; c; t;  ; r; e; t; r; i; e; v; e; d;  ; n; o; r; m; a; l; i; z; e; d;  ; M; a; t; h; D; B; 3; 8; 2; 1; 3; 0;  ; b; i; n; d; i; n; g;  ; i; n; d; e; p; e; n; d; e; n; t; l; y;  ; P; A; S; S; .
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `ImsetSink.source_negation : ¬ ImsetSink.UniversalSinkEdge`, `ImsetSink.explicit_five_counterexample`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `PAPER-v1.md`, `LEAN-SOURCE-APPENDIX-v1.md`
- Lean source: `mathdb-382130-proof-packet.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Positive bounded primary-method and source-result comparison; explicit sink-pair midpoint obstruction classified substantive. Not newness inferred from formalization, empty solution list, absent vocabulary or worldwide absence. remaining_literature_limits: Restadh journal final; KTH thesis/classification lead; distinct EJS2518 work; Full current lean/reasoning-trace subtrees and manuscript theorem bodies; prior root catalogue text not supplied. No claim of complete repository semantic coverage. This task made no new request, searched no registry mirror, and read no manuscript theorem/proof bodies. No claim that absent vocabulary alone proves novelty; candidate result predicates were compared personally. New public statements outside this catalogue and later updates remain uncovered.; Journal-final fidelity not asserted; exact ownedv2 target fidelity passed. not_claimed: Worldwide priority guarantee; Historically spotless process; Publication/upload; Minimality of the five-vertex witness; Truth audit of pinned upstream theorems
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the characteristic-imset sink-edge conjecture, Conjecture 1 of the source. A five-vertex skeleton, an acyclic orientation, and a vertex whose sink orientation is not Markov equivalent to it provide a segment between characteristic imsets that is an edge of no face, indeed not a face, of the convex hull over all acyclic orientations; all 26 subset coordinates and genuine d-separation are used. No general diameter bound is refuted. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Refutation of arXiv2302.03647v2 Conjecture1: there is a five-vertex skeleton G, an acyclic orientation C and vertex4 whose sink orientation D is not Markov equivalent to C, while the segment between their characteristic imsets is not an edge (indeed not a face) of the convex hull of characteristic imsets of ALL acyclic orientations of G. All26 subset coordinates, genuine d-separation, actual sink operation and real convex-face bridge included. No general diameter-bound refutation or minimality claim.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER-v1.md. The complete Lean source is in mathdb-382130-proof-packet.zip.
