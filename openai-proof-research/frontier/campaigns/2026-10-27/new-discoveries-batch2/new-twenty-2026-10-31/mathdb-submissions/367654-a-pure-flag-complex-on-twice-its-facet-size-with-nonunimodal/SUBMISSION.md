# MathDB 367654: A pure flag complex on twice its facet size with nonunimodal face vector

- Problem: https://mathdb.com/p/367654
- Source: C; o; o; p; e; r; /; F; a; r; i; d; i; /; H; o; l; l; e; b; e; n; /; N; i; c; k; l; a; s; s; o; n; /; V; a; n; T; u; y; l; ,; S; p; h; e; r; e; s;  ; a; n; d;  ; b; a; l; l; s;  ; a; s;  ; i; n; d; e; p; e; n; d; e; n; c; e;  ; c; o; m; p; l; e; x; e; s; ,; a; r; X; i; v; 2; 5; 0; 3; .; 1; 8; 4; 9; 0; v; 1; (; 2; 4; M; a; r; c; h; 2; 0; 2; 5; ); ,; C; o; n; j; e; c; t; u; r; e; 1; .; 4; ;; e; x; a; c; t;  ; o; w; n; e; d;  ; n; o; r; m; a; l; i; z; e; d;  ; M; a; t; h; D; B; 3; 6; 7; 6; 5; 4;  ; b; i; n; d; i; n; g;  ; P; A; S; S; .
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `PureFlag.literal_broad_refutation`, `PureFlag.actual_missing_witness`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `PAPER-v1.md`, `LEAN-SOURCE-APPENDIX-v3.md`
- Lean source: `mathdb-367654-proof-packet.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Positive boundedsource-method/constructioncomparison and target-specific weightedtwo-branch/concentrationmechanism;not inferred from openlabel,formalization,nohits or universalabsence. Older directcone-padding doesnot supplytheactual counterexample asdocumented in contributionreview. remaining_literature_limits: Journalfinal and July2026prior closed/unread;no equivalence/content reconstructed.; Originalisolate-freegraphconjecture remainsunrefuted.; Boundedcataloguepredicatecomparison,notworldwidepriorityorallmanuscriptproofcoverage.; Ownednormalizedtargetsnapshot,notlivecanonicalpageobservation. not_claimed: Worldwidepriorityguarantee; Historicallyspotlessprocess; Publication/upload; Smallestorisolate-freecounterexample
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the literal broad form of Conjecture 1.4 of arXiv:2503.18490, on face vectors of pure flag complexes. A finite abstract pure flag complex on 540000 vertices, all of whose facets contain 270000 vertices, has a nonunimodal f-vector; the witness is the independence complex of an explicit graph with 210000 isolated vertices. The isolate-free variant remains unrefuted, and no minimal vertex count is claimed. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Refutation of the literal broad arXiv2503.18490v1 Conjecture1.4: a finite abstract pure flag complex on540000 actual vertices,all facets of cardinality270000(dimension269999),has nonunimodal f-vector counting nonempty faces by dimension. Witness is the independence complex of the explicit mixed-clique-join graph with210000 isolated graph vertices/cone vertices. Actual vertex,purity,flag,face-coefficient,moment/window and f-vector bridges included. The original isolate-free graph conjecture remains UNREFUTED; no finite vertex-count minimality claim.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER-v1.md. The complete Lean source is in mathdb-367654-proof-packet.zip.
