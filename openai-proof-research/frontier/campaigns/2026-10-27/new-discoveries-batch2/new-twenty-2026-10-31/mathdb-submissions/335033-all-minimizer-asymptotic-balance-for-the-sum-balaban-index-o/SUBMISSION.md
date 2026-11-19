# MathDB 335033: All-minimizer asymptotic balance for the sum-Balaban index of dumbbells

- Problem: https://mathdb.com/p/335033
- Source: K; n; o; r; /; K; r; a; n; j; c; /; S; k; r; e; k; o; v; s; k; i; /; T; e; p; e; h; ,;  ; O; n;  ; t; h; e;  ; m; i; n; i; m; u; m;  ; v; a; l; u; e;  ; o; f;  ; s; u; m; -; B; a; l; a; b; a; n;  ; i; n; d; e; x; ,;  ; o; w; n; e; d;  ; a; r; X; i; v; 1; 7; 0; 1; .; 0; 2; 7; 1; 6; v; 1;  ; C; o; n; j; e; c; t; u; r; e; 1; 0;  ; p; r; i; n; t; e; d; p; 1; 1; .;  ; A; r; X; i; v;  ; s; t; a; m; p; 2; 0; 1; 7; -; 0; 1; -; 1; 0;  ; v; s;  ; i; n; t; e; r; n; a; l;  ; c; o; v; e; r; 2; 0; 2; 1; -; 0; 8; -; 2; 6;  ; p; r; e; s; e; r; v; e; d; ;;  ; n; o;  ; j; o; u; r; n; a; l; -; f; i; n; a; l;  ; e; q; u; i; v; a; l; e; n; c; e; .;  ; E; x; a; c; t;  ; p; r; o; o; f; -; e; m; p; t; y;  ; r; e; t; r; i; e; v; e; d;  ; M; a; t; h; D; B; 3; 3; 5; 0; 3; 3;  ; r; e; c; o; r; d;  ; b; o; u; n; d; .
- Outcome: **PROVED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `SumBalaban.source_target : SumBalaban.SourceTarget`, `ReviewIndependent.all_choices_expanded`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `PAPER-v1.md`, `SOURCE-APPENDIX-v4.md`
- Lean source: `mathdb-335033-proof-packet.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Bounded positive prior-method comparison and target-specific uniform next-order all-minimizer selection. Not a conclusion from open labels, finite experiments, formalization or absence of keyword matches. remaining_literature_limits: Closed2017journal-final and2016ordinary-Balaban predecessor bodies remain unread; no equivalence attested.; Owned arXiv stamp/internal cover dates differ; scoped identity preserved.; Dated catalogue fields and plausible predicates, not all manuscript proof bodies or worldwide priority.; Owned normalized retrieved target, not live canonical-page observation. not_claimed: Exact finite clique balance; Global optimum among all connected graphs; Worldwide priority guarantee; Historically spotless process; Publication or upload
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Proved: every eventually minimizing choice of the sum-Balaban dumbbells D(a,b,d), with a + b + d = n and a <= d, satisfies a/sqrt(n) and d/sqrt(n) tending to c = sqrt(sqrt(Q)), where Q = sqrt(2) log(1 + sqrt(2)), and b/n tending to 1, uniformly over all admissible competitors. This is asymptotic balance only: no exact finite balance or global minimum over all connected graphs is claimed. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

For every eventually minimizing choice of actual sum-Balaban-index dumbbells D(a,b,d), with positive integers a,b,d, a+b+d=n, a<=d, two disjoint cliques and a disjoint b-VERTEX path with EVERY clique vertex attached to its respective path endpoint, a/sqrt(n) and d/sqrt(n) tend to c=sqrt(sqrt(Q)), Q=sqrt(2)*log(1+sqrt(2)), and b/n tends to1. Includes actual graph distance/transmissions, real edge objective, all admissible competitors, attainment and all-minimizer uniformity. Not exact finite balance, not global minimum over all connected graphs.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER-v1.md. The complete Lean source is in mathdb-335033-proof-packet.zip.
