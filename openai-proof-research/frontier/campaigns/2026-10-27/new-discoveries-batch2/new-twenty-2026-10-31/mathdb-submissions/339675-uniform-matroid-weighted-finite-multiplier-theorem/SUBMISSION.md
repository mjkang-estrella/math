# MathDB 339675: Uniform-matroid weighted finite multiplier theorem

- Problem: https://mathdb.com/p/339675
- Source: M; a; t; h; D; B; 3; 3; 9; 6; 7; 5;  ; e; x; a; c; t;  ; p; r; o; o; f; -; e; m; p; t; y;  ; o; w; n; e; d;  ; r; e; t; r; i; e; v; e; d;  ; r; e; c; o; r; d; ,;  ; i; n; t; e; r; p; r; e; t; e; d;  ; w; i; t; h;  ; p; o; s; i; t; i; v; e;  ; m; ,; d;  ; a; n; d;  ; t; h; e;  ; b; i; n; o; m; i; a; l; l; y;  ; w; e; i; g; h; t; e; d;  ; f; i; n; i; t; e;  ; c; r; i; t; e; r; i; o; n;  ; f; r; o; m;  ; G; a; o; /; L; u; /; X; i; e; /; Y; a; n; g; /; Z; h; a; n; g;  ; a; r; X; i; v; 1; 8; 0; 6; .; 1; 0; 8; 5; 2; v; 1;  ; a; n; d;  ; o; w; n; e; d; 2; 0; 2; 1;  ; a; s; s; o; c; i; a; t; e; d;  ; b; o; d; y; ,; E; q; 3; .; 3; /; C; o; n; j; 3; .; 3; .;  ; N; o;  ; l; i; v; e;  ; M; a; t; h; D; B; /; j; o; u; r; n; a; l; -; f; i; n; a; l;  ; i; d; e; n; t; i; t; y;  ; c; l; a; i; m; .
- Outcome: **PROVED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `MathDB339675.source_target : MathDB339675.SourceTarget`, `MathDB339675.source_target_literal`; axioms limited to Classical.choice, Quot.sound, propext.
- Written proof: `PAPER-source-v1.md`, `LEAN-APPENDIX-v1.json`
- Lean source: `uniform-matroid-weighted-symbol-accepted-proof-packet-20261115-v1.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Bounded SUBSTANTIAL: quadratic-lattice evaluations, paired interpolation and threshold/equality root count supply the additional source-specific proof beyond inspected classical finite-multiplier methods. No prior full specialization or exact public resolution authenticated within documented evidence. not_claimed: worldwide absence of prior proof; clean historical/current process; live canonical MathDB observation; uninspected closed journal proof identity; truth audit of trusted pinned upstream theorems
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Proved: the uniform-matroid finite multiplier conjecture of Gao, Lu, Xie, Yang and Zhang, on the d-sequence in the Kazhdan-Lusztig polynomials of uniform matroids. For all m, d >= 1 the explicit coefficient sequence b_i, given in closed form by falling factorials, acts diagonally on real polynomials of degree at most d and preserves zero-or-splitting: the image is zero or has only real zeros, with no extra hypotheses. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

For every positive natural m,d, the source sequence b_i = sum(h=0..m-1) ((i*(h-m+1)+m)/((h+1)*m))*fallingChoose(i-1+h,h)*fallingChoose(d-i+h,h) (all subtraction and falling products in R) acts diagonally on real polynomials of degree<=d, preserving zero-or-splitting over R. Weighted symbol is sum(i=0..d) choose(d,i)*b_i*t^i. Includes arbitrary root signs,multiplicities,lower degree,constants and zero input. No m=0,negative-parameter,unweighted-symbol or unrelated Z/gamma assertion.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER-source-v1.md. The complete Lean source is in uniform-matroid-weighted-symbol-accepted-proof-packet-20261115-v1.zip.
