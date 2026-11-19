# MathDB 352193: Universal symmetries of rooted directed compass boards

- Problem: https://mathdb.com/p/352193
- Source: M; a; t; h; D; B; 3; 5; 2; 1; 9; 3;  ; e; x; a; c; t;  ; o; w; n; e; d;  ; r; e; t; r; i; e; v; e; d;  ; r; e; c; o; r; d;  ; u; n; d; e; r;  ; S; h; a; v; i; v; ,; B; o; a; r; d;  ; g; a; m; e; s; ,; r; a; n; d; o; m;  ; b; o; a; r; d; s;  ; a; n; d;  ; l; o; n; g;  ; b; o; a; r; d; s; ,; a; r; X; i; v; 2; 1; 1; 0; .; 0; 5; 4; 1; 6; v; 1; (; 1; 1; O; c; t; 2; 0; 2; 1; ); ,; D; e; f; i; n; i; t; i; o; n; s; 2; /; 1; 1; ,; s; e; c; t; i; o; n; 5; .; 1; /; C; o; n; j; e; c; t; u; r; e; 1; 5; .;  ; O; n; e; -; b; a; s; e; d;  ; t; o;  ; z; e; r; o; -; b; a; s; e; d;  ; c; o; o; r; d; i; n; a; t; e;  ; t; r; a; n; s; l; a; t; i; o; n;  ; p; r; e; s; e; r; v; e; s;  ; r; a; y; s;  ; a; n; d;  ; b; o; t; h;  ; r; o; o; t; s; .; 2; 0; 2; 3;  ; j; o; u; r; n; a; l; -; f; i; n; a; l;  ; b; o; d; y;  ; i; n; a; c; c; e; s; s; i; b; l; e;  ; a; n; d;  ; n; o; t;  ; a; s; s; e; r; t; e; d;  ; r; e; a; d; .
- Outcome: **PROVED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `BoardV1.source_group_endpoint`, `BoardV1.all_odd_source_groups`, `BoardV1.literal_endpoint`; axioms limited to Classical.choice, Quot.sound, propext.
- Written proof: `PAPER-v1.md`, `APPENDIX-v1.json`
- Lean source: `board-symmetry-accepted-proof-packet-20261115-v1.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Bounded SUBSTANTIAL: universal entry-variation to ray-profile rigidity and uniform compass/root classification supplies target-specific argument beyond the strongest developed routine additive-invariant contrary adaptation. No authenticated exact PUBLIC or complete older-method specialization within inspected bounded evidence. not_claimed: worldwide absence of prior proof; clean historical/current process; live canonical MathDB observation; uninspected closed journal proof identity; truth audit of trusted pinned upstream theorems
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Proved: the only universal symmetries of rooted directed compass boards of odd order n >= 3, with a prescribed root, are the identity and the reflection in the main diagonal. A board permutation with one global permutation of the eight directions is universal, meaning every board admits a doubly rooted isomorphism to its transformed image, possibly board-dependent, exactly in those two cases; centre outgoing arcs are retained. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

For every odd n>=3, retain all n^2 board positions and every positive-step directed compass ray arc, including center outgoing arcs. Both upper-left beginning and center roots fixed. For arbitrary position permutation sigma and one GLOBAL8-direction permutation tau, S(A)(v)=tau(A(sigma(v))). S is universal iff FOR EVERY board A THERE EXISTS a doubly rooted digraph isomorphism A to S(A), possibly depending on A and unrelated to sigma. The set of actual universal board permutations is exactly identity and physical main-diagonal reflection, as one global group/set equality.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER-v1.md. The complete Lean source is in board-symmetry-accepted-proof-packet-20261115-v1.zip.
