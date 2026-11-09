# Full generic cubic criterion

`formal/GenericCubic.lean` imports the unchanged frozen `StrengthenedScalar.lean` (SHA256 d13d8acacabf3edc1866be81ebdab0fed6565b18692864204aec10c9c26b1cf2).

Main theorem: `StrengthenedTaxicab.generic_cubic`.
For A,B,C,u,v,w≥0, all six opposite-side caps u≤B,C;v≤A,C;w≤A,B, and ABC−Avw−Buw−Cuv−2uvw≥0, it proves

    3(u+v+w+min(u,v,w)) ≤ 2(A+B+C).

No division, positive-length assumption, ordering assumption, or barycentric weights appear in its statement. The proof reuses the threshold lemma and cubic offset identity, whose positive δ³ gives the strict contradiction even when some A,B,C vanish, then handles all six simultaneous permutations of paired variables. The two new declarations are the sorted helper and arbitrary-order main theorem.

Module SHA256 e8c765a0183a77d1b7bc10850a87d78eda48c09e278e827ffea7e17c4a86da7d. Both declarations freshly replayed with Lean4.34.1, warning-as-error, only propext/Classical.choice/Quot.sound. Receipt: `build/fresh-audit-chysrhls/receipt.json`. Reproduce with `python3 audit_generic.py`.

This closes the literal scope of the paper's generic polynomial lemma. It is part of the same strengthening, with no additional discovery count.
