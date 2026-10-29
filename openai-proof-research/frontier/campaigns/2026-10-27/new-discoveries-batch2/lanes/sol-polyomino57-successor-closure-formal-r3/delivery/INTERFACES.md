Namespace `Polyomino57`; exact types and actual-origin inventories are in the extracted verification directory.

* `LocallyClosed A B`: for every literal row in `A.toList`, there exists a row-local choice function whose sorted successor checker succeeds. No shared lookup is evaluated.
* `locallyClosed_array`: converts that semantic certificate to the existing `arrayClosureCheck` interface using proof-level Classical choice. No untrusted Python choice, index, or translation is assumed true.
* `closure5`, `closure6`: closed existential array-closure certificates for `closedLayer5 → layer6`, `closedLayer6 → layer7`.
* `layer5_link`, `layer6_link`: kernel-decided literal array equality to existing size-five target and between the two new layers respectively.
* `sevenLayers_certified`: closed sequence certificate for all six transitions from singleton to size seven, reusing all four existing small closures.
* `seven_normalized_coverage P hP hc`: every connected integer-grid Finset of cardinality seven has the normalization of a nonempty row of `layer7`.
* `placement_of_normalized_row`: transfers an actual translated literal inclusion to a representative with equal normalization.
* `placement_of_tree_normalization`: the same transfer for any `TreeMember` of any `PlacementTree` with `treeCheck T = true`. This applies to each supplied checked forest, but does not supply the missing concrete row/forest correspondence.

No D4 quotient or rotation is used. The bridge is translation-only and works for negative coordinates and differently anchored rows. Neither a terminal-family count nor a Python-completeness premise appears in these theorems.
