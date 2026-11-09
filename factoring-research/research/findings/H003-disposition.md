# H003 disposition: close explicit residue enumeration

Verified factoring complexity improvement: **NONE**. The independent review
accepts the local cardinality formula, its CRT product, and the uniform
`M^(1-o(1))` output-size derivation. This applies to writing the whole allowed
residue set; it is not a lower bound on factoring or implicit interval queries.

The proposed two-list bypass is already present in Hittmeir's factor-sum work.
For its balanced, non-close coverage regime, explicit half-lists cost at least
`N^(1/4-o(1))`, losing to the checked deterministic `N^(1/5+o(1))` baseline.
Do not implement that continuation as a disruptive candidate.

Evidence: [frozen diagnostic](../experiments/H003/result.json),
[derivation](H003-cardinality-draft.md), and
[independent review](H003-independent-review.md). The diagnostic source hash
was rechecked after review and matches. The reviewer independently checked the
original numerical claims; additional exploratory checks are described in its
report and are not performance evidence.

Reopen only for a specified implicit query/product primitive with complete
construction, query, reporting, extraction and bit costs. A different data
structure's compact description alone does not meet that requirement.

