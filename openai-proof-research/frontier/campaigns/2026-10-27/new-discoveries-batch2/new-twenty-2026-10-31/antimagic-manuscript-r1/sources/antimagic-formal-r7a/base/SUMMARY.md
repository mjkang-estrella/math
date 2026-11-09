# Round 6A — partial, not acceptance

The first target is CLOSED, without a construction hypothesis:
Antimagic.Round6A.nonbinaryWeightCompletion proves the exact inherited
Round5A.NonbinaryWeightCompletion, and nonbinaryHigherConstruction proves
Round3.NonbinaryHigherConstruction. For every even t >= 4 and n >= 3, the
frozen literal labeling is proper and has exactly t^n + 1 colours.

The second target remains OPEN. Checked binary progress includes the row patch
permutation and bound; all internal-label injectivity and coverage; explicit
row-two labels; the root and first-row incidence weights for any realization
of the frozen formula; and root separation. A general binary literal labeling,
leaf permutation, remaining properness and colour count are still needed.
No BinaryHigherConstruction theorem is claimed.

AntimagicFinal6A.even_case assumes only BinaryHigherConstruction.
AntimagicFinal6A.mathdb_354228 assumes only BinaryHigherConstruction and
ModelBridge. No merged unconditional endpoint is supplied, since the second
construction target remains open. Round 4B files were not copied or imported.

All 37 frozen round-5A modules remain byte-identical. The source-only archive
contains 45 Lean modules and lane-local reproducibility scripts. See results.json
and replay-final for the fresh strict serial rebuild, every explicit leanchecker
call, full declaration audit and numerical checks. Only propext,
Classical.choice and Quot.sound occur as axioms. Root decides acceptance;
no credit is claimed.
