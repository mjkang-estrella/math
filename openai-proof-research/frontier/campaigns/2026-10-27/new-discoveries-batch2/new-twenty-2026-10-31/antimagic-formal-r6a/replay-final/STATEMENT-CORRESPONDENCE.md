# Statement correspondence

The literal source definitions remain unchanged in the 37 frozen modules:
Labeling is an edge equivalence to Fin |E| with labels shifted by +1;
weight sums incidence labels; IsLocal separates adjacent weights;
colorCount counts their image; spectrum and chiLA express the minimum.
The finite row-index tree, its structural proof, leaf count and lower bound
are inherited unchanged. The scope is even t >= 2 and depth n >= 1.

Antimagic.Round6A.nonbinaryWeightCompletion has exactly the inherited
Round5A.NonbinaryWeightCompletion statement. Its labeling is the same frozen
higherLabeling, without changing the formula, graph or incidence weights.
nonbinaryHigherConstruction discharges Round3.NonbinaryHigherConstruction
for every even t >= 4 and n >= 3, with formula agreement included.

The binary helper results do not discharge Round3.BinaryHigherConstruction.
Their conditional incidence formulas explicitly require a realization of the
inherited label formula. The exact remaining Prop definitions are unchanged:
Round3.BinaryHigherConstruction in AntimagicFinal3.lean and ModelBridge in
AntimagicModel.lean. No new axioms or placeholders are introduced.

Antimagic.Round6A.even_case is conditional only on BinaryHigherConstruction;
mathdb_354228 additionally assumes ModelBridge and concludes IsLeast plus
the literal chiLA equality for any FullTree. These are partial endpoints,
not unconditional proofs of MathDB 354228. No acceptance or novelty claim.
