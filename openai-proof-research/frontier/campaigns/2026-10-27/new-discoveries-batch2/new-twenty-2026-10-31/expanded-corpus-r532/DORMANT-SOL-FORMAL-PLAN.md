# DORMANT FORMAL PLAN: MathDB 344875 (no dispatch)

This plan is dormant. Nothing here was executed, no Lean was run in this lane, and no formal lane is requested. The inherited file name says SOL; the plan is model-neutral. Whether to dispatch is root's decision and depends on the significance question in FULLCANDIDATE.md section 6.

## Literal endpoint

The printed claim is universal over k >= 4, so its negation needs one k. The cheapest literal endpoint is k = 4:

  not Tendsto (fun n => (chiL (palm n 4) : Real) / ((3/2) * (4 * n : Real)^(1/4 : Real))) atTop (nhds 1)

Definitions needed, with no simplification of the source's objects:
* palm n k : SimpleGraph on Option (Fin n x Fin k), or an equivalent explicit type: hub none; hub adjacent to (i,0); (i,j) adjacent to (i,j+1).
* a locating coloring: c : V -> Fin p, surjective, proper (Adj u v -> c u != c v), with injective code v |-> (fun t => distance from v to c^{-1}(t)), where distance is the infimum of SimpleGraph.dist over the class.
* chiL G := sInf {p | exists a locating p-coloring}.
Bridges to record: proper plus nonempty classes as the reading of the source's "k-coloring"; o(1) as n -> infinity with k fixed.

## Proof route for the k=4 endpoint (only the Lemma 3 half is needed)

The negation needs only the upper bound along one subsequence, so Lemmas 1 and 2 are NOT required.
1. Fix b >= 2 and N_b = (b(b-1))^2. Arms are indexed by quadruples (x1,x2,x3,x4), x1 != x2 in Fin b, x3 != x4 in Fin b. Use the full family, which removes the coverage/selection step.
2. Spider distance lemmas: dist(hub,(i,j)) = j+1 (0-indexed j); same-arm distance is |j-j'|; different-arm distance is j+j'+2. Prove with an explicit walk for the upper bound and a depth/arm potential that is 1-Lipschitz for the lower bound.
3. Colors: Fin (2b+1), hub color 0, block one colors 1..b, block two colors b+1..2b. Show properness and surjectivity.
4. Code computation from Lemma 3 specialised to k=4; injectivity by reading the hub coordinate and then each block's two small values, using that |j-s| != |j-s-1|.
5. Conclude chiL (palm N_b 4) <= 2b+1.
6. Real analysis: (2b+1) / ((3/2) * (4 N_b)^(1/4)) = (2b+1) / ((3/2) sqrt 2 sqrt(b(b-1))) tends to 2 sqrt 2 / 3 < 1, and N_b -> infinity; a Tendsto to 1 along n would contradict this. Eventually the ratio is below 19/20, which can be proved by clearing the fourth root.

## Estimated cost

Finite graph and spider-distance infrastructure dominates, likely several hundred lines. Use specific imports (SimpleGraph metric, Finset, Real.rpow, Filter limits), not `import Mathlib`. This is finite and cheap by the campaign's standard, and needs no measure theory or asymptotic analysis beyond one elementary limit.

## Full theorem (optional, not needed for the literal)

Lemmas 1 and 2 and all k would add: the general distance-to-class formula, the data-to-code factorization and pigeonhole, AM-GM (Mathlib's inner_le_nnorm or Real.inner_le_Lp forms, or a direct weighted form), and the two parity profiles. Roughly double the cost. Worth doing only if credit is to attach to the all-k theorem, which section 6 of FULLCANDIDATE.md recommends as the only sensible unit.

## Permitted axioms and gates if dispatched

Only propext, Classical.choice, Quot.sound; no sorry, admit, native_decide or added axioms. Independent fidelity, significance and body audit, a fresh source-only replay, a paper and root final adjudication would all remain unpaid.
