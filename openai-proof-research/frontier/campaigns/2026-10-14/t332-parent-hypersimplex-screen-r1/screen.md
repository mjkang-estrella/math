# Correlated hypersimplex rounding does not close T332's tree constraint

Myeongjin Kang, no affiliation. Original prose CC BY4.0. This is a parent-side literature/interface screen for the unchanged T332 target, not a theorem nomination or an independent gate. Count13/20 is unchanged.

The earlier analyticr41 reading ledger located arXiv2511.13573 but read only its abstract. This round acquired the versioned primary body and inspected the operative statements and algorithm interface. [Naor–Raju–Shetty–Srinivasan–Valieva–Wajc, Dimension-Free Correlated Sampling for the Hypersimplex](https://arxiv.org/abs/2511.13573v1), Definition1.1/Theorem1.2, round vectors in [0,1]^n with coordinate sum at most k to sets, preserving coordinate marginals and the rounded total cardinality, with expected unweighted symmetric difference O(log k) times input ell1 distance. The k=1 simplex result is constant. AppendixC applies independent copies to disjoint parts; its proof concerns submodular dominance. The main algorithm hashes and compresses coordinates; it does not take a rooted label-tree path constraint as input. Its computational sampling tree is not such a constraint. The stated metric multi-labeling application uses this set-valued interface.

## Exact missing geometric condition

For the finite tree-flow route in analyticr41/finite-analysis.md, every realized edge indicator must be a root-to-vertex path. Parent containment and sibling disjointness are needed pointwise, not only in expectation. Matching every edge marginal and total path length does not imply those conditions.

Take a unit stem e0 followed by two children e1,e2, each with two leaf edges e3,e4 and e5,e6, respectively. The probability uniform on the four leaves has flow

    q=(1,1/2,1/2,1/4,1/4,1/4,1/4).

Its coordinate sum is3. The following random three-element subsets preserve every coordinate marginal exactly:

    {e0,e1,e2} with probability1/2,
    {e0,e3,e4} with probability1/4,
    {e0,e5,e6} with probability1/4.

None is a path. The first has two sibling edges; the other two have leaf edges without their parents. This is an elementary witness that cardinality and marginals alone do not imply feasibility. It is NOT a claim that this distribution is the primary algorithm's actual output, nor a counterexample to all its global guarantees.

Even imposing one edge at every level through a partition matroid does not fix consistency. Apply AppendixC's independent-part operation to the level sets {e0}, {e1,e2}, {e3,e4,e5,e6}, with capacity1 on each. Marginal preservation and exact cardinality force a uniform child and a uniform leaf; independence across the two parts makes them genealogically consistent with probability exactly1/2. The other half are not paths. This diagnoses this particular use of the stated partition operation, not every possible coordinated rounding method.

There is also no uniform constant from directly setting k equal to the number of edges in a longest rooted path: tree depth is unrestricted in T332. Reducing to vertex masses with k=1 instead changes the controlled input metric from weighted cut-flow distance to total variation. On an interval rooted at0, delta_a and delta_b have W1=|a-b| but vertex-coordinate ell1 distance2; their ratio is unbounded as b approaches a. No tree-geometric cost estimate follows just from the unweighted simplex guarantee. These observations do not exclude a new weighted, path-consistent adaptation of the primary machinery.

## Status and limits

This closes only the previously unread primary lead as a direct theorem import. No universal coupling, cone retraction, cotype estimate, or counterexample to the unchanged T332 theorem is obtained. Approximate marginals or bounded-depth replacements would not meet the frozen scope. The substantive required estimate remains analyticr42/constrained-optimization.md equation(8), or another full-scope construction.

Actual primary text reading this round: extracted lines50–220 (definitions, main theorem and surrounding interface),270–410 (hash/compress algorithms and cardinality/marginal proofs),750–790 (metric multi-labeling interface),880–925 (end of approximate-marginal discussion and open questions),1776–1835 (partition-matroid construction and LemmaC.1 proof). The intervening global stretch proof, deferred AppendixA estimates, AppendixB proofs and most applications were not read. No new claim rests on those unread proofs; the screen compares stated outputs and re-derives the two finite consistency examples. No worldwide novelty conclusion or theorem audit.

The pinned source is not freshly acquired or audited here. Read earlier authored r41 finite-analysis/reading limits, r42 constrained-optimization, path-and-branching, positive-normalization and parent-global-check, plus parent joint-probe and fixed-p obstruction notes. Several initial web searches returned familiar source-isometry and random-projection leads, not usable new positivity theorems. An attempted arXiv1908.01388v5 HTML URL returned404; existing r41 already records operative v2 readings, and no new result from it was imported. Third-party PDF/text stay private; primary-receipt.json records their exact identities. Hashes are not mathematical proof.
