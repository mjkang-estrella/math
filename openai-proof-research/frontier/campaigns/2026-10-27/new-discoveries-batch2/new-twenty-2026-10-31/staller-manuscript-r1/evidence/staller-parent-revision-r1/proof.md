# MathDB355140: seven-vertex counterexample, pending independent review

Let G have vertices 0,…,6 and edges 01,05,12,16,23,34,45,56. This is a simple connected bipartite graph (a theta graph with path lengths2,2,4). Its degrees are2,3,2,2,2,3,2, so its minimum degree is2. No bipartite or connected restriction is needed by the target.

Its closed neighborhoods, in vertex order, are
{0,1,5}, {0,1,2,6}, {1,2,3}, {2,3,4}, {3,4,5}, {0,4,5,6}, {1,5,6}.
Staller wins when her claimed vertices contain one of these sets. Dominator wins when his claimed vertices meet every such set: this is exactly the condition that his vertices dominate G. Players alternate legal unclaimed vertices, Staller first.

The claim is that the optimal number of Staller moves is4. An explicit upper-bound strategy is the complete JSON tree in strategy.log (after its initial diagnostic line). Its root move is3. Each S node specifies a single legal choice; every D node lists every remaining legal choice and its continuation. All26 leaves list an occupied closed neighborhood, after at most4 Staller moves. This tree has70 nodes. The independent exact-set verifier ordinary-proof.py checks legal choices, full response coverage, the winning neighborhood at every leaf and the four-move budget. Thus induction up this finite tree proves the upper bound. The tree is small enough to inspect directly; the verifier is a reproducible convenience, not an assumed mathematical oracle.

For the lower bound, the following table gives Dominator's first response to each first Staller move. The third column maps every legal second Staller move to Dominator's second response.

| S1 | D1 | S2 : D2 |
|---|---|---|
|0|1|2:3,3:2,4:2,5:2,6:2|
|1|0|2:3,3:2,4:2,5:6,6:5|
|2|1|0:3,3:4,4:3,5:0,6:0|
|3|2|0:1,1:0,4:5,5:4,6:0|
|4|2|0:1,1:0,3:5,5:3,6:0|
|5|0|1:6,2:1,3:4,4:3,6:1|
|6|0|1:5,2:1,3:1,4:1,5:1|

Every listed response is legal. For each of these35 positions, adding any legal third Staller vertex to her two vertices contains none of the seven closed neighborhoods listed above. This is a direct finite set-inclusion check (also performed by ordinary-proof.py). Winning before three moves is impossible since every closed neighborhood has at least three vertices. Hence no strategy wins within three moves. Together the upper and lower bounds prove gamma'_SMB(G)=4.

Conjecture7.2(i) in the cited preprint and published paper demands at most ceil(7/2)-2+1=3 moves whenever the winning number is finite. The actual value4 refutes that clause, and hence the conjunction requested by MathDB355140. No separate resolution of clause(ii), smallest-counterexample assertion, or family variant is claimed.

## Literal Lean semantics

Game.lean uses an inductive finite strategy tree Wins, not a surrogate graph property: done requires ownership of an actual closed neighborhood; staller chooses a legal remaining vertex and spends one unit of her move budget; dominator branches over every remaining legal vertex. Unclaimed vertices are erased on either move. From the initial empty occupation and full board these rules maintain disjoint occupations and forbid repeated moves. A finite strategy tree is exactly a strategy guaranteeing the specified win against every legal opposing strategy; every play lasts at most seven total moves. terminal_incompatibility and Wins.not_after_dominator prove that ignoring further play after a Dominator win cannot introduce a false Staller win.

The separate recursive checker is proved equivalent to Wins for every finite graph, board, occupation, turn and budget by induction on the number of unclaimed vertices. It is then evaluated by kernel decide, not native_decide. Budget monotonicity, the least finite winning number in WithTop Nat, exact minimum degree, exact winning number4, and negation of the literal source conjunction are all proved. SourceClaim writes bounds additively as b+delta<=ceil(n/2)+1 (and the floor version), avoiding truncated natural subtraction. Existence of any finite winning budget is equivalent to finiteness of the minimum; monotonicity makes the budget formulation equivalent to the usual minimum-number assertion.

The two endpoints are MathDB355140.winning_number_four and MathDB355140.source_refutation. All63 local declarations, including generated recursors, equation lemmas and instances, pass the in-source safety/axiom audit. Generated check._unsafe_rec has unsafe flag false; the audit checks the flag, not spelling. A fresh extracted strict warningAsError replay succeeds. Only propext, Classical.choice, Quot.sound occur transitively. External package oleans are trusted; no full upstream rebuild is claimed.

## Source and prior-art limits

Primary source: Bujtas–Dokyeesun, arXiv2206.12812v1, standard definitions, Section1.2 winning numbers and Section7 Proposition7.1/Conjecture7.2; published Discrete Applied Mathematics344(2024)10–22, DOI10.1016/j.dam.2023.11.015, lawful institutional PDF sources/game-published.pdf. The final published definition and conjecture, as well as the adjacent sharpness construction/proof, were inspected. Exact URL/status/hash receipts are in source-receipts.json and more-source-receipts.json. Search-engine snippets incorrectly rendered a ceiling in clause(ii); the downloaded primary published body has the floor. This does not affect the clause(i) counterexample.

Bounded title/author/conjecture searches and refreshed public registry path inventories found no matching settlement for355140. That is not clearance of all proof bodies, deletions, solution APIs, specialist literature or priority. MathDB/Palomar inherited403 remains a limitation. Independent significance and novelty reviews and root acceptance have not occurred. This packet earns zero credit by itself.
