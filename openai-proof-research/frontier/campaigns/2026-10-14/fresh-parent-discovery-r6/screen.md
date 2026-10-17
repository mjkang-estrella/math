# Family 187: the strong-game race is an additional obligation

Status: pre-freeze screen, no nominee or count. Source theorem truth is stipulated at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The deductions here concern two particular paths, not the winning status of the full strong game. No independent substantiality or proof PASS is claimed.

## Exact source interface

The source *Snaky in 21 Maker moves* uses

S = {(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)}

and its translations and eight signed coordinate permutations. Maker moves first on the empty square lattice, with one previously unclaimed cell per turn. Breaker only blocks; completing a Breaker copy does not end the weak game. Theorem `thm:main` gives a single globally legal policy winning within 21 Maker moves. Corollary `cor:finite-board` confines it to the 251-cell envelope T727 inside [0,16]². These are credited source results, not new deductions.

A source card is a conditional weak win (A,T,h). At a Maker turn it requires A⊆M and B∩T=∅. A combination claims its pivot and, after the next reply, chooses a child whose envelope avoids that reply. The printed policy in `strategy.tex` chooses the first such child. The placed child envelope is contained in its parent. At a base, one last cell completes S.

The stronger question would ask for a first-player strategy when either player's completed copy ends the game immediately. There is no frozen target: no mechanism covering all replies has been obtained. A finite weak-win certificate does not itself verify the new race condition.

## Exact failure of the unchanged printed policy

Let Second's first six moves, in order, be

(100,100), (101,100), (102,100), (103,100), (103,101), (104,101).

They form S+(100,100). Every one lies outside T727, hence outside every nested active envelope. Under the printed first-surviving-child rule the first six Maker moves are

(8,8), (8,7), (8,9), (8,10), (8,11), (9,11).

The successive selected local references, before the last reply, are 648:043, 174:011, 116:102, 7:103, 6:001. Affine placements compose in the source order F∘G. All these pivots are fresh; the replacement rule is not invoked.

Maker cannot win before move six by cardinality. On move six its six-cell set has five collinear cells, whereas S and each congruent copy have no five collinear cells. It therefore still has no target. Second completes its translated S on reply six and wins the strong game. These are legal moves, with no overlap. This is a counterplay to the *specified printed policy*, not to the source theorem and not to every possible first-player strategy.

The original wrapper `trace_check.py` reconstructs those reference placements from the pinned source evaluator and separately detects targets by all eight orientations and all possible translations into the owned set. Its output is `trace-result.json`. Reconstruction is used to examine this new inference; it is not an upstream truth audit.

## Why that example does not exclude other certificate choices

After the same first four Maker moves, card116 also has the surviving child 115:240. Use that child instead of the printed first one. Then choose its first surviving child 5:403. The remaining two Maker claims are (7,7) and (7,6). The resulting six-cell set is exactly

{(8−y,10−x) : (x,y)∈S}.

Maker wins on its sixth move, before Second's sixth reply. The wrapper verifies this alternate reference path too. In fact this fixed path works whenever the first five Second replies all lie outside T727: nesting keeps every chosen envelope clean, and Second has fewer than six stones before Maker completes its copy. Thus the remote example cannot refute all child-selection policies. This observation is an elementary certificate consequence, not a substantial nomination.

## Closest primary operation and remaining gap

Boucher–Villemaire, *The QBF Cover encoding for Harary's Tic-Tac-Toe* (2025), §2.2 defines the strong game, and §§3.1–3.4 explicitly retain the opponent's race condition. Their fixed cover restricts First's moves. Opponent moves outside it are counted; for each target they require that its in-cover part not be fully opponent-owned whenever the counter is large enough to cover the remaining cells. Stopping variables freeze a First win before any later opponent win. This is already a sound conservative way to handle exterior moves, not a new operation from this screen. Their §4 explicitly distinguishes the weaker Maker–Breaker encoding and reports finite-board experiments; it supplies no strong Snaky strategy for the present full board. [Primary paper](https://caiac.pubpub.org/pub/km2g3t1j/release/1).

For the nested source cards, B∩T=∅ alone gives no control over a target outside T. Merely selecting a child with a small height, or inserting a defensive move in place of the prescribed pivot, has not been proved to preserve a strong winning strategy. In the latter case the next opponent reply may occupy the unpaid pivot, so the original combination induction cannot be invoked without an additional invariant. This states a missing proof obligation, not an impossibility theorem for a modified strategy.

The remaining task would require one legal policy covering every mixed local/exterior reply history, with opponent targets checked before every later Maker move. The two path calculations do not establish that. No manuscript, formalization or release follows from this screen.

## Reading, provenance, and limits

The complete preprint catalogue was inspected with `truncated=false`: this family has one manuscript with older 25/35-move routes in appendices and supporting certificate files. The 18 downloaded pinned inputs are listed in `source-receipt.json`; original hierarchy, Git blob and SHA256 identities are retained. Actual relevant reading: introduction, strategy, templates, certificate proof, geometry, paper wrapper and bibliography in full, plus route21 README and independent evaluator in full. The literal certificate is parsed for reconstruction, not manually read line by line. The 25/35-route appendices, formalization/verification narrative and other checker bodies were not fully read, and no claim depends on their proof details. No distinct companion theorem is inferred from the catalogue.

Closest primary: Boucher–Villemaire full §§2.2, 3.1–3.4 and 4 were read, including the actual winning clauses and justification, not merely the abstract. The PDF/text are retained privately and hash-bound by `primary-receipt.json`. Sieben's 2004 primary paper was inspected through its weak-game definition and dimension argument; it is not a premise here. Bounded searches of canonical iterations/proposals by Snaky/family187/Maker-moves found no developed-chain match, which is not exhaustive eligibility or worldwide novelty clearance. Broad search results were used only as leads.

Author: Myeongjin Kang, no affiliation. Original prose CC BY 4.0; original wrapper MIT. Private upstream and external files retain their original rights and provenance. The manifest authenticates identity only; mathematical scope is exactly the two paths and the deductions above.
