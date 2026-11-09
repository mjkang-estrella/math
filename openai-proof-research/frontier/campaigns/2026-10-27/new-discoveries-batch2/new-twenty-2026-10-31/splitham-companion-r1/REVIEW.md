# Focused prior-construction comparison: MathDB 373598

**Gate C verdict: SUBSUMED. Recommend EXCLUDE under the campaign’s routine-adaptation rule.** This is a focused comparison, not acceptance; zero credit is asserted and root decides. The companion’s displayed graphs themselves miss Conjecture 6.1’s order bound, but they already have exactly the balanced independent-set obstruction. A short explicit regular sparsification of larger members yields the held candidate and an infinite counterexample family. The earlier argument that the displayed order is only 2r is therefore insufficient to clear the novelty gate.

## Evidence and source limits

Liu, Song, Zhan and Lai, *On hamiltonian properties of K₁,r-free split graphs*, Discrete Mathematics 346 (2023) 113402, DOI [10.1016/j.disc.2023.113402](https://doi.org/10.1016/j.disc.2023.113402), Section 5, pages 7–8, gives this construction:

Take H = K_{s−1,s}, with parts X = {x₁,…,x_{s−1}} and Y = {y₁,…,y_s}. Add a new vertex w and make Y ∪ {w} a clique K_{s+1}. The graph is the union of these two graphs. The text states s-connectivity, K₁,s+1-freeness, and failure of a Hamilton path with endpoints y₁,y_s. Its short exact wording is “there is no hamiltonian (y1, yr)-path” (the paper uses r where this report uses s).

The complete construction law is reliably exposed by indexed primary text of page 7 and its continuation on page 8, saved in [logs/search6.json](logs/search6.json) and [logs/search4.json](logs/search4.json). A normalized description and provenance are in [outputs/companion-construction.txt](outputs/companion-construction.txt). The source is the [author-hosted PDF](https://math.wvu.edu/~hlai2/Pdf/Hong-Jian_Lai_Pdf/318_DM_2023.pdf). **The full PDF body was not downloaded or read.** This is reliable construction-description evidence, not a claimed full-body clearance. In particular, I do not claim the authors printed the later sparsification.

The single allowed retry used a 125-second total timeout and a 35-second connection timeout; connection timed out after 35 seconds, before an HTTP response. No second retry or alternate PDF-host retry was made. One WVU publication-list fetch also timed out. Song’s author page and Zhan’s institutional publication page were readable, but offered publisher/EBSCO links rather than another open manuscript. No such restricted link was followed. A lawful arXiv HTML search for Song, Zhan, Liu and split returned only an unrelated quantum-computing paper. Repository and author-title searches located no separate open version. The route inventory is [logs/author-pages-and-search-scope.md](logs/author-pages-and-search-scope.md); exact HTTP receipts for the new OpenAlex and arXiv requests are in [outputs/http-receipts.json](outputs/http-receipts.json). Search receipts retain queries, source URLs and returned indexed text. No denied endpoint was directly fetched, no access denial/challenge retried, and TLS verification stayed enabled.

## The normalization that changes the comparison

In the displayed maximum-clique partition, Y ∪ {w} has size s+1 and X has size s−1. This can misleadingly look unlike a balanced candidate. However, w has no neighbours in X. Consequently, **Y is a clique and X ∪ {w} is an independent set of the same size s**, with every cross edge present. The displayed family is precisely

F_s = K_s ∨ independent(s), for s ≥ 3.

Thus all the independent vertices, including w, are false twins. A Hamilton path with endpoints in Y has only s−1 gaps between its s clique vertices, but must accommodate s independent vertices internally. No such path exists. This is exactly the candidate’s obstruction; taking the maximum clique in the prior paper merely hides the balanced partition.

The literal family is not already a counterexample to Conjecture 6.1. Its connectivity is s and order is 2s. With the conjecture parameter r=s it misses 2r+7 by seven. With r<s, any clique vertex and r+1 independent neighbours induce K₁,r+1. With r>s it is not r-connected. It does satisfy the extra K₁,s+1+e exclusion at its natural parameter. Therefore the extra forbidden graph is **not** what excludes this printed family; the order condition is sufficient to exclude it. This is a mathematical fact about the example, not evidence of authorial intent.

## Explicit routine bridge to the held family

Start with F_m, identify each side with Z_m, and retain only cross edges i—j with j−i in an r-element set D. Leave all clique edges intact. This deletes the other m−r cyclic perfect matchings from the complete cross block. It retains exactly the known balanced obstruction and creates exactly the cyclic graphs in the independent review, up to its noted simultaneous sign relabeling.

There is no search needed for the infinite family. For every r ≥ 6 take m=r+4 and, for example, D={0,…,r−1}. Equivalently, delete four cyclic perfect matchings from F_{r+4}. Then:

1. Every cross degree on both sides is r. After deleting fewer than r vertices the remaining clique is nonempty and connected, and every remaining independent vertex has a surviving clique neighbour. Deleting the r neighbours of an independent vertex isolates it. Connectivity is exactly r.
2. Two clique vertices have at least 2r−m=r−4 ≥ 2 common independent neighbours. An independent centre has degree r, so cannot centre either forbidden graph. For a clique centre, consider r+1 proposed leaves. With no clique leaves there are too few independent neighbours. With one clique leaf all r independent leaves are present, and the intersection bound supplies at least two leaf edges. With two clique leaves there are r−1 independent leaves; each clique leaf has at least one neighbour among them, in addition to their mutual clique edge. With at least three clique leaves there are already at least three leaf edges. Neither zero nor exactly one leaf edge is possible. Both induced forbidden graphs are absent.
3. Order is 2r+8 ≥ 2r+7. The balanced gap argument still forbids a Hamilton path between any two clique vertices.

This is a fixed four-matching deletion after enlarging the known complete balanced family, with an elementary intersection lower bound. Alternatively enlarge F_r by four vertices on each side to obtain F_{r+4}, then delete those matchings. It is a short augmentation-and-sparsification operation, not a new obstruction or a newly discovered structural ingredient. More generally m ≤ 2r−2 gives the same automatic intersection bound.

The exact held witness is F₉ with the four matchings at offsets {4,6,7,8} deleted, retaining {0,1,2,3,5}; it has r=5, order 18. The reviewed m=10 and m=11 examples similarly retain {0,1,2,3,6} and {0,1,2,4,7}. The r=5 offset choices need an intersection check rather than the automatic density bound. That distinction does not clear this candidate as a separate significant result: it is a small parameter/design variant of the same regular sparsification, and the r≥6 subfamily already refutes the full universal conjecture by the routine operation above. This is the reason for SUBSUMED, rather than merely observing that every graph embeds in a complete split supergraph.

This verdict does not assert a previously published refutation of Conjecture 6.1, nor bibliographic identity of the final cyclic edge list. It applies the campaign’s exclusion of routine adaptations of known constructions. Root retains the significance decision.

## Independent finite checks

Own isolated code [scripts/compare.py](scripts/compare.py) reconstructs the literal X,Y,w union and verifies its exact equality with F_s for s=3,…,8. For each it exhaustively checks every centre and every s+1-neighbour subset for zero or one leaf edge, and every vertex deletion of size below s. For s=3,4,5 an unpruned subset Hamilton-path DP from a clique vertex has exactly the independent vertices as full-mask endpoints.

The same code exhaustively checks forbidden induced configurations in five sparsifications: (r,m)=(5,9),(5,10),(5,11),(6,10),(7,12). Each has minimum pairwise clique-neighbourhood intersection 2 and no forbidden configuration. At (5,9), 15,444 centre/leaf sets were checked, as well as all 4,048 cuts of size below 5. At (6,10), the corresponding numbers are 64,350 and 21,700. The three r=5 examples delete 36, 50 and 66 cross edges respectively; the (6,10) example deletes 40. Finite results are [outputs/comparison.json](outputs/comparison.json); [logs/comparison.log](logs/comparison.log) records successful completion in about 1.17 seconds with peak group RSS 12,708 KiB. The general argument above, not finite enumeration, establishes all r≥6.

## Target text and awareness

[outputs/target-excerpts.txt](outputs/target-excerpts.txt) quotes every passage citing companion [12], plus the named-author attribution, with exact line references to the hash-bound `../splitham-review-r1/outputs/source-text.txt`. These are lines 64–69, 98–105, 108–116, 143–146, 167–172, 182–184, 324–329 and 818–819. Conjecture 6.1 and its motivation are at 783–786. In particular lines 98–100 state exactly:

> There exists an infinite family of
> r-connected K_{1,r+1}-free split graphs, each of which is not
> Hamilton-connected [12].

The target is therefore explicitly aware of the companion family. Lines 143–146 require a maximum clique for its working split partition; that convention explains how the prior balanced obstruction can appear unbalanced. Neither its cited-family paragraph nor Section 6 states that balance is the obstruction, or explains 2r+7 as an exclusion of this example. Section 6 says only that Theorem 1.10 motivates the conjecture. The source’s alternating-cycle/pseudo-cover discussion is not itself a Hamilton-connectedness guarantee. I found no explicit claim that the extra forbidden graph was selected to eliminate this construction; mathematically it does not eliminate F_r at all. These observations do not establish what the authors intended.

## The three citing works and later-source limitations

Fresh OpenAlex records for W4400848169, W7164133400 and W7214296171 all return closed access, a single publisher location, and no repository full text: [outputs/citing-locations.json](outputs/citing-locations.json). No open or arXiv body was located in the bounded title searches. Their full bodies remain unread; no negative literature clearance is inferred.

The indexed primary excerpts of Xiong et al., *Spanning connectivity of K₁,r-free split graphs* (2024), DOI 10.1016/j.dam.2024.07.005, Section 5, describe the companion example as a lower-bound example for the Hamilton-connected spanning-connectivity threshold, followed by its Conjecture 5.2. They do not expose a different construction in the available text (logs/search1.json and search5.json).

Chen–Tian, *Spanning fan-connectivity of K₁,r-free split graphs* (2026), DOI 10.1016/j.disc.2026.115267, attributes the r-connected K₁,r-free Hamilton-connectedness conjecture to Liu et al. and treats small forbidden-star parameters. The available indexed text gives no further law for the non-Hamilton-connected family (logs/search3.json and search5.json).

Chen–Geng–Li–Yu, *Spectral radius and Hamiltonicity in generalized split graphs*, DOI 10.1016/j.disc.2026.115437, concerns independent vertices replaced by cliques of size at least two and spectral sufficient conditions. Its indexed primary excerpt exposes no usable description of the companion obstruction (logs/search6.json). Its online date is 2026 with a 2027 volume assignment. No contrary inference from this absence is warranted. None of these limited later texts is needed for the explicit bridge established above.

## Integrity and handback

All writes are lane-local. `outputs/inputs-before.sha256` and `outputs/inputs-after.sha256` hash every file in the discovery and independent-review lanes; `outputs/input-hash-comparison.txt` records byte-for-byte equality. Instructions and supplementary inherited context are separately bound. Downloads were data only, placed in fresh per-request directories (the first retry’s two receipt files were subsequently grouped into its own directory). Every Python call used python3 -I under the lane-local process-group RSS watchdog, two pinned CPUs, CPU 120 seconds, wall 140 seconds, MALLOC_ARENA_MAX=2 and local TMPDIR/cache. No child agent, git operation, ledger edit, browser tab, external message, upload, credential access, TLS bypass or Lean run occurred. No background job remains.

The held counterexample remains mathematically valid. The newly resolved comparison undermines its substantive-novelty case: the prior family already encodes its entire obstruction, and a short regular sparsification supplies the conjecture-breaking hypotheses. **SUBSUMED is the review recommendation; root alone decides disposition.**
