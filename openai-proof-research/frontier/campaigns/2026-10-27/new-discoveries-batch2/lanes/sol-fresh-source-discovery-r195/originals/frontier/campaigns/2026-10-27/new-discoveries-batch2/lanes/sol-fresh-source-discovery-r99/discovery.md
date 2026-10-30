# r99 — fresh graph and finite-geometry source discovery

Disposition: **UNRESOLVED, credit 0**. No full ordinary source theorem or counterexample. Counts remain 8 additional, 38 total. No PROOF.md, Lean or paper.

## Scope and duplicate gate

Read ancestor/batch AGENTS, current NEXT, ledger, prior-campaign-context and upstream catalogue. `context-read.json` hashes these inputs. Before sustained work, `duplicate-audit.json` screened 5,942 all-date SUMMARY/discovery/FINDINGS/PROOF/review/ledger-named Markdown, JSON and text files under openai-proof-research, excluding this lane. Terms cover super domination/domatic, competition number, Kovács–Nagy and both finite-geometry identifiers. Zero hits. Filename/content keyword screening is bounded and does not prove semantic independence. The actual accepted/held/excluded records were reconciled; no old family is nominated. MMPP remains parked; no MMPP source was fetched or mathematically reconsidered. r97/r98 are separate active lanes.

## Exact claim A — selected for sustained work

Douglas J. Klein, Juan A. Rodríguez-Velázquez and Eunjeong Yi, *On the super domination number of graphs*, Communications in Combinatorics and Optimization 5(2) (2020), 83–96, DOI 10.22049/CCO.2019.26587.1122, **Conjecture 2, printed p.93**. Actual author-institution VoR PDF saved as sources/super-vor.pdf. Latest arXiv metadata says v2, 23 April 2018; its actual PDF is also saved (Conjecture 25, PDF p.13). The internal compiled date in that PDF is November 27, 2024; it is not treated as a new submission date.

For every pair of finite simple undirected graphs G,H,

    gamma_sp(G □ H) >= gamma_sp(G) gamma_sp(H).

A subset D of vertices is super dominating iff every u outside D has a vertex v in D with N(v) intersect (V\D) = {u}. The invariant is the minimum size of D. The product is the Cartesian product, not the direct, strong or lexicographic product. Empty graphs and isolated vertices cause no counterexample by convention/additivity.

The source already proves half-order cases (Theorem 12), complete-factor values (Theorem 14), and the exact star-product formula gamma_sp(K1,r □ K1,s)=rs+1 (Theorem 17). None is new credit or a proposed residual endpoint.

### Actual closest bodies read

* Bujtás–Ghanbari–Klavžar, *Computational complexity aspects of super domination*, TCS975 (2023)114137: actual author-hosted journal PDF, Lemma2.4 and its proof, Corollary2.5 and Theorem3.1 tree/matching proof. This already contains the balanced private-core matching characterization used below. Tree identities and subdivision/II-matching results are not universal Cartesian-product results.
* Ghanbari–Jäger–Lehtilä, *Super Domination: Graph Classes, Products and Enumeration*, arXiv2209.01795v3, 31October2022, later DAM349(2024)8–24: actual full PDF saved/read for introductory known formulas, Section2 private-core exchange and product scope. Its products are neighbourhood corona, clique gluing and Hajós sum; the later enumeration section counts minimum super dominating sets, not super domatic partitions. The journal repository URL returned HTTP500; v3 is a genuine primary body but journal-version comparison remains incomplete.
* Alikhani–Ghanbari, arXiv2607.22686v1, actual HTML: definitions2.1–2.3 and final problems7.1–7.3. These concern super coalition partitions, a different invariant. A separate secondary lead to their submitted *Super domatic in graphs* was not promoted: no actual primary body or literal partition-count conjecture was obtained. No Q3-based nomination is made from that lead.

No public full resolution of Claim A was located in the bounded web/source/registry screen. This is not worldwide novelty clearance.

### Mathematical work: a full-scope reduction and the exact missing term

Write p(G)=|G|-gamma_sp(G). Equivalently, p(G) is the largest |A| for disjoint equally sized sets A,B such that all edges between A and B form a perfect matching. Indeed, take A=V\D and one private witness per outside vertex for B; witnesses are distinct, each meets A exactly once, and hence every A also meets B exactly once. Conversely B privately dominates A. This is the content of the already published Lemma2.4, not a new theorem.

Let n=|G|, m=|H|, a=p(G), b=p(H), and let O be the complement of any super dominating set in G□H. Choose one private witness for each member of O. Each witness edge changes exactly one coordinate. Partition O into X (witness changes the H-coordinate) and Y (witness changes the G-coordinate).

For fixed g, put X_g={h:(g,h) in X}. Every chosen H-direction witness lies outside the entire O-row, is private relative to the entire O-row, and therefore remains private relative to X_g. Consequently H\X_g is super dominating in H and |X_g|<=b. Similarly |Y^h|<=a for every fixed column h. Thus

    |O| = |X|+|Y| <= nb+ma,
    gamma_sp(G□H) >= nm-nb-ma
                      = m gamma_sp(G)+n gamma_sp(H)-nm.

Combining this with the injective-private-witness bound gamma_sp(G□H)>=ceil(nm/2) is valid for every pair. These are weaker, routine deductions; they do not resolve or receive credit for Claim A.

The source conjecture is exactly the demand

    p(G□H) <= nb+ma-ab.

One must save the additional **ab** outside vertices. The row and column budgets above do not imply it. For n=m=4 and a=b=1, put four horizontal tokens at (i,i), and four vertical tokens at (i,i+1 mod4). They are disjoint, meet every row/column budget, and satisfy the half-order bound 8, but exceed nb+ma-ab=7. This is a counterexample to a relaxation, NOT a source counterexample: no private-witness graph realization is supplied. In fact the source's complete-factor formula gives p(K4□K4)=4.

A second failed simplification is that every D-row is itself super dominating in H. In K2□K3, one complete K3-layer is a valid size3 super dominating set, while its other row is empty and is not super dominating in K3. Hence multiplying individual row minima is invalid.

Finally gamma_sp is additive on graph components: private neighbours cannot cross components, and optimal component sets unite. Products decompose over component pairs. A proof for all nontrivial connected factors would therefore settle all graphs (K1 factors give equality); this reduction is uncredited and leaves precisely the same universal connected gap.

### Exact bounded checks and falsifiers

`check.py` uses only Python's standard library. It enumerates every labelled connected graph of orders2–5, removes isomorphic duplicates by all vertex permutations, and obtains 30 factors (1,2,6,21 by order). Factor gamma values are exact subset enumerations. It checks all 234 unordered factor pairs except those where both factors have order5. For 192 pairs the half-order bound settles the proposed inequality. For the other42 it enumerates every outside set of size nm-gamma_sp(G)gamma_sp(H)+1: 5,503,420 exact subsets total; none has private witnesses. Upward closure of super dominating sets means that testing this one outside cardinality excludes every larger outside cardinality as well. There is no probabilistic or floating-point step. `check-results.json` records each graph, each pair and subset count.

These finite checks do not prove Claim A. The sharp falsifier for any future proof is an actual pair G,H and outside set O with |O|>nb+ma-ab together with a literal valid private witness for every element of O. The strongest objection to the present route is its loss of cross-direction compatibility: separate row and column budgets cannot recover ab, as the eight-token example proves. A missing universal coupling inequality is the precise mathematical gap. No expansion of finite testing closes it.

## Exact claim B — finite-geometry screen, not selected for investment

Kovács–Nagy, *Avoiding intersections of given size in finite affine spaces AG(n,2)*, latest arXiv2305.05632v3 (30May2024), **Conjecture1.11**, later JCTA209(2025)105959. Actual v3 HTML saved. Kovács, *Code-based [3,1]-avoiders in finite affine spaces AG(n,2)*, latest arXiv2505.24072v1 (29May2025), actual HTML **Conjecture1.1**, repeats the claim.

For every fixed integer k>=1 and t in {0,...,2^k}, define Sp(n;k,t) to be the cardinalities m in {0,...,2^n} such that EVERY m-element subset of F2^n meets SOME affine k-flat in exactly t points. The claim is

    lim(n→infinity) |Sp(n;k,t)| / 2^n = 1.

Read actual original definitions1.4, Conjecture1.11, cube/evasive arguments and Theorems1.8–1.10, and successor Construction4.1, Theorem1.5 and Corollary4.7 with proof. The successor bounds the number of exceptional sizes produced by its code construction by O(n c_k^n), with c_k=(2^(k-1)-1)^(1/(k-1))<2. Therefore that entire construction produces density-zero exceptional sizes and explicitly cannot disprove the density conjecture. Exponential many exceptions are not positive density. Known k<=2 and special t, or reproducing this corollary, are not fresh outcomes. Full all-fixed-k,t proof or a positive-density counterfamily is absent. Journal body and wider classical evasive-set bodies were not obtained here, so no substantive/prior-art clearance is asserted. No investment beyond this body screen.

## Current registries and chronology

OpenAI HEAD freshly fetched at19:37UTC and again later: unchanged 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a, commit26October21:18:03UTC. Omega initially49444ed17a62b3b1e64dd3a79cbeeb6ecfe6867d (commit19:35:46UTC), then9aef67a59dec08d1ff04a18a3d23560525ab023d (commit19:40:58UTC). Initial supplied checkpoint28414→49444 is3commits/191files; 49444→9aef is1commit/23files. Both comparison JSONs and every nonremoved changed file body are saved. These are actual complete small deltas, not the old truncated97commit/300file comparison. Family/path/content screening found no matching result. Full baseline trees/catalogue from root-edge-irregulator-final-freeze-r1 were screened separately; their exact bytes are hash-referenced in registry-screen.json. Older r86/r90/r1/r2 intermediate chain is inherited context, not independently rebuilt and body-cleared for these new targets. Accordingly registry PRIOR HOLD persists for any eventual acceptance. No Blueprint/Lean equivalence or exhaustive whole-registry body reading is claimed. No later public counterpart was located requiring a priority chronology determination.

## Operational limits and disposition

All writes confined to r99. No git/shared/ledger/candidate/count edits, external mutations, contact, browser or upload. The mandated copied helper_guard.py enforces AS512MiB, sampled process-group RSS512MiB, CPU210s, wall230s, nominal40ms, BLAS1. Successful exact check: ~8s, sampled peak11.4MiB. Missing bs4/networkx/g++ attempts are recorded or disclosed; the successful checker needs none. No resource caps raised. One repository HTTP500 was retained and a distinct primary arXiv body used; no 403/429/challenge bypass or retry loop.

Claim A remains a properly attributed fresh source target with a rigorous failed-route analysis; Claim B remains screened only. Neither is a full new result. No formal/manuscript investment recommended from this packet.
