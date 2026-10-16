# Source contracts

Pinned upstream: `https://github.com/openai/math` at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` (`sources/upstream.json`). Upstream theorems are accepted as true (AGENTS.md); every new deduction is proved in `candidate.md`.

## Upstream (family 165)

File: `preprints/The-crossing-number-of-complete-graphs-September-23-2026/build/main.tex`
Raw URL: `https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-crossing-number-of-complete-graphs-September-23-2026/build/main.tex`
Local copy: `sources/upstream/kn/main.tex`, 40122 bytes, sha256 `5ae2c60704054f1b45290463c038c32335cc1554c5cc7dcee53518a045472301` (matches `frontier/sources/i14_spectral_width_novelty_r3/corpus-manifest.json`). Read in full.

| Contract | Label | Line | Exact content used | How used |
|---|---|---|---|---|
| U1 | `lem:normalization` | 850 | For every finite simple graph, a minimum ordinary drawing can be chosen polygonal, straight near vertices and crossings, with no crossings between edges with a common endpoint. | Applied to $G=K_n-e$ (§3) and to the optimal drawing in §4. |
| U2 | `eq:J`, `lem:cycles` | 222, 231 | Skew form $J=I+\frac12\sum\sigma\sigma T_w$; $J(z,z')=0$ for any two cycles. Proof states it "applies to every finite simple graph" (line 237). | Applied to the edge space of $G$ (Lemma 3.1). |
| U3 | `lem:weights` | 362 | $\sum_p A(u_p)/G'(u_p)=0$ for $\deg A\le N-2$. | Boundary of $z_A$ (Lemma 3.1). |
| U4 | `lem:detector` (with `eq:M` 437) | 443 | Order pairing $M$ on $2s$ nodes, any prescribed linear order, is nonsingular on $\mathcal P_{s-1,s-2}\times\mathcal P_{s-2,s-1}$. | Lemma 3.4 (twisted detector). |
| U5 | `thm:main` | 117 | $\operatorname{cr}(K_n)=Z(n)$ for $n\ge3$. | Even case (§4), Corollary B. |
| U6 | `sec:upper`, `prop:upper` | 709, 766 | Endpoint-sum two-page drawing; crossings are exactly same-page alternating pairs; total $Z(n)$. | Upper bound (§5). |
| proof template | `lem:tests` 504, `eq:support` 537, `eq:dim` 547, `lem:injectivity` 560, `eq:localtest` 569, `eq:local` 588, `eq:C` 622, `prop:odd` 639, `cor:lower` 690 | — | Not used as black boxes; their arguments are re-run with modifications and every changed step is proved in `candidate.md` §3. | Model for Lemmas 3.1, 3.3, 3.5, Prop. 3.6. |

Companion (bipartite) sections, read for context only, not used in the proof:
`preprints/The-crossing-number-of-complete-bipartite-graphs-September-23-2026/build/sections/{introduction,intersections,detector,subspaces,conclusion,normalization}.tex`, local copies in `sources/upstream/knm/` (hashes in `input-manifest.json`).

Catalogue entry: `sources/CONTENTS.md` line 3877 (family 165, "The Harary–Hill and Zarankiewicz crossing-number formulas").

## Literature

| Key | Reference | Locator | Use | Local evidence |
|---|---|---|---|---|
| OWH | Z. Ouyang, J. Wang, Y. Huang, "The crossing number of the Cartesian product of paths with complete graphs", Discrete Math. 328 (2014) 71–78, doi:10.1016/j.disc.2014.03.011 | Thm 3.1, Thm 3.2, Thm 3.3, Thm 3.4 (status $m\le12$), Lemma 2.3 (upper bound, from Zheng et al.), Cor 5.1 ($\operatorname{cr}(K_m\square P_n)=(n-1)\operatorname{cr}(K_{m+2}-e)+2\operatorname{cr}(K_{m+1})$, $m\ge4$, $n\ge1$), Cor 5.2 ($m\le10$) | Thm 3.2 proof re-derived in candidate §4; Cor 5.1 cited, not re-audited; Thm 3.1 used in check G to delimit the routine range. | `sources/literature/owh-2014-sciencedirect-fetch.txt` (ScienceDirect HTML fetch, 2026-10-15; theorem text at lines ~161–330) |
| CHN | K. Clancy, M. Haythorpe, A. Newcombe, "A survey of graphs with known or bounded crossing numbers", arXiv:1901.05155v1 | §2.2.1: Thm 28, Conjecture 29 (cr$(K_n-e)$, known $n\le12$); §3.2.4: Conjecture 74 (cr$(K_n\square P_m)$, confirmed $n\le10$ by OWH); refs [143], [231] | Conjecture statements and status | `sources/literature/clancy-1901.05155v1.pdf`, `clancy.txt` lines 545–565, 1138–1148, 3686, 3896 |
| Sadhu | A. Sadhu, "The crossing number of $K_{m,n}$ with one edge deleted", ResearchGate preprint 415807828, October 2026 | Abstract; "Further questions" (mentions only $K_{m,n}-F$) | Killed the bipartite candidate; confirms it does not treat $K_n-e$ | `sources/literature/sadhu-researchgate-fetch.txt` (lines 38–44, ~4112) |
| Schaefer | M. Schaefer, "The graph crossing number and its variants: a survey", Electron. J. Combin. DS21 v8 | Read for status of related problems | Background only | `sources/literature/schaefer-ds21v8.pdf`, `s.txt` |
| Zheng et al. | W. Zheng, X. Lin, Y. Yang, C. Cui, "On the crossing number of $K_m\square P_n$", Graphs Combin. 23 (2007) 327–336 | Origin of both conjectures (via CHN and OWH) | Attribution only; not read directly | — |
| Chia–Lee | G. L. Chia, C. L. Lee, "Crossing numbers of nearly complete graphs and nearly complete bipartite graphs", Ars Combin. (2015) | Even-case equivalent of OWH (per CHN) | Attribution only; not read directly | — |
