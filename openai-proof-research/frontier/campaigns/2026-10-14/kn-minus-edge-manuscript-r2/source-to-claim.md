# Sources, claims and read extents

Paths are relative to the project root `openai-proof-research/` unless stated. Hashes and sizes of every file named here are in `input-manifest.json`. Reading extents below are inherited r1 records unless explicitly identified as r2 reading; no new primary-literature search is claimed.

## 1. Pinned upstream (premises, stipulated true)

Repository `https://github.com/openai/math`, commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` (`sources/upstream.json`).
File `preprints/The-crossing-number-of-complete-graphs-September-23-2026/build/main.tex`, 40122 bytes, SHA-256 `5ae2c60704054f1b45290463c038c32335cc1554c5cc7dcee53518a045472301`, git blob `826c79722317e701a7c77e9dcc0bb5e082f2bc39`.
Local copies used (identical hash): `frontier/campaigns/2026-10-14/kn-minus-edge-proof-r1/sources/kn-main.tex` and `frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/The-crossing-number-of-complete-graphs-September-23-2026/build/main.tex`. Read extent: the full file (942 lines). The upstream README in the same directory was read in full.

| Paper | Upstream label (line) | Statement used | Where it enters the paper |
|---|---|---|---|
| U1 | `lem:normalization` (850–854), Lemma A.1 | minimum drawings of any finite simple graph can be normalized | Sec. 3 (odd bound), Sec. 4 (even bound) |
| U2 | `eq:J` (222), `lem:cycles` (231–233), Lemma 2.1 | skew cycle pairing vanishes on cycles, for every finite simple graph | Lemma 3.1, applied to G = K_n − e |
| U3 | `lem:weights` (362–369), Lemma 3.1 | barycentric interpolation weights | Lemma 3.1 (boundary of test chains) |
| U4 | `eq:M` (437), `lem:detector` (443–452), Lemma 3.3, first sentence | order pairing nonsingular on the degree rectangles P_{s−1,s−2} × P_{s−2,s−1}, any prescribed order | Lemma 3.5 (twisted detector). The rectangular statement is needed, not its square consequence. |
| U5 | `thm:main` (117–126), Theorem 1.1 | cr(K_n) = Z(n), n ≥ 3 | Sec. 4 (even bound), Sec. 6 (Corollary B) |
| U6 | `sec:upper` (709), `prop:upper` (766–768), Section 5, Proposition 5.1 | endpoint-sum two-page drawing with Z(n) crossings, same-page alternating pairs | Sec. 5 (upper bound) |

The upstream proof of its own odd lower bound serves as a template for Lemmas 3.1, 3.6 and Proposition 3.7; every changed step is proved in the paper, and no upstream lemma beyond U1–U6 is used as a black box. The bipartite companion preprint (same commit, `preprints/The-crossing-number-of-complete-bipartite-graphs-September-23-2026/`) is cited only to describe Sadhu's stated inspiration; it is not used in any proof.

## 2. External literature

| Ref. | What the paper takes from it | Status in the paper | Local evidence and read extent |
|---|---|---|---|
| Ouyang, Wang, Huang, Discrete Math. 328 (2014) 71–78 [OWH] | Cor. 5.1: for m ≥ 4, n ≥ 1, cr(K_m □ P_n) = (n−1) cr(K_{m+2} − e) + 2 cr(K_{m+1}), P_n with vertices 0..n. Thm. 3.2 (reproved in Sec. 4). Thm. 3.1 (novelty boundary only). Thms. 3.3, 3.4, Cor. 5.2, Lemma 2.3 and displays (1.1)–(1.2) (attribution). | Cor. 5.1 cited, unconditional, proof chain (Thms. 5.1, 5.2, Lemma 4.1, a lemma of Bokal) not re-audited. | `frontier/campaigns/2026-10-14/fresh-substantial-discovery-r2/sources/literature/owh-2014-sciencedirect-fetch.txt` (ScienceDirect HTML text fetched by the candidate agent on 2026-10-15). Read: lines 94–330 (abstract, Sections 1–5 as rendered). Statement lines: (1.1)–(1.2) at 121, Lemma 2.3 at 153, Thms. 3.1–3.4 at 173/195/213/221, Lemma 4.1 at 244, Thms. 5.1–5.2 at 286/298, Cors. 5.1–5.2 at 308/316. The publisher PDF was not available; a later live request by the proof reviewer returned HTTP 403 (`kn-minus-edge-proof-r1/README.md`). |
| Chia, Lee, Ars Combin. 121 (2015) 437–446 | Lemma 1 (upper bound), Theorem 1 (counting lower bound), Theorem 2 (even case under odd Harary–Hill), Corollary 1 (n ≤ 12), Conjecture 1; also treats K_{m,n} − e | Attribution only | `frontier/campaigns/2026-10-14/kn-minus-edge-parent/literature/chia-lee-2015.pdf` (10-page image scan, no text layer). Scan pages 1–7 (journal pp. 437–443) rendered to images in scratch (`/tmp/kn-cl`, not retained) and read; pages 8–10 (pp. 444–446) not read. |
| Zheng, Lin, Yang, Cui, Graphs Combin. 23 (2007) 327–336 [ZLYC] | upper bound for cr(K_n − e) with equality for n ≤ 8; conjecture of equality; cr(K_6 □ P_n) = 15n+3; lower bound (1.1); conjecture (1.2) | Attribution only; **not read directly**; the paper says so | Through OWH (lines 121, 153) and the survey CHN v5 (below). Title and bibliographic data from CHN v5 reference [251]. |
| Clancy, Haythorpe, Newcombe, arXiv:1901.05155v5 [CHN] | Thm. 2.19, Conj. 2.20, Thms. 3.12–3.13, Conj. 3.14; status of both conjectures | Survey, attribution | `frontier/campaigns/2026-10-14/kn-minus-edge-parent/literature/clancy-haythorpe-newcombe-v5.pdf`; a local text extraction `work/chn-v5.txt` (not public). Read: lines 695–715 and 1375–1395 of the extraction (statements and status) and reference [251]. The v1 extraction `fresh-substantial-discovery-r2/sources/literature/clancy.txt` was searched for the same items. |
| Sadhu, ResearchGate preprint 415807828, October 2026 [Sadhu] | Theorem 1.1, cr(K_{m,n} − e) for all m, n and every edge; stated independence from the Zarankiewicz formula; stated inspiration by the bipartite OpenAI framework | Contemporary antecedent for the bipartite family; compared in Sec. 1.2 and Sec. 7; no claim of independence of idea or of global priority | `frontier/campaigns/2026-10-14/fresh-substantial-discovery-r2/sources/literature/sadhu-researchgate-fetch.txt` (text rendering of the ResearchGate page; the PDF link was not accessible). Passages compared, by starting line: abstract 38–44; contribution paragraphs 100–102 and 232–302; Theorem 1.1 at 164; Proposition 2.2 at 506; Lemma 3.2 at 1346 and the start of its proof; Lemma 4.1 at 2032; proof of Theorem 1.1 from 3436 (three-edge completion, closing rank comparison to about 4080); further questions 4112–4150; reference to Chia–Lee at 4174. Sadhu's lemmas were not re-proved. |
| Asiri, Burdett, Chimani, Haythorpe, Newcombe, Wagner, GD 2025, LIPIcs 357, art. 20 | general computational framework for cr(G □ P_n), applied to graphs of order 5 and 6 | Related work | `frontier/campaigns/2026-10-14/kn-minus-edge-parent/literature/asiri-et-al-gd2025.pdf`; read: abstract, introduction and statement of scope (first pages). |
| Bokal, J. Combin. Theory Ser. B 97 (2007) 381–384 | lemma used inside the OWH proof of Cor. 5.1 | Named only as part of the cited chain | Not read; bibliographic data from the OWH reference list ([5]). |
| Harary, Hill (1963) | origin of the Harary–Hill conjecture | Attribution | Not read; standard citation. |

## 3. Claim map

| Claim | Proof location | Inputs |
|---|---|---|
| Theorem A, odd n = 2s+1, lower bound (new for s ≥ 7) | Sec. 3: Lemmas 3.1, 3.3–3.6, Proposition 3.7 | U1, U2, U3, U4 |
| Theorem A, even n, lower bound (classical after U5) | Sec. 4, Proposition 4.1 (proof of OWH Thm. 3.2 reproduced) | U1, U5 |
| Theorem A, upper bound (classical) | Sec. 5, Proposition 5.1 | U6 |
| Theorem A, n ≤ 5 and assembly | Sec. 6 | above |
| Corollary B | Sec. 6 | Theorem A, U5, OWH Cor. 5.1 |
| Novelty boundary (odd n ≤ 13 classical; new for odd n ≥ 15; new lower-bound input to Cor. B only for odd m ≥ 13 and n ≥ 2; bounded literature comparison) | Sec. 1.1, Sec. 7 | OWH Thm. 3.1, Thm. 3.2, U5; identities checked by R4 |

## 4. Internal records read (not cited in the paper as literature)

Frozen candidate `fresh-substantial-discovery-r2/candidate.md` (full) and `source-contracts.md` (full), its README, provenance and manifests; proof review `kn-minus-edge-proof-r1/review.md` (full) and `provenance.json`; contribution review `kn-minus-edge-contribution-r1/review.md` (full), `sources.md`, `gap-check.py`; parent dispositions and verifications (`kn-minus-edge-parent/{proof,contribution}-r1-{disposition,verification}.json`); the manuscript brief and task; `kn-minus-edge-parent/*task.json` and `discovery-terminal.json` for the model names in the acknowledgement only; `kn-minus-edge-parent/RIGHTS.txt`, `UPSTREAM-LICENSE`; `AGENTS.md`; `frontier/campaigns/2026-10-14/publication-metadata.json`. That was the r1 reading record. For r2, the parent read the manuscript audit, formal parent disposition and formal coverage record; this updates the formal-status description without claiming a fresh source or compiler audit. At n=1 the product coefficient vanishes; the upper bound is classical. New-range statements retain the Section 7 bounded-search limit.
