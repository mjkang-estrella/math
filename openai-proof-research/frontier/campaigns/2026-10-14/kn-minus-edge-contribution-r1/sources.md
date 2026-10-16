# Sources read for the contribution gate

Hashes are SHA-256 of the bytes that were read. Third-party files were not copied into this directory.

## Frozen candidate

| Item | Locator | Bytes | SHA-256 | Read |
|---|---|---:|---|---|
| candidate.md | `fresh-substantial-discovery-r2/candidate.md` | 23029 | `2a078a07142986c93845f4855496db14e41ee2590adc17720727b19145dd1c8b` | full |
| README.md | same directory | — | `eebfc80fe523c664972474f0d0838c86b19106a3e5d94c306a2730b940cba93e` | full |
| source-contracts.md | same directory | — | `7ab0719ee152871ac524c29ecb1eea8c5c3ecbbfc137ee5aa026ac1bc300b731` | full |
| provenance.json | same directory | — | `b88c015331124ef204a9f29b757650934e814c2bf66e21bdbb7cce6683e107d3` | full |
| parent-screen.json | `kn-minus-edge-parent/parent-screen.json` | — | `80166864f2648a130340626e01b97c7b2c57dde0b3dbdf36f74991f2cae3312e` | full |

The candidate's input manifest was used to confirm the Ouyang–Wang–Huang, Sadhu, and complete-graph hashes. The two check scripts were read. They were not rerun.

## Pinned complete-graph argument

Local copy `fresh-substantial-discovery-r2/sources/upstream/kn/main.tex`, 40122 bytes, SHA-256 `5ae2c60704054f1b45290463c038c32335cc1554c5cc7dcee53518a045472301`.

Raw URL: `https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-crossing-number-of-complete-graphs-September-23-2026/build/main.tex`.

Read: cycle pairing (`lem:cycles`, from line 231), interpolation and the rectangular detector (`lem:weights`, `lem:triangles`, `lem:detector`, lines 362–492), polynomial tests, injectivity, the odd proposition, and the even deletion corollary (lines 504–707), and the start of the two-page upper bound. The rectangular nonsingularity is the statement of `lem:detector` before the square consequence (display `eq:detector`).

## Ouyang–Wang–Huang 2014

Z. Ouyang, J. Wang, Y. Huang, Discrete Mathematics 328 (2014) 71–78, doi:10.1016/j.disc.2014.03.011.

Preserved ScienceDirect HTML text: `fresh-substantial-discovery-r2/sources/literature/owh-2014-sciencedirect-fetch.txt`, SHA-256 `69b46e0f623ae186f258a2108466c8ecce4f58e6b7e8aa54d68f2520561878ba`. A fresh ScienceDirect open was not repeated; the parent screen records an Internal Error on that open.

Read in that text: introduction through display (1.2); Lemma 2.3; Theorems 3.1, 3.2, 3.3, and 3.4, including the proofs of 3.1 and 3.2; Lemma 4.1; Theorems 5.1 and 5.2; Corollaries 5.1, 5.2, and 5.3. Bokal's lemmas cited inside that chain were not re-read.

## Chia and Lee 2015

G. L. Chia and C. L. Lee, Ars Combinatoria 121 (2015) 437–446.

Publisher PDF: `https://combinatorialpress.com/article/ars/Volume%20121/volume-121-paper-35.pdf`.

Local parent copy `kn-minus-edge-parent/literature/chia-lee-2015.pdf`, 382327 bytes, SHA-256 `410a1dab0d1c6c8bebe95b311627528a823c11a1d65bb2d9ab63326f7a35175d`. The file is a scan. `pdftotext` does not recover the words. Printed pages 437–443 were read from page renders: abstract, Lemma 1 and its proof, Lemma 2, Theorem 1 and its proof, Theorem 2 and its proof, Remark 2, Corollary 1, Conjecture 1, and the bipartite Lemma 3 and Theorem 3. Printed pages 444–446, the rest of the bipartite section, were not read.

## Clancy, Haythorpe, and Newcombe

arXiv:1901.05155v5, 8 December 2021, "Version 2.0". Downloaded PDF, 95 pages, 1188444 bytes, SHA-256 `6768bd30589ab6a6dfc9725852295a3860897a4f9db6ea72c7d994fd97af3e3a`, from `https://arxiv.org/pdf/1901.05155`.

Read: Section 2.2.1 (Theorems 2.19 and 2.20's surrounding text, the even-case sentence, and the Chia–Lee sentence) and Section 3.2 on \(K_n\square P_m\) through Conjecture 3.14 and the Ouyang–Wang–Huang confirmation for complete order at most 10. Conjecture 2.3 was checked in the bipartite section and is Zarankiewicz's conjecture. The survey's even-case sentence names that conjecture; Ouyang–Wang–Huang, Theorem 3.3, names Harary–Hill.

## Asiri et al. 2025

Z. Asiri, R. Burdett, M. Chimani, M. Haythorpe, A. Newcombe, and M. H. Wagner, LIPIcs 357 (2025), article 20, doi:10.4230/LIPIcs.GD.2025.20.

PDF `https://drops.dagstuhl.de/storage/00lipics/lipics-vol357-gd2025/LIPIcs.GD.2025.20/LIPIcs.GD.2025.20.pdf`, 32 pages, 3176389 bytes, SHA-256 `3e88c024378fcc7ea8ce0c7988dbc547818f42eb47fcd022c70859fcbb0942a5`, creation date 30 October 2025.

Read: abstract, introduction, the BCCNP definition, the statement of the reduction from a finite restricted drawing, Sections 5 and 6 on the order-5, order-6, and partial order-7 scope, and the reference to Zheng for survey index 156. The appendix of individual graphs was not read graph by graph. A text search of the extraction found no general complete-order theorem.

## Sadhu 2026

A. Sadhu, ResearchGate publication 415807828, October 2026, CC BY 4.0. Page: `https://www.researchgate.net/publication/415807828_The_crossing_number_of_K_with_one_edge_deleted`. The PDF link returned HTTP 403.

Text extraction already stored by the candidate author: `sources/literature/sadhu-researchgate-fetch.txt`, 51891 bytes, SHA-256 `b28302e25f257d230e4aef616315350e31785878b34306bca47e9804bd6162bd`.

Read from that extraction: abstract and contribution paragraph; Lemma 3.2 (balanced compression) and the opening of its proof; Lemma 4.1 (rectangular bipartite detector); the three-edge replacement and completed matrix in the proof of Theorem 1.1; the closing comparison \(c\ge Z(m,n)-t_mt_n\); the further questions on \(K_{m,n}-F\). The extraction runs words together. Sadhu's lemmas were not re-proved.

## Zheng, Lin, Yang, and Cui 2007

W. Zheng, X. Lin, Y. Yang, and C. Cui, Graphs and Combinatorics 23 (2007) 327–336, doi:10.1007/s00373-007-0726-z.

The DOI PDF URL returned an HTML interstitial (about 3 kB, `content-type: text/html`), not the article. The paper was not read. Attribution in the review follows Ouyang–Wang–Huang's quotations and Clancy–Haythorpe–Newcombe v5, Theorems 2.19 and 3.12–3.13 and Conjectures 2.20 and 3.14, with that limit stated.

## This gate's own check

`gap-check.py`, 2181 bytes, SHA-256 `693f2092901ec569366aaca553b1578cabd56c6ec00ae7c40f287220c902af10`.

`gap-check.out`, 850 bytes, SHA-256 `c8042c28964422ae0f2181ee8a9e07d64f1e1e8ac535bb81a4ba3421da906593`.

Python 3, stdlib only. It checks the Ouyang–Wang–Huang Theorem 3.1 deficit, the ceilings through odd order 31, the Theorem 3.2 gap, the vertex-deletion gap, and the even identity. It does not check drawings.
