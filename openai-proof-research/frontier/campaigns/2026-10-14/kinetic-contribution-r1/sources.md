# Kinetic-window contribution review: sources and access

2026-10-14. Companion to `review.md`. Frozen input hashes are in `input-hashes.json`. Output hashes are in `outputs.json`. Pinned mathematical truth is stipulated at commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` and is not audited. The author of the candidate opened no external literature. Every comparison below was opened in this review.

## Candidate and internal record

| Item | What was read | Role |
|---|---|---|
| `frontier/campaigns/2026-10-14/kinetic-window-factory/candidate.md`, SHA-256 `7c71805a0029bf5badcdbed37355775741e7aeb2513a3fba0a9a64b1f8fd2208`, 28868 bytes | complete | statement (F) and Lemma W |
| same directory, `README.md`, `exclusions-and-failures.md`, `reading-and-provenance.md`, `provenance.json` | complete | scope, risks, author's reading limits |
| `frontier/iterations/i340-kinetic-path-fluctuations.md` | complete | original unpaid window |
| `frontier/experiments/i340_kinetic_path_fluctuations/analysis.md` | §§1–6, including the redundant-time obstruction | I340 partials |
| `frontier/experiments/i340_kinetic_path_fluctuations/reading-and-failures.md` | complete | I340 reading record of BGSS §8.2 |
| `frontier/sources/i340_kinetic_path_fluctuations/literature.md` | complete | prior comparison note; re-checked here |
| `frontier/iterations/i340-parent-path-transfer.md` | opening statement and the tightness disclaimer | credited continuity and transfer |
| `AGENTS.md`, `sources/upstream.json` | complete | pin and agent rules |
| `sources/CONTENTS.md` items 363–364 and a search for process-convergence wording | catalogue statements | companion screen |

`checks/shift_checks.py` and `checks/shift_checks.json` were not rerun. The candidate records them as illustrations. They are not used as evidence.

## Pinned H

Prefix `preprints/Hard-sphere-fluctuations-on-the-regular-Boltzmann-lifespan-September-23-2026/build/` at the pinned commit. Local copies under `frontier/campaigns/2026-10-14/kinetic-window-discovery/fetched-H/`. Blob SHA-1 values match `sources/preprints-tree.json` as recorded in the candidate's `provenance.json`. This review recomputed the SHA-256 of the three section files it read in full or in the cited ranges.

- `sections/01-introduction.tex`, SHA-256 `f64b52941054e73c5a9e80ed7698c6a2d0a5d7f6894decd8c9dbb8fcd9d4c2a8`. Read complete. Used for the FDD statement, the exclusion of tightness, and the grand-canonical law.
- `sections/04-cluster-expansion.tex`, SHA-256 `5f824af314132999e830425354a43a273d2e17e14bf46d02a4d254917c8f8d47`. Read `lem:autonomous-partition` through `lem:one-slab-expansion` (lines 46–259) and the pulse-record definition (lines 415–420).
- `sections/06-sharp-asymptotics.tex`, SHA-256 `32a5a00ce410873a30fbed113b0b1ec56a80da5b6bc28664ae19a73637282883`. Read `lem:sharp-merger-coordinates` (lines 145–228).
- `sections/02`, `03`, `05`, `07`, `08`, `main.tex`, and `references.bib` were not re-read line by line. Their theorem labels are used only as stipulated by H's introduction and by the candidate's dependency table. `references.bib` was read through the BGSS and DHM entries.

Raw URL pattern:

`https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Hard-sphere-fluctuations-on-the-regular-Boltzmann-lifespan-September-23-2026/build/<path>`

## Primary literature read in this review

### Bodineau–Gallagher–Saint-Raymond–Simonella, short-time nonequilibrium process

Thierry Bodineau, Isabelle Gallagher, Laure Saint-Raymond, and Sergio Simonella, arXiv:2008.10403v2, 25 August 2022.

- HTML: <https://arxiv.org/html/2008.10403v2>
- PDF: <https://arxiv.org/pdf/2008.10403v2>
- Local extract: `frontier/sources/i20_pde_kinetic_discovery/literature/bgss_v2.txt`, SHA-256 `6a6d2d3448007d44f5910c74de4ce03c4ed5f7774b551ecc3dd7aa1b516a0bb0`, header `arXiv:2008.10403v2 [math.AP] 25 Aug 2022`. The versions file records PDF SHA-256 `18f06eb72c799ba845ccf5f025a0faf20b038a2f3004ec95bc2b15e20dd0a86a`.
- Published: Annals of Mathematics 198 (2023), no. 3, 1047–1201, <https://doi.org/10.4007/annals.2023.198.3.3>. The published PDF was not opened. Theorem numbers below are the v2 numbers.

Read: abstract; Theorem 2 and the four remarks that follow it; the whole-space and equilibrium comments on introduction pages 13–14 of the extract; Proposition 6.2.3, Proposition 6.2.4, Lemma 6.2.5, Lemma 6.2.6, and their proofs in §§6.2.2–6.2.3; Theorem 10, points 1–3; the clustering-time construction in §8.1 through Proposition 8.1.1; the whole of §8.2, including the three-case proof of the factor `δ` on pages 107–108. The large-deviation half of the paper and the identification chapter after Theorem 11 were not read.

Theorem 2 is process convergence on a data-dependent short interval for a periodic gas. Theorem 10 point 3 extracts `δ` from a free creation time, a free clustering time, or free flight.

### Bodineau–Gallagher–Saint-Raymond–Simonella, equilibrium long time

Same authors, arXiv:2201.04514v1, 12 January 2022.

- HTML: <https://arxiv.org/html/2201.04514v1>
- PDF: <https://arxiv.org/pdf/2201.04514v1>
- Published: Annals of Probability 52 (2024), no. 1, 217–295, <https://doi.org/10.1214/23-AOP1656>. The published PDF was not opened.

Read in the v1 HTML: abstract, §§1.1–1.3, Theorems 1.1, 1.2, and 1.3, Remarks 1.1–1.3, and display (1.19). The iteration that identifies higher moments after Remark 1.3 was not read. Theorem 1.3 is all-time convergence at equilibrium on a periodic box of dimension at least 3. Display (1.19) is the invariant-measure union bound that patches short-time tightness.

### Deng–Hani–Ma

Yu Deng, Zaher Hani, and Xiao Ma, arXiv:2408.07818v3, 18 July 2025.

- Abstract: <https://arxiv.org/abs/2408.07818v3>
- HTML: <https://arxiv.org/html/2408.07818v3>
- Local extract: `frontier/sources/i20_pde_kinetic_discovery/literature/dhm_v3.txt`, SHA-256 `84a3fd20c00982f7e600e6d8eb446e46d3b60ae12c5436b1bb05d74d1ffd4fce`, header `arXiv:2408.07818v3 [math.AP] 18 Jul 2025`. The versions file records PDF SHA-256 `61cc39d44eabf2f119880a9f1bd0cbb9409382ac3f67beff4c952f69290a30ed`.

Read: abstract, the statement area of Theorem 1, and §1.4.3 in full (fluctuations and large deviations, display (1.28)). The derivation in §§2–15 was not re-audited. Section 1.4.3 expects an off-equilibrium long-time fluctuation theorem and does not prove one.

### Le Bihan

Corentin Le Bihan, arXiv:2408.03597v2, 8 January 2026. Local extract `frontier/sources/i20_pde_kinetic_discovery/literature/lebihan.txt`, header `arXiv:2408.03597v2 [math.AP] 8 Jan 2026`. Read the abstract and the statements of Theorems 1 and 3. The proof was not read. The theorem is equilibrium covariance convergence for power-law potentials.

### Wu

- Zhengyan Wu, arXiv:2609.06482v1, *Fluctuating Kinetic Theory: A Poissonian Stochastic Boltzmann Equation*, <https://arxiv.org/abs/2609.06482>. Abstract and selected theorem headings of the public PDF text.
- Zhengyan Wu, arXiv:2610.08247v1, *A Program for Fluctuating Kinetic Theory*, <https://arxiv.org/abs/2610.08247>. Abstract.

These are stochastic kinetic models. They were not used as deterministic hard-sphere theorems.

### Identified and not re-read in full

- arXiv:2205.04110, cluster expansion on physical trajectories, short-time recovery of the BGSS theory. Abstract and the BGSS citation context.
- arXiv:2201.10149, survey of dilute-gas statistics. The short-time process theorem quoted there is attributed to BGSS.
- arXiv:2210.11812, equilibrium fluctuating hydrodynamics, which assumes the equilibrium kinetic fluctuation theorem.
- Spohn, J. Stat. Phys. 26 (1981), and van Beijeren–Lanford–Lebowitz–Spohn, J. Stat. Phys. 22 (1980), as cited by H for covariance, not for a path theorem on the regular lifespan. The articles were not re-opened.

## Search bounds

Searches issued on 2026-10-14, in addition to the papers named above:

- hard-sphere fluctuations, nonequilibrium, process convergence, tightness, whole space, fluctuating Boltzmann;
- Bodineau–Gallagher–Saint-Raymond–Simonella, time shift, cluster expansion, redundant collision, after the 2022 process papers;
- Deng–Hani–Ma, fluctuations, central limit, arXiv 2025–2026;
- arXiv queries combining hard spheres, Skorokhod or tightness, and nonequilibrium, restricted to 2023–2026.

The broad hits included molecular-dynamics relaxation, active Brownian spheres, KPZ single-file hard rods, lattice-gas fluctuation theorems, and Landau empirical-measure tightness for a stochastic collision model (arXiv:2511.09035). Those are different models. They were not used as evidence about (F).

No systematic citation crawl of Annals of Mathematics 198 (2023), 1047–1201, was performed. No claim is made about a manuscript that is absent from arXiv, that appears only in the unread published PDFs, or that sits outside the pinned OpenAI catalogue under a title this screen did not open. Inside the pinned catalogue, the kinetic entries read at catalogue level are the potential law of large numbers, H's finite-dimensional theorem, and the two Boltzmann nonuniqueness papers. H's introduction is the statement that excludes tightness.
