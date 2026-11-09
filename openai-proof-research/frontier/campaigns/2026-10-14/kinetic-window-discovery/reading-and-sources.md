# Primary-source reading map, hashes and literature boundary

2026-10-14. All hashes are SHA-256 of the full bytes. Git blob ids were checked against
`sources/preprints-tree.json` by `checks/verify_sources.py`. Reading scope is stated separately
from hashing: a hash covers the whole file, while the reading column says what was actually read.

## Pinned H (`openai/math@fd4aeeb2…`, `preprints/Hard-sphere-fluctuations-on-the-regular-Boltzmann-lifespan-September-23-2026/build/`)

| File | Bytes | SHA-256 | Blob | Read this task | Labels relied on |
|---|---|---|---|---|---|
| sections/01-introduction.tex | 11368 | f64b5294…c2a8 | 18a09778 | all 242 lines | `ass:kinetic`, `eq:grand-canonical`, `eq:empirical-fluctuation`, `thm:main` (FDD only; l.46–47 disclaim tightness) |
| sections/02-initial-target.tex | 23065 | 51fad6be…2396 | 1050ba9a | lines 1–90 (statement of `prop:initial`) | `prop:initial`, `eq:initial-N-moments`; `prop:gaussian-target` via the prior parent reading (lines 270–510) |
| sections/03-dhm-inputs.tex | 20583 | a2506a51…1cbf | ffa66588 | all 397 lines | `thm:dhm-package`, `lem:dhm-dummies`, edge-integral convention `eq:edge-integral` |
| sections/04-cluster-expansion.tex | 39676 | 5f824af3…8d47 | 87d6cdc9 | all 781 lines | `lem:autonomous-partition`, `lem:one-slab-expansion`, `lem:one-root-bridge`, `lem:marked-regrouping`, `lem:diagram-labels`, `lem:stopped-variation`, `thm:marked-expansion` |
| sections/05-cutoff.tex | 52765 | e5380f7a…ac4e | 81f66d30 | lines 1–105 (statement and witness reduction) | `prop:cutoff`, used as a stipulated statement only |
| sections/06-sharp-asymptotics.tex | 47771 | 32a5a00c…2883 | dfa4a25d | all 946 lines | `thm:sharp-cumulants`, `eq:sharp-initial-link`, `eq:sharp-merger-count`, `lem:sharp-merger-coordinates` and proof, `eq:sharp-scaling`, `lem:sharp-factorials`, `lem:sharp-summability` and proof, the cycle paragraph l.618–639 |
| sections/07-gaussian-limit.tex | 20846 | 9cf6ab1d…99e4 | abc670cb | all 449 lines | records `eq:limit-mark-update`, `prop:cumulant-clt`, `eq:limit-factorial-ordinary` |
| sections/08-transfer.tex | 3357 | 3efa338d…0136 | 82268938 | all 69 lines | `lem:center-transfer`, proof of `thm:main` |
| figures/chronological-mergers.tex | 1507 | f53514c9…bf17 | c5909e0e | all | redundant contact = constraint, not a new translation |
| main.tex | 3819 | 4f84d56f…53af | fd0e2981 | `\input` list only | section order 01,02,03,04,06,07,05,08; no appendix |
| references.bib | 5705 | 6c423a9e…4a6c | 5e0a24b2 | not read | — |

The files were fetched from pinned raw URLs into `fetched-H/` for reading and deleted at the end of
the task. No source body is retained; `checks/verify_sources.py` re-fetches and re-verifies.

## Local inputs (read-only)

| Path | Bytes | SHA-256 | Read |
|---|---|---|---|
| AGENTS.md | 1298 | e9ab9518…3e7e | all |
| sources/upstream.json | 179 | 3784eb61…f30c | all; the pin matches |
| frontier/experiments/i340_kinetic_path_fluctuations/analysis.md | 17499 | 505a86ea…244d | all |
| frontier/experiments/i340_kinetic_path_fluctuations/reading-and-failures.md | 10968 | d5a5ebbe…3bb1 | all |
| frontier/experiments/i340_kinetic_path_fluctuations/input-authentication.json | 15853 | af51c1ec…2d30 | all |
| frontier/iterations/i340-kinetic-path-fluctuations.md | 7082 | f8573604…78f7 | all |
| frontier/iterations/i340-parent-path-transfer.md | 3701 | 811c29a5…512f | all |
| frontier/sources/i340_kinetic_path_fluctuations/literature.md | 5495 | 0663fb24…34d5 | all |
| frontier/sources/i20_pde_kinetic_discovery/literature/bgss_v2.txt | 528052 | 6a6d2d34…0bb0 | lines 3989–4420, 5877–5935, 6960–7010 |
| sources/preprints-tree.json | 4858136 | eeecc1da…e09b | H blob/size entries only (by script) |

## BGSS 2008.10403v2, read in the retained primary text above

- **§6.2.2, Prop. 6.2.3–6.2.4 (modified GRR), Lemmas 6.2.5–6.2.6 and proofs.** The fourth-moment
  bound (6.2.10) is C(|t−s|²+|t−s|/μ). The cutoff is α=μ⁻⁷ᐟ³ and γ=7/3. The microscopic step
  (6.2.19)–(6.2.26) is "at least two collisions in the periodic gas during a 2α-cell", with
  P(A_i)≤Cαμ^{−1/3}, proved through Prop. 3.3.1.
- **Theorem 10 (statement) and the §8.2 proof of point 3** (lines 6971–6985). The window factor
  comes from localising a collision's Duhamel time, or a *clustering* recollision time, which in
  BGSS's representation is an integration variable ("the recollision time has to be integrated
  now in [t−δ,t]").

H has no such coordinate for redundant contacts (H `lem:sharp-merger-coordinates`, figure). That is
the gap the I340 report identified. Lemma A uses a different mechanism, global time translation,
which needs no recollision coordinate. Our Prop. C also differs from Lemma 6.2.5.

## Bounded literature check (2026-10-14)

Queries (web):

1. `hard sphere gas nonequilibrium fluctuations process convergence long time Boltzmann tightness 2025 2026 arXiv` (extended)
2. `"fluctuating Boltzmann equation" hard spheres "Deng" "Hani" "Ma" fluctuations long time derivation`

The searches returned the known items: BGSS 2008.10403 (Annals 2023), BGSS 2201.04514
(equilibrium, all times), BGSS 2012.03813 and 2210.11812 (equilibrium), Le Bihan 2212.04392
(equilibrium covariance), and DHM 2408.07818 (mean). One new item was checked at its primary
abstract page: arXiv:2609.14766, Kenig, *On particles and waves* (13 Sep 2026). It is expository on
DHM and makes no fluctuation-process claim.

No primary source was found that proves long-time nonequilibrium process convergence for hard
spheres. This is a bounded search, **not** a novelty proof. The prior file
`frontier/sources/i340_kinetic_path_fluctuations/literature.md` and its two Wu 2026 abstract leads
remain as recorded.

## Credit

- **H:** the entire expansion, sharp bounds, FDD, cutoff and transfer.
- **Parent and prior I340:** continuous modification, uniform transfer, and the uniformity
  inspection.
- **BGSS:** the GRR route, cutoff exponents, and the fourth-moment shape.
- **Garsia–Rodemich–Rumsey (1970); Billingsley (1999), Thm 3.1, 7.3:** standard tools.
- **New here:** Lemma A (the time-translation averaging in H's chart), Corollary A′, Prop. B
  without rᵋ, Lemma R and Prop. C (the colliding-particle count closure), and the assembly.

The time-translation idea is elementary, and its use elsewhere in the literature has not been
checked. No worldwide-priority claim is made for the mechanism itself.
