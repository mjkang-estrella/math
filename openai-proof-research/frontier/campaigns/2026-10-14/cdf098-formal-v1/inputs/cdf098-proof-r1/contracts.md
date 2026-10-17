# CDF098 proof review r1 — exact contracts, dependencies and read extents

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

Paths are relative to `frontier/campaigns/2026-10-14/fresh-parent-discovery-r8/` unless stated. Source pin: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The source blobs were checked against the complete `sources/preprints-tree.json` (SHA256 `eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b`, `truncated=false`).

## Read completely
- `candidate.md` (lines 1–86) and `original-scope.md` (lines 1–18).
- `manifest.json`, `verify.py` (also executed with the external anchor), `source-receipt.json`, `context-receipt.json`, `status.json`, `checkpoint.md`, `RIGHTS.md`, `private/README.md` and `private/primary-receipt.json`.
- `family-inventory.json`: the first 20 lines were read. The verifier checks the whole file.
- `AGENTS.md`, and `frontier/campaigns/2026-10-14/cdf098-parent/proof-r1-brief.txt`, which is identical to the task brief.

## Read partially
- `private/main.tex`:
  - lines 30–52: the doubling and distortion definitions, the problem context and `thm:main`;
  - lines 53–80: the proof strategy, with lines viewed truncated at 200 characters;
  - lines 81–136: the construction and the complete `prop:doubling` with its proof;
  - lines 412–492: the section intro and the complete `cor:banach` with its full proof.
  - In addition, grep hits showed every `\label` and every line containing "doubling", including line 28 (abstract) and line 390 (`cor:lp` statement).
- `reading-and-comparison.md`: all 41 lines, but each line was viewed only up to 400 characters. It bears on contribution only and is not a proof input.
- `frontier/campaigns/2026-10-14/ab194-proof-r1/`: read only as a packet-format template, not as mathematical input.

## Not read
- `private/main.tex` lines 137–411: the derivative, energy and crossing nonembedding proof, plus `cor:lp` and its proof. These lie behind the stipulated `thm:main`, and the review does not need them.
- The source PDF. It is not in the packet.
- All primary PDFs and texts: Gupta–Talwar v1/v2, Schul, and Semmes (which is scanned). None of them is a proof premise.
- `cdf098-contribution-r1/`. Only its directory listing was seen, and no verdict from it was used.
- I88 beyond the excerpt embedded in `context-receipt.json`.

## Imported or stipulated contracts (exact use)
| Label | Status | Exact use |
|---|---|---|
| source `thm:main` | stipulated true at the pin | S⊂ℓ_2 is 76800-doubling with centers in S, and S has no bi-Lipschitz embedding into R^k for any k≥1 at any finite distortion. Distortion is defined with a free scale a (source lines 33–37). |
| finite-witness extraction (proof of `cor:banach`, l.425–435) | stipulated true at the pin; credited | For each j∈N there is a finite X_j⊂S with \|X_j\|≥2 and no embedding into R^j of distortion ≤j. |
| Classical Dvoretzky ([Dvoretzky §7], [COO Thm 1.1], as cited by the source at l.439) | imported classical theorem | For every n and every infinite-dimensional real Banach B, a linear map ℓ_2^n→B exists with distortion <2. It is applied with n=dim span(G_j). |
| Equivalence of finite-dimensional norms | standard | Turns an arbitrary finite-dimensional target into Euclidean R^k at finite distortion. |
| Source Y_j transfer, cluster separation and tail-ball arguments (l.445–487) | credited, and independently redone in review.md | They are applied to G_j and C_j, with the extra spine portion. |

## New deductions, all independently rederived (review.md)
- Lemma 1: the height-separated net graph, together with its ambient 256D^10 doubling bound.
- The λ² doubling bound for X_j and the normalization.
- Dvoretzky applied to the whole graph span, and Δ^4 doubling for Y_j.
- Placement of the clusters and the spine.
- Compactness.
- The Lipschitz tour parametrization and H¹<∞.
- Γ-doubling with Λ=10+6Δ^8.
- Nonembedding, including the zero-dimensional target.
