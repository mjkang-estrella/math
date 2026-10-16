# Provenance and boundary

Task: independent adversarial PROOF review, round 1, of the frozen candidate
`frontier/campaigns/2026-10-14/fresh-structural-discovery-r3/` (candidate.md
SHA256 `e3f4c65e5eb0f35e9d19090e0ba897b27219a223795a0569319a3114cb3babcc`,
seal SHA256 `75df70d930c3ccd57287e76a082dab1885bb844b0691132201ce2d4a199684e4`).
Author of record: Myeongjin Kang, no affiliation. Review date 2026-10-16.

Owned writes: only `frontier/campaigns/2026-10-14/poly-zp-proof-r1/`. No
nested agents, shared edits, staging, commits, acceptance, counting, external
messages, uploads, publication or submission. The candidate directory was
only read; tamper tests used disposable copies inside this directory, which
were deleted afterwards. The sibling `poly-zp-contribution-r1` directory was
deliberately not read, to keep this review independent.

Pinned source: `openai/math` at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`,
stipulated true; only interfaces were checked.

## Explicit read extents

Frozen candidate (all 94 files authenticated in place by `inputs-manifest.json`):

- Read entirely: `candidate.md`, `README.md`, `RIGHTS.md`, `provenance.md`,
  `literature.md`, `source-contracts.json`, `retrieval-literature.json`,
  `checks.py`, `checks.json`, `verify.py`, `outputs-manifest.json`, `seal.json`.
- Parsed programmatically: `retrieval-upstream.json` (all 39 rows, blob
  cross-check; rows for 04/05 displayed); `inputs-manifest.json` via the
  candidate verifier.
- `inputs/.../Cyclic-Length.../sections/05-profinite.tex`: entire file,
  all statements and proofs (`thm:procyclic`, `lem:profinite-elementary`,
  `lem:shrinking-action`, `lem:lattice-limit`, `lem:kernel-abelianization`,
  proof of `thm:procyclic`, `cor:rational-gluing`, `lem:product-series`).
- `04-congruences.tex`: lines 160-380 (`lem:hom-integrality`,
  `thm:subgroup-congruence` with proof, `eq:transitive-coefficient`), plus a
  label listing of the whole file.
- `01-introduction.tex`: lines 120-140, plus label/term search. Other
  sections of the family 314 build: label/term search only.
- All other candidate inputs (context snapshots, other preprints, GRV,
  Kisilevsky, Tamanoi, Davison-Mandel, Frenkel PDFs/TXT): authenticated by
  hash only; not re-read (their content is summarized in the candidate's
  `literature.md`, which was read).
- `LICENSE-MIT` of the candidate: header lines only.

Mutable project files read during review, hashed at read time (not
re-authenticated by `verify.py` because the parent may legitimately update them):

| path | bytes | SHA256 | extent |
|---|---|---|---|
| AGENTS.md | 1298 | e9ab951853e1607e8d125adb5609a89214a46bb655fda39874257b8210093e7e | entire |
| sources/upstream.json | 179 | 3784eb61f1efa141ed49d00c5d13a5206502c4081759abff4f64c99183b5f30c | entire |
| sources/preprints-tree.json | 4858136 | eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b | parsed for blob identities |
| frontier/NEW-TEN-2026-10-14.md | 19425 | e0a65de230e1d6fe237dcf7dde76c24ff5c913d28c0ec0541d9cb330ef6adf02 | lines 240-253 and term search |

Project HEAD observed at inventory time: `a9acfe2cf9ba0e1ad10d24ce71de55e2b91acea1`
(it was `157421b5` at session start; the parent committed meanwhile).
Accepted finding records were only term-searched (Z_p, pro-p, subgroup
count, poly-Z_p, procyclic): no hits in `frontier/findings/`.

New primary source: Frankel (2016) dissertation, see
`retrieval-literature.json` for URL, hash and read extent.

## Inventories

`inputs-manifest.json`: 97 entries (94 candidate files in place with
`root: project`, 3 private literature files with `root: review`).
`outputs-manifest.json`: every other file of this directory except the
manifests and `seal.json`. `seal.json` binds both manifests; its detached
SHA256 is reported in the handoff. `verify.py` is read-only and has no
sealing or receipt-writing mode.
