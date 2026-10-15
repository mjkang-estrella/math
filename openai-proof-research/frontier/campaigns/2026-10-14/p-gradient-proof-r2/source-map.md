# Round-2 source map, exact interfaces and reading limits

2026-10-14. Companion to [review.md](review.md). Every SHA-256 is in [input-hashes.json](input-hashes.json). Pinned truth is stipulated at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` (`sources/upstream.json`, 3784eb61…). Round-1 pinned-interface readings and live-fetch hash matches are inherited from [../p-gradient-proof/source-map.md](../p-gradient-proof/source-map.md). This round re-fetched no pinned source.

## Repaired argument: the four bound texts

| Role | File | Reading |
|---|---|---|
| Original full argument (frozen) | `frontier/experiments/i345_lifted_p_gradient_research/analysis.md` | complete, §§1–11; **untracked in git at HEAD caf19c07** |
| Repair response | `p-gradient-parent/proof-repair-addendum.md` (d3ff16a1…) | complete; diff against the committed f0386a3a… version: only the R1 status sentences changed |
| R1 supporting proof | `p-gradient-uniformity/lemma.md` (06452273…), with `reading.md`, `manifest.json` and `insertion.md` | all four complete; every manifest hash matches the files |
| I236 written dependency | `p-gradient-manuscript/viscous-appendix.tex` (1685cc94…) | complete, compared line by line with I236 |
| Explicit M₀ bounds | `p-gradient-parent/ellipticity.md` (f4ea3e49…) | complete |
| Round-1 review | `p-gradient-proof/review.md`, `source-map.md` and `checks/algebra_checks.py` | complete; script rerun |

## Internal dependency

- **I236** `analytic-attempt.md` (a30077ca…): read completely, §§1–8, and re-derived §§2–6 at operation level.
  - Interface: for m≥1, 0<τ<∞ and C₀≥0, every V∈C(R^m×R) solving D²V[(D_xV,1)]+τΔ_xV=0 with all-center, all-radius sheared FIT is affine.
- **I239** `analytic-check.md` (5ed6e0bf…), `reviews/i239-viscous-rigidity-proof.md` (51e8ebf7…) and `iterations/i239-viscous-proof-parent-disposition.md` (bf335a6f…, hash only): the first two read completely. They were used to confirm which expansions the appendix should carry (P4–P5), not as a substitute for re-derivation.

## Primary classical sources (exact pages read this round)

| Source | Bytes used | Exact interface | Read this round |
|---|---|---|---|
| Uhlenbeck, *Regularity for a class of non-linear elliptic systems*, Acta Math. 138 (1977) 219–240 | `p-gradient-uniformity/sources/uhlenbeck.pdf` = `/tmp/frontier-typeset/uhlenbeck.pdf` (bb041a82…); OCR layer `uhlenbeck.txt` (42625055…), re-extracted with `pdftotext -layout` to identical bytes | (1.3), (1.3)′, (1.4); Thm (1.10); (2.1)–(2.5); (3.1)–(3.3); (4.1)–(4.15); Prop (5.1); Thm (5.4), (5.5); Thm (6.1). Scalar case: ρ=Q^s, s=(p−2)/2, C=0 | full text of Sections 1–6 (OCR). Rendered pp. 221, 232, 233, 234, 235 and 238 inspected; for these the formulas were read from the image, not the OCR. pp. 223–231 and 236–237 read in OCR only, where some formulas are garbled. Also not rendered by me: the pp. 230, 237 and 239 images from the R1 audit. |
| Savin, *Small perturbation solutions for elliptic equations*, CPDE 32 (2007) 557–578, author copy | `/tmp/frontier-typeset/savin.pdf` (e575cc88…, 137567 bytes) | H1–H4 (for \|p\|,\|z\|≤δ only); Thm 1.3 (‖u‖_{C^{2,α}(B_{1/2})}≤δ); Prop 4.1 (r₀ depends on δ, K and universal constants; sequence F_k with ‖D²F_k‖≤K); Cor 3.3 (universal β, c₀) | rendered pp. 558–560, 569–573; pdftotext for pp. 557–560. **Not read:** pp. 561–568 (proofs of Thm 1.1, Lemmas 2.1–2.3, Prop 3.1) and pp. 574–578 (Section 5 applications). |
| Kotschwar–Ni Thm 1.1 | — | as quoted in round-1 review A | not re-read this round |
| Juutinen–Lindqvist–Manfredi; Julin–Juutinen (equivalence; Remark 3.3) | — | as round 1 and I236 | not read (U4) |
| Crescimbeni–Forzani–Perini (linear Harnack) | — | weak-solution Harnack and continuity | not read; cited through I236 and the appendix |
| Sánchez-Morgado (exponential structure) | — | appendix's citation for the flux | not read; not load-bearing |

## Formal support

`campaigns/2026-10-14/formal/`: `README.md` (69ff2abc…), `validation.json` (4d007b8a…), `FrontierSupport/LiftedEllipticity.lean` (20b41178…), `FrontierSupport.lean`, `Audit.lean`, `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`.

- The Lean source was read in full and re-elaborated from a /tmp copy with the repository's Lean 4.34.1 binary (`dlp-research/.tools/lean-4.34.1-linux/bin/lean`), against the existing package oleans.
- Its three theorems use only the standard axioms.
- No lake command was run in `formal/`, and nothing was written there.
- The examined `Audit.lean` (3d78a0cb…) and `FrontierSupport.lean` (50685a06…) equal the `validation.json` record. The parent changed both concurrently after examination, and added `VectorEllipticity.lean` (3a58a1a9…). Those new bytes are unexamined.

## Excluded and unread by instruction

- `p-gradient-manuscript/main.tex`: hash recorded at review time only; it changed during the session because it is authored concurrently.
- `large-viscosity.tex`, `scales-and-limits.tex`, `references.tex`, `README.md`, `submission-scope.md`, `validation.json` and `output/pdf/main.pdf`: not opened.
- `viscous-appendix-typeset.tex` (1daca7fa…): hashed only. A `diff` line count of 8 against the reviewed appendix was taken without reading the content.
- `p-gradient-parent/contribution-screen.md` and `p-gradient-contribution-r1/`: novelty material, out of scope, not opened.

## Scratch work

These files live outside the repository in `/tmp/r2work/`:

- re-extracted Uhlenbeck and Savin text;
- rendered Savin pages;
- mutation copies of the check script;
- a copy of the round-1 script;
- the Lean source copy `LE.lean` (78b8b950…; it differs from the repository file only by two appended `#print axioms` lines).

Nothing was written in the repository outside `p-gradient-proof-r2/`.
