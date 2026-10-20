# fresh-arithmetic-discovery-r99 — outside report

Runner: Factory Droid / claude-opus-5-5 / high. Campaign 18/20. Pin
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

## Result

**Full author-proof nominee at the unchanged frozen scope** (family 164,
positive characteristic). No correctness, contribution, acceptance or count is
assigned here.

Frozen 2026-10-20T17:20:23Z, before proof development:
`freeze/scope-freeze.md`, SHA-256
`2a39e2a3410a79812e3e48478fa892d507e163fcd739fd409173219c7c5a23b7`
(copied byte-for-byte to `packet/public/scope-freeze.md`).

- **Theorem F.** Every infinite field `K`, every `r, n ≥ 1` and every
  `χ: K^x → [r]`: there are pairwise distinct `x_1,...,x_n ∈ K^x` with all
  nonempty subset sums nonzero and `χ` constant on all nonempty subset sums
  and subset products.
- **Corollary G.** For each prime `p` and `r, n` there is `d` such that the
  same holds in `F_{p^m}` whenever `d | m`.

Proof: `packet/public/proof.md`.

## Strongest integrated reduction and what was unpaid

Characteristic 0 follows from Alweiss over `Q` (arXiv:2307.08901v6, Theorem
1.3). Large characteristic follows from that by the first-order compactness
argument of Bowen–Sabok (arXiv:2210.12290v1, §4.3). The pinned source proves
the statement over `N` with nilsequence machinery that does not transfer;
structural r130 judged that characteristic `p` would need that machinery over
function fields. Unpaid before this round: fields of a fixed small
characteristic, for example `F_2(t)` and the algebraic closure of `F_2`.

The proof re-derives Alweiss's Proposition 4.1 over an arbitrary infinite
field. Bergelson–Leibman Corollary 7.11 (any infinite ring) replaces integer
polynomial van der Waerden. Backward-chosen finite sets plus topological
compactness of colourings replace Alweiss's height bounds and Hunter's
characteristic-0 finiteness step. Nondegeneracy uses an isolated zero colour
and a `ψ(2z) ≠ ψ(z)` colouring (or `2z = 0` in characteristic 2). Alweiss §5
Ramsey/Folkman selection finishes, as in the source's `lem:chain-selection`.
Corollary G is a König-type compactness over `F_{p^{j!}}`.

## Risks and limits

- The argument transports Alweiss's method; reviewers may judge it routine.
  This report takes no position.
- Novelty is limited to six web searches and the primaries listed;
  Bergelson–Leibman–McCutcheon (2005) and function-field Ramsey literature
  were not read.
- Corollary G covers only `m` divisible by `d`. No bounds.
- Bergelson–Leibman's PHJ proof was not read; Corollary 7.11 is used as
  stated.
- Lemma 4 identities were also checked by random evaluation over several
  fields, including characteristic 2 and 3. That is not a proof.

## Reads and timing

Root created 16:55:27Z. Source 164 introduction read in full and
`02_framework.tex` lines 230–319. Alweiss v6 §1–§6, Bergelson–Leibman
§0.13–0.18 and §7.9–7.15 and §8.7–8.8, Bowen–Sabok introduction and §4.3,
Hunter §1–§2.2 and the Lemma 6.1 sketch, Kousek abstract and §1.1, Alweiss
2211.00766v4 introduction. History: r98 parent assessment/intake, r98 screens
and reading limits, structural r35 `mixed164.md`, arithmetic r94 and
structural r130 other-screens. The full list is in
`packet/public/reading-limits.md`. Families 200, 005, 179 and others were
screened at the depth stated in `packet/public/screens.md`.

## Provenance gaps

An author scratch file `/tmp/x` was written outside the root and deleted at
once (about 16:55:49Z). The harness saved some command outputs under
`/tmp/droid-terminal-*`. A context compaction happened during navigation;
reading extents from before it are stated conservatively.

## Sealing

`packet/MANIFEST.json` records every packet file. `FINAL.json` binds the
manifest, verifier, controls, public report, proof, frozen scope and this
REPORT. The detached FINAL and REPORT anchors are given in the final handoff,
not in the packet. `packet/code/verify.py` is read-only.
`packet/code/controls.py` replays it on mutated copies and writes
`integrity-results.json`. These are artifact checks, not mathematical gates.
