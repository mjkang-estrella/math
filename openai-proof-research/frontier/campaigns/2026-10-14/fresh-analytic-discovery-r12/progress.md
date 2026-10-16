# Fresh analytic discovery r12 — progress log

Author: Myeongjin Kang (no affiliation). Original prose CC BY 4.0; code MIT.

## Checkpoint 0 — continuity and inventory (early status)

- Read AGENTS.md, sources/upstream.json (pin fd4aeeb2…), CONTENTS.md family
  headings, complete preprints-tree.json (13,223 entries, `truncated: false`).
- Read the mandatory continuity brief salem-sextic-parent/r2-brief.txt
  (SHA256 6516059b…b504) in full, including the embedded r10/r11/Coulomb
  history and parent responses, and the current ledger NEW-TEN-2026-10-14.md.
- Excluded lanes retained: Salem T (no third attempt or adjacent degree/seed
  reformulation), Coulomb P, Spin Q4, B, EPnI, Randers, reconstruction, C, U,
  H, signing, BG4, Liouville, directed mixing, FK F/G and alpha=1/2, Artin,
  Poly-Zp, SAT, ball-slab, Bell, scalar variance, W11.
- Rough usage screen: preprint directory names cited in project markdown
  outside bulk inventories. Family 374 (Sharp one-third stability of Brenier
  maps) has no project use beyond inventories. Selected for screening.

## Checkpoint 1 — source reading (family 374)

Fetched the pinned build sources (7 TeX/bib files + README); all Git blob
identities match preprints-tree.json. Read every section in full:
introduction (main:stability), sharpness (cells:optimality,
sharpness:exponent), cells (cells:calculus, cells:weights), moments
(moments:derivative, moments:midpoint), finite_stability
(finite:potentials and the cube remark), gradient (gradient:interpolation,
gradient:finite, gradient:extension, proof of main theorem).

Status: screening in progress.

## Checkpoint 2 — scope frozen

Literature screen recorded in `literature-screen.md` (Wang–Wang
2610.09640 intro and Theorem 1; abstracts of Mérigot HAL, Ford, Ruan
2610.07577; observatory README; catalogue grep). Located the three uses of
uniformity in the pinned proof. Froze Theorem LC (log-concave sources with
compact convex support, explicit constant independent of `inf f`) in
`original-scope.md` before writing proof text.

## Checkpoint 3 — proof attempt

- Weighted midpoint domination (Lemma 4.1): the Knothe Jacobian product
  becomes `alpha / f(X)`; AM–GM plus midpoint log-concavity gives the exact
  constant. Remark 4.2: exact domination for all ball pairs forces
  log-concavity of a continuous density, so the bounded-density class is
  left out of scope as planned.
- Moment estimate (Proposition 5.1) re-run with constant 162; algebra
  rechecked line by line.
- Gradient interpolation without a lower density bound (Lemma 7.1): on
  each coordinate slice, `t -> log g(t+h) - log g(t)` is nonincreasing, so
  forward differences on an initial segment and backward differences on a
  final segment leave an exceptional set of length at most `h`. Constants
  18 and 52.
- Cell calculus, prescribed masses, finite potentials and approximation
  re-run with weight `f` (continuity of `f` on `int K`, `Lambda < inf`).
- Pure-Python sanity checks (evidence only): slice bound max ratio 0.0565
  over 300 trials; moment ratio max 0.242 against 162 on four accepted
  2D configurations.

## Checkpoint 4 — packaging

`candidate.md`, `source-contracts.md`, `RIGHTS.md`, `README.md`,
`status.json`, `git-identities.json`; context snapshots under
`inputs/context/`; manifests, verifier, receipt, seal.
