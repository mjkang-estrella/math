# Arithmetic r95 handoff

PREFREEZE: no frozen target, no author proof, no nominee. No mathematical gate, contribution gate or count is assigned.

Runner: Factory Droid (Opus 5.5, reasoning high). Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

## Main direction: source041, nonprojective Kähler base

The candidate considered, and never frozen: every fibration of a compact IHS Kähler manifold (not necessarily projective) onto a normal complex space has base $\mathbb P^n$, with no smoothness assumption on the base.

Both source041 companions restrict to projective $X$: Projective-Space-Bases `thm:main` and Strong SYZ `cor:projective-base`. Every operation needed for the Kähler case is still paid:

- Greb–Lehn 1303.3919v2, Proposition 2.2: the base is projective, and the fibration is Lagrangian.
- A deformation to a projective member with the same base. Either route is paid:
  - Matsushita 0903.2098v2, Theorem 1.2 and Corollary 1.3. These were read; their hypotheses do not require $X$ to be projective. They are combined with the source's own trace-derivation local product in `def:fixed-base` (07-deformation.tex, lines 137–178), which does not use projectivity of the central fiber, and with density of projective periods.
  - The degenerate-twistor and Soldatenkov–Verbitsky fixed-base constructions, already cited in the source introduction (lines 149–158).
- Source `thm:main` at the projective member, then Greb–Lehn Theorem 1.1.

This is the Greb–Lehn template with source041 in place of Hwang's theorem. It is a routine composition, so it was not frozen.

## Other screens

- **017 (μ(π)=2):** rational-log and arctangent extensions are claimed externally (navigation-level reads only). The general algebraic logarithm is a central gap.
- **016 (Zilber–Pink):** the characteristic-zero version is the Barroero–Dill reduction, which the source already uses.
- **037 (normalized-volume gap):** the global consequence is already the source's `cor:global`.
- **062 (contact Fano):** the Kähler case with $b_2=1$ is routine; $b_2\ge2$ needs a Kähler KPSW theorem, which is a central gap.

Remaining low-history families were not screened. No exhaustion or worldwide-priority claim is made.

Read `packet/public/report.md`, `route-041.md`, `screens.md` and `reading-limits.md`.

## Inventory

- 16 pinned source bodies, all blob-checked against the complete preprints tree.
- 3 primary PDF and text pairs (Matsushita, Greb–Lehn, Campana).
- 11 context and history copies.
- The family history-count table.
- The final no-size-cutoff alias counts over 9 term groups, all with exit code 0. Hits are not semantic reads.

## Seal

The exact packet manifest SHA256 is 82237944d68b5ea200a72d8c7528c62cf8f8b3a64682c95e11430406b502bff6.

`FINAL.json` binds this outside report, the manifest, the verifier, the controls script and the public report. Take its detached hash from the parent handoff. Run the read-only verifier and the copied controls as described in `packet/public/reproduction.md`. `integrity-results.json` is written outside the packet and must be hashed separately. These artifact checks are not mathematical gates.
