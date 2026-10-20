# Arithmetic r96 handoff

PREFREEZE: no frozen target, no author proof, no nominee. No mathematical gate, contribution gate or count is assigned.

Runner: Factory Droid (Opus 5.5, reasoning high). Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

## Main direction: source028, Gaussian moat beyond $\mathbb Z[i]$

Two extensions of the bounded-step-walk theorem were tested against the full source mechanism.

- **Rank two** (every positive definite binary form, every imaginary quadratic order, real quadratic fields with a unit-orbit separation step). This is the source mechanism with lattice parameters substituted. Under the i256 calibration it is a parameter variant, so it was not frozen.
- **Rank $d\ge3$** (degree-$d$ fields, quaternary norm forms). After `lem:enrichment`, the coverage transfer, schedule and information budget are dimension-free up to constants, and so are `prop:periodic` and the Chebotarev inputs. Only the two planar input lemmas fail:
  - `lem:rectangle`: in an index-$p$ sublattice of $\mathbb Z^3$ the cross product of two members is $\equiv\lambda a \pmod p$, not $\equiv 0$, so the unique-witness-line partition is lost.
  - `lem:differences`: the three-segment path has $\lvert E-E\rvert=O(m^2)$; its differences of differences miss two open octants of $[-m,m]^3$, so volume or union-bound exclusion runs at entropy rate about $2/3$. A collision-counting substitute loses about $P^{1/4}$ in the schedule's middle band.

  The missing operation is a new $d$-dimensional enrichment followed by a rerun of the whole schedule at new rates. That is not a closable compatibility step, so nothing was frozen.

These are method diagnostics. They do not refute the rank-$d$ statement or any other route to it.

## Other screens

- **001 (Milne rationality):** products of K3 surfaces is an immediate composition with a catalogue-level companion; abelian-motive varieties and bad reduction are central gaps or outside the formulation.
- **013 (inverse Goldbach):** prime progressions are a parameter variant; a density version needs a new robust supply mechanism.
- **207 in characteristic $p$:** needs a $p$-adic Bass theorem, and the trace is not faithful; central gap.
- **067, 018, 033/034/036/056:** history only (prior exact screens or catalogue-level compositions).

Remaining low-history families were not screened. No exhaustion or worldwide-priority claim is made.

Read `packet/public/report.md`, `route-028.md`, `screens.md` and `reading-limits.md`. One pre-seal correction to `route-028.md` (the cube claim) is disclosed in `reading-limits.md`.

## Inventory

- 10 retained pinned source bodies (028, 001, 013), all blob-checked against the complete preprints tree; 7 fetched-but-unread bodies removed, with hashes registered.
- No primary literature; navigation items are listed in `external-navigation.json`.
- 11 unchanged history and handoff copies, including the r95 family history-count table.

## Seal

The exact packet manifest SHA256 is 2c98e55d63617c227a6fd577d4eeffda2812ed631d4257a9b38b5d7e25a0a98a.

`FINAL.json` binds this outside report, the manifest, the verifier, the controls script and the public report. Take its detached hash from the parent handoff. Run the read-only verifier and the copied controls as described in `packet/public/reproduction.md`. `integrity-results.json` is written outside the packet and must be hashed separately. These artifact checks are not mathematical gates.
