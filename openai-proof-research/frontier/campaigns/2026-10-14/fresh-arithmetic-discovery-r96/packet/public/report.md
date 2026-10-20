# Arithmetic r96: public report

**Outcome.** PREFREEZE. There is no frozen target, no author proof and no nominee. No mathematical gate, contribution gate or count is assigned.

**Runner.** Factory Droid (Opus 5.5, reasoning high). Pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

## Screened families

| Family | Direction considered | Why it stopped |
|---|---|---|
| 028 Gaussian moat (main) | A. Every positive definite binary form, every imaginary quadratic order, and real quadratic fields. B. Rank $d\ge3$: degree-$d$ fields, quaternary norm forms. | A is the source mechanism with lattice parameters substituted, plus one elementary unit-orbit separation step, so it is a parameter variant. B needs a new $d$-dimensional replacement for the two planar input lemmas of `lem:enrichment`, which is unbuilt. |
| 001 Milne rationality | Products of K3 surfaces, abelian-motive varieties, bad reduction | The first is an immediate composition with a catalogue-level companion. The other two are central gaps or outside the formulation. |
| 013 inverse Goldbach | Prime progressions; density version | The first is a parameter variant. The second needs a new robust supply mechanism. |
| 207 idempotents, char $p$ | $p$-adic lift to $c_0(G,\mathbb Z_p)$ | Needs a $p$-adic Bass theorem. The trace is not faithful in characteristic $p$. Central gap. |
| 067, 018, 033/034/036/056 | History only | Prior exact screens or catalogue-level compositions. |

## Main finding of the round (diagnostic, not a theorem)

In source028, everything after `lem:enrichment` is dimension-free up to constants: coverage transfer, schedule and information budget. So are `prop:periodic` and the arithmetic inputs, after Chebotarev. Only two lemmas are planar:

- **`lem:differences`.** In $\mathbb Z^3$, the three-segment path $S_1\cup S_2\cup S_3$ of $3m$ unit steps has $\lvert E-E\rvert=O(m^2)$. Its differences of differences contain all lattice points of $[-m,m]^3$ outside two open octants. A volume or union-bound exclusion therefore runs at entropy rate about $2/3$.
- **`lem:rectangle`.** Two vectors in an index-$p$ sublattice $\ker(a\cdot x\bmod p)$ of $\mathbb Z^3$ have cross product $\equiv\lambda a\pmod p$, not $\equiv0$. So the unique-witness-line partition fails.

A collision-counting replacement needs $\Pr(u\in\Lambda_J)\le P^{-1+o(1)}$. The crude divisor bound loses $P^{\theta}$ with $\theta$ near $1/4$ in the schedule's middle band. Details are in `route-028.md`.

These are method diagnostics. They do not refute the rank-$d$ moat or any other proof of it.

## Why the round stopped

The rank-two extension of 028 is closable, but it is a parameter variant of the source mechanism, which the campaign calibration (i256) rates TECHNICAL. The rank-$d$ extension is a genuinely different integrated problem. Its missing operation, though, is a wholly new geometric enrichment, and the full source schedule would then have to be rerun at new rates. That is not a closable compatibility step within this round. The other screened directions are compositions, parameter variants or central gaps. Freezing any of them would lower the threshold, so no scope was frozen.

Reading extents, timing and the one pre-seal correction are in `reading-limits.md`. Other screens are in `screens.md`.
