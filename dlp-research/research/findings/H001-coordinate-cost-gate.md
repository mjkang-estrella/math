# H001.1: concrete relation-generation costs and remaining known candidates

Sol primary-literature exploration completed; no supported improved algorithm.
Coordinator adopts the following scoped implementation gates, not universal
coordinate lower bounds. Associated reproduced experiment: H001-relation-rank-falsifier.md.

For B=q^(1/5+δ), 0≤δ<1/20, under the optimistic uniform-sum heuristic:

| Implementation | Charged work for about B relations | Decision |
|---|---|---|
| Shared pair table, random triple probes | B² preprocessing/storage; q/B² probes per relation; total q/B | Exponent4/5−δ loses |
| Precompute shared triple table | B³ construction/storage before queries | Exponent3/5+3δ loses |
| Fix four coordinates, factor univariate S6 | Optimistically q/B trials per relation, q overall, plus factoring | Loses |

These models require their relation distributions and yield assumptions; duplicates,
dependent rows and sign recovery only add work. They do not prove that every
algebraic extraction or probabilistic coordinate filter must enumerate these sets.

## Known explicit mechanisms with unresolved solver costs

1. [Petit–Kosters–Messeng, PKC2016 author manuscript](https://people.maths.ox.ac.uk/petit/files/16PKC_primeECDLP.pdf):
   compose low-degree auxiliary-isogeny maps to structure a factor base; form
   actual S3-chain equations and membership constraints; solve, extract signs
   and verify point relations. Denominators must be excluded. Auxiliary trials,
   point counting/kernel checks/maps, lifts and subgroup checks cost work.
   Store elimination matrices and polynomial bases as well as factor-base points.
   A useful ledger is P_aux+P_base+(cB/η)(C_solve+2C_scalar+C_verify)+C_LA,
   where η counts failures and rank/recovery/retries are explicit. The concrete
   solver needed to beat the historical tB+B² threshold remains missing.
2. [Amadori–Pintore–Sala, 2018 primary manuscript](https://pure.tue.nl/ws/files/91158650/609.pdf):
   random labelled factor-base points a_iP+b_iQ and a one-shot signed zero relation
   remove the large linear-algebra stage. If Σ ε_i b_i≠0, recover
   d=−Σ ε_i a_i / Σ ε_i b_i mod q and verify. But high-degree membership solving,
   failed attempts and target-dependent base generation must be charged. Plain
   joins do not establish a sub-square-root result. This is prior art, not novelty.

The sparse-linear-algebra component also requires an actual algorithm and its
probabilistic conditions; see [Wiedemann's primary paper](https://www.enseignement.polytechnique.fr/profs/informatique/Francois.Morain/Master1/Crypto/projects/Wiedemann86.pdf).
Naïve Semaev complexity analyses with statistical assumptions are not universal
impossibility theorems; [primary conference manuscript](https://nutmic2019.imj-prg.fr/confpapers/SemaevECDLP.pdf).

Sol reports inspecting PKC, APS and the naïve-analysis manuscripts; original
Semaev PDF fetch failed, abstract available at https://eprint.iacr.org/2004/031.
Root's initial alternative PKC-host fetch failed; no invented retrieval success.
Search results or abstracts for other recent proposals do not supply a validated
matched classical bound and are not used as evidence of novelty or impossibility.

## Decision

No new relation extraction mechanism clearing the full-cost gate was found in
this bounded exploration. Known structured elimination remains an open candidate,
not an accepted attack. A future test must specify the inspected solver, compare
five-point structured/unstructured systems on ordinary target curves, and count
all preprocessing/failures/matrix memory. No such replication is launched merely
to fill the gap; broad independent H002 ideation proceeds first. No generic Lean
refinement is necessary for this rejection. Reference square-root work unchanged;
verified improvement NONE.
