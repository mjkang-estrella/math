# Two further substantive matrix outcomes

Both packages give full counterexamples to distinct primary-source conjectures outside the inherited twenty IDs and the earlier extension IDs. Their mathematics was already available in their cited primary source or posted solution; no discovery or first-formalization claim is made.

| MathDB | Package | Complete outcome | Pinned audit |
|---|---|---|---|
| 358595 | `quadratic-difference/` | The real symplectic plane and p=q=X²+1 refute equivalence between ordinary and symplectic quadratic differences; final theorem is on actual linear endomorphisms | PASS, 26 declarations |
| 381863 | `symplectic-orbits/` | Exact nonsingular 6-by-6 forms have every source Pfaffian invariant equal but different symplectic congruence orbits | PASS, 45 declarations |

Each package contains `formal/<module>.lean`, `outcome.json`, `main.tex`, `PROOF.md`, `source.json`, and the pinned verifier's complete `build/` audit. All local declarations compile warning-free with Lean 4.34.1 and only standard logical axioms. `sources/` has the complete posts and primary manuscripts, including the posted proofs; each package's provenance JSON inventories its used snapshot hashes. Preserve these snapshots when packaging the outcomes separately.

Source caveats are prominent: 358595 is already explicitly disproved by de Seguins Pazzis in the cited manuscript; 381863 concerns the primary's nonsingular skew-symmetric forms despite MathDB's erroneous word “symmetric.” The latter certificate verifies equality with both the printed raw permutation-sum convention and the usual normalized Pfaffian convention.

No PDFs were authored; parent handles rendering and production. Independent review is still required before counting. No agents, git changes, or shared index edits were used in this lane. `PfaffianTest.lean` is a disposable discovery experiment, not part of either outcome.
