# Literal four-projection source endpoint

**Implemented and strictly compiled: the actual projection-level inequality, with no residual frame, spectral, injectivity or analytic hypothesis.** This is a solo implementation lane, not independent review, a paper, acceptance or a discovery-count claim. Additional accepted count remains 0/30; the first thirty are untouched. Published-body and novelty HOLD remain unresolved.

The two new production declarations in `formal/SourceEndpoint.lean` are:

- `FourProjection.four_projection_inequality`, which omits both rank balances.
- `FourProjection.banica_nechita_conjecture_6_6`, which takes both source balances using ordinary `Matrix.rank` and forwards the stronger result.

Exact stronger endpoint (inside `namespace FourProjection`, with `{N : Type*} [Fintype N] [DecidableEq N]`):

```lean
theorem four_projection_inequality
    (P Q R S : Matrix N N ℂ)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (hR : R.IsHermitian) (hS : S.IsHermitian)
    (hPP : P * P = P) (hQQ : Q * Q = Q)
    (hRR : R * R = R) (hSS : S * S = S)
    (hPQ : P * Q = 0) (hRS : R * S = 0)
    (hPR : LinearMap.range P.mulVecLin ⊓ LinearMap.range R.mulVecLin = ⊥)
    (hQS : LinearMap.range Q.mulVecLin ⊓ LinearMap.range S.mulVecLin = ⊥) :
    let X := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) (P + R)
    let Y := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) (Q + S)
    let P' := X * P * X
    let Q' := Y * Q * Y
    let R' := X * R * X
    let S' := Y * S * Y
    (Matrix.trace (P' * Q' + R' * S')).re ≤
      (Matrix.trace (P * R + Q * S)).re
```

The source wrapper has all the same hypotheses and conclusion, plus exactly

```lean
(_hRankPQRS : P.rank + Q.rank = R.rank + S.rank)
(_hRankPRQS : P.rank + R.rank = Q.rank + S.rank)
```

`Matrix.rank A` is the finite dimension over ℂ of `LinearMap.range A.mulVecLin`. There is no alternate surrogate rank. The type `N` may be empty. There is no positive rank, nonempty dimension, ambient inverse, supplied frame or extra hypothesis. The two new boundary declarations in `formal/SourceBoundaryChecks.lean` instantiate zero-rank projections in arbitrary ambient dimension and arbitrary matrices with empty ambient type through the actual source wrapper.

## Integration argument

For each original Hermitian idempotent, use `projectionFrame hP` and the corresponding constructions for R,Q,S. `projectionFrame_isometry` supplies all four isometry equations. `projectionPairFrame_injective` supplies the two concatenation injectivities from the literal source range intersections. `projectionFrames_cross_eq_zero` supplies the two cross-Gram zero blocks from PQ=0 and RS=0. Instantiate `four_frame_inequality` on those four internally constructed frames; rewrite each `projectionFrame_mul_adjoint` equality, then unfold `mpInvSqrt`. The result is the displayed CFC expression of the original P,Q,R,S. There is no remaining bridge to supply.

The CFC scalar function is the positive inverse square root on positive eigenvalues and zero at zero. The copied spectral and kernel theorems prove this convention, including singular sums. The exact cached arXiv source, printed page 20, was both text-read and visually checked. `source/SOURCE-FIDELITY.md` documents the six source hypotheses and mappings; `source/frozen-proof.md` is the unchanged root ordinary proof.

## Verification

**Fresh strict replay PASS: 16 modules; 157 actual environment declarations, including 123 manually named public declarations, 2 private helpers and 32 generated declarations. Only propext, Classical.choice and Quot.sound occur.** Both source endpoint proofs were fully printed with no elision markers.

The machine-readable final replay status is `verification/result.json`; extracted implementation-packet status is `verification/packet-result.json`. Reproduce using:

```sh
python3 scripts/replay.py
python3 scripts/packet.py
```

The replay rebuilds all local Lean modules in an isolated fresh directory using the absolute Lean 4.34.1 executable and pinned mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. It uses `-DwarningAsError=true`, rejects forbidden proof tokens, enumerates actual environment declarations by defining module, and checks all axiom reports against only propext, Classical.choice and Quot.sound. It includes every manually named definition/theorem, the `ProjectionFrameIndex` abbreviation, `projectionFrameIndex_fintype` instance, both private CFC helpers, and generated named auxiliaries. It uses pinned built mathlib dependencies; it does not rebuild upstream mathlib.

`verification/fresh/Inventory.log` contains actual readable types and axiom reports; `ExplicitInventory.log` contains explicit types and all implicit arguments; `EndpointPrint.log` contains the actual endpoint proofs, definitions and ranks; `EndpointExplicitPrint.log` contains fully explicit endpoint proof terms. The replay rejects elision markers in the full prints. The packet is only an implementation artifact, not the eventual root paper/proof packet.

## Exact file hashes

Fourteen support/boundary modules were copied byte-for-byte. Every common module available in the frame-assembly, range-frames and root integration lanes was compared and found equal. **No conflict fixes or changes to copied modules.** `provenance.json` gives original absolute paths, every equivalent path and hashes. Only SourceEndpoint and SourceBoundaryChecks are new Lean modules.

| Lean source | SHA-256 |
|---|---|
| BoundaryChecks.lean | `01f9ad467d4ae0e2cfb48cd5bc1817678d6b8212c2ceb0b213c91d0fd3007690` |
| ContractiveBridge.lean | `e7e85271a6ab96dba389a54b6650bed5a346505badff195236021d319e9a9813` |
| FrameBlocks.lean | `576e6e08ef2fe0be0b17f11e27db5817a1ffe083847e73f685114176cf45acc0` |
| FrameBoundaryChecks.lean | `2a6ec0919171e4ff3102ca07f9c624af3e26c7c11829cc03c5ec9347c2eb5087` |
| FrameInequality.lean | `ded3cb6483c82457f1aa9792c01333a02ab69ec738d9d4f2f190873d65e3c546` |
| FrameReconstruction.lean | `e3741147ccdaf95f6f7b28c0434e6dfa889059fac033047a18b79c3ad2e8b802` |
| GradedSpectralBridge.lean | `ac8a1c8f2e2ed201c2b7c51c03b462cbf6125529adad26c93517d341641983ab` |
| GradingConsequences.lean | `ff43ea2e3aabc36cafb1268fc52c6f09f8357fa0eb07d7036206d5cf4acc0265` |
| HSBridge.lean | `caab8950954d1819e8eded7153268da3588e2a5d904ace357269b2b08c8eb61e` |
| PolarFrameBridge.lean | `9b6535642f304bdd89a981c2cfaa37cb1a7eaf5647b3ddf4e96f93ae0ce1d52d` |
| ProjectionFrames.lean | `62d6cda1b1251d38c26f99e0dc90f468ce6f4039b7243f9603e5790a1682df2b` |
| RangeFrames.lean | `756972b2b259853b0436cd1a7e5214a6b68b04743567a839793537de476519e4` |
| ScalarCore.lean | `65a556a34508c7ad742797a2106a2083f079a1a82bf0c93e56a34c59f9cb060e` |
| SourceBoundaryChecks.lean | `6897f8762f4e3ab870aa1ee4a23916535132e1e80bb5240645f36d0cc16ebcbd` |
| SourceEndpoint.lean | `fb0f9f53cfd90ea99472839b67254b387d73baf7d6fa2235b494307e3610afd8` |
| SpectralCore.lean | `2167d40a807acdc1faf1860198edc6af8bc72faf65b113a9459c9d12208b7966` |

## Remaining root gates and strongest objections

`verification/OBJECTIONS.md` records the normalization, hidden-premise, pairing/constant, rank/empty-dimension, inventory and provenance attacks. The formal endpoint is ready for independent integrated review; this implementation self-inspection is not independent review.

Root still needs: actual published-journal body comparison; bounded novelty/subsumption clearance with its documented access/coverage gaps; independent source/mathematical/full-formal review of the final integrated code and types; paper preparation and review; the final root deterministic paper/proof packet and extracted strict replay; and an explicit acceptance/counting decision. The prior source-novelty lane retains both published-body HOLD and novelty HOLD. A successful formal proof clears neither. At most one four-projection family outcome may be counted, never separate credits for rank removal, helpers or boundary cases.

The frozen 46-entry root manifest was rechecked without mismatches. Work was solo and all writes were confined to this assigned lane. No git, shared ledger, other lane, public posting, external messages, account actions or access-control bypasses were performed.
