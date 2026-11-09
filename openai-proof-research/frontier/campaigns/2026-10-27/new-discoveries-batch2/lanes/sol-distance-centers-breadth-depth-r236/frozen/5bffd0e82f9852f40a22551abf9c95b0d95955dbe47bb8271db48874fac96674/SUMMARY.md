# Stolarsky stabilization and conditional literal-source transfer

PASS for this conditional integration component; no full SourceClaim or gap monotonicity proof, no acceptance, credit 0. Counts remain 3/30 additional and 33/60 total.

Import `Transfer` and use namespace `LogArctangentSource`. The checked endpoint is

```lean
sourceClaim_of_strictMono_gap
  (hmono : StrictMonoOn centeredLogGap (Set.Ioi 0)) : SourceClaim
```

`SourceClaim` is the frozen root proposition, byte-identical, including both parameter branches and every distinct positive pair in either order. The endpoint has no stabilization, homogeneity, representation or residual algebra hypothesis. The only remaining substantive premise is the strict centered log-gap monotonicity. This lane does not prove that analytic premise and does not use the parallel analytic worker's files.

`Stolarsky.lean` defines d, alpha, beta, the generic diagonal-extended Stolarsky function, fixedS and the genuine centeredLogGap using the frozen literal mean. `fixedS_formula` identifies fixedS with the requested expression with exponent 1/d; `fixedS_self` gives the diagonal. Parameter bounds, positivity, symmetry, positive homogeneity, the literal mean/log-ratio rewrite, the generic power identity, generic stabilization, and BOTH fixed-parameter stabilizations are proved. The negative branch uses the proved swapped-parameter/inverse-rpow identity; no positivity of the outer exponent is assumed. Real power injectivity is used with a nonzero exponent and positive bases.

`Transfer.lean` proves the geometric-center/half-loglength representation for arbitrary positive inputs. Homogeneity gives the exact log-ratio identity; strict gap monotonicity gives both strict subinterval comparisons. Strict internality of Bq ensures both subinterval lengths are positive and smaller than the whole length. Positive scaling, the frozen strict coordinate monotonicity for every nonzero exponent, and the internally proved stabilization give the strict resultant inequality. Symmetry covers the reversed input order. The internal generic `transfer_of_stabilization` exposes a stabilization premise for reuse, but the exported SourceClaim endpoint discharges it separately for both branches.

The optional sinh/arctangent centered rewrites and optional between-power-means sandwich were not added. CenteredLogGap itself is the literal exp/log expression requested, with no surrogate analytic definition. These optional rewrites are not assumptions of the endpoint.

## Validation and reproduction

Pinned Lean binary SHA256 e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550 was independently read and checked. Mathlib detached HEAD was read directly as d13f23b723b8a846827a245b89c10fc7d3f11612; no git operation was used. `formal/run_lean.py` is byte-identical to the supplied runner. `formal/MeanSourceDefs.lean` has SHA256 6a64dfdbc059d35dbdf8985660fc0bd61ef60d7e4f1246829cc68c139ad64db3.

Fresh replay began with only source files and the supplied runner, with no local oleans copied. It compiled MeanSourceDefs, Stolarsky and Transfer serially, then audited all 50 declarations (20 frozen and 30 authored, definitions included) using explicit full `#check @...` and `#print axioms`. All actual types and axiom outputs were inspected. Every declaration uses only propext, Classical.choice and Quot.sound. Both authored modules enable warningAsError=true and autoImplicit=false. There are no proof placeholders, custom axioms, unsafe declarations or computational trust shortcuts. Imports are targeted; only the frozen source module and its existing six Mathlib imports are required.

Run from this lane:

```
python3 replay.py
python3 compile.py fresh-source-replay -o MeanSourceDefs.olean MeanSourceDefs.lean
python3 compile.py fresh-source-replay -o Stolarsky.olean Stolarsky.lean
python3 compile.py fresh-source-replay -o Transfer.olean Transfer.lean
python3 compile.py fresh-source-replay Checks.lean
python3 finalize.py
```

`replay.py` intentionally refuses to overwrite an existing replay directory. For a subsequent replay use a new source-only directory and pass its relative name to compile.py. Lean receives a sampled process-group RSS ceiling of 3 GiB, a 180-second wall deadline per command, and BLAS/OMP/MKL/NumExpr thread counts of one. Every final replay command exited 0; peak sampled group RSS was 2,650,677,248 bytes, below 3 GiB. Diagnostic preparation/finalization scripts use a hard 512 MiB address-space and 45 CPU-second budget; Lean uses its separate RSS budget. These are sampled RSS measurements, not a claim about unsampled instantaneous maxima.

Development failures are retained in logs: wrong `Ne.symm`/negative-division names, a beta-reduction mismatch in rpow injectivity, denominator normalization, unused/unnecessary tactic lint errors, and an attempted division-inequality rewrite before moving the factor into the numerator. All were corrected; no linter was disabled and no resource limit was increased. One exploratory rg used a nonexistent optional hyperbolic-import path and returned status 2; it supplied no mathematical dependency. No exact numeric diagnostic is used as a proof.

Full supplied PROOF.md, AUXILIARY.md, SOURCE-REVIEW.md, root ADOPTION.md, SOURCE-COMPONENT.md and receipt, and the full investment review were read. The source/review claims are context, not extra trusted Lean premises. Frozen inputs were read only. All writes are confined to this lane; no children, git operations, external communication, browser tabs, posts or uploads occurred.

The strongest remaining gap toward the unconditional source conjecture is precisely `StrictMonoOn centeredLogGap (Set.Ioi 0)`. This component supplies the entire classical stabilization and source transfer once that premise is proved. It is a formal integration helper and receives no separate candidate credit.
