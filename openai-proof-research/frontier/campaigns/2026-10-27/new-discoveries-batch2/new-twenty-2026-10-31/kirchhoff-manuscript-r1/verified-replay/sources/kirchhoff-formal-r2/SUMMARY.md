# MathDB 349441 — formal refutation submitted for root review

The implementation is complete and the fresh strict replay passed. This lane does not self-accept the result or change any campaign count. Credit remains zero pending root acceptance and independent review.

The witness is the simple connected graph consisting of K6 on vertices 0 through 5 and the five-edge pendant path 0–6–7–8–9–10. Lean verifies its adjacency, degree sequence, connectivity and both relevant source Laplacians. Explicit 11 by 11 rational certificates satisfy all four Penrose equations for alpha 0 and 1, and separate certificates satisfy the three group-inverse equations. Algebraic uniqueness is proved separately over the rationals and the reals. Exact scalar extension transfers the certificate equations, resistance sums and group-inverse traces to the reals.

For the primary equation (4.3)/Definition 4.5 reading,

- R0 = 370/3;
- R1 = 515538204/7137235 < 370/3.

For the secondary Lemma 4.6 group-inverse trace reading,

- R0 = 370/3;
- R1 = 1696684/14035 < 370/3.

The primary resistance is exactly Xii + Xjj − Xij − Xji. The proof does not replace the last two terms by −2Xij. The spectral endpoint uses the unique group inverse and its trace, as the assignment expressly permits; it makes no unsupported claim that the Moore–Penrose inverse equals the group inverse.

The principal real theorems are `KirchhoffReal.refuteMP` and `KirchhoffReal.refuteSpec` in formal/RealBridge.lean. Each negates `LiteralConjecture` with its respective inverse and index. This statement quantifies over every n ≥ 2, every finite simple connected graph on Fin n, and alpha in {1, −1}; it includes the ordering, equality iff regular, and existence of the defining inverse. At the witness, existence is exhibited and uniqueness forces any purported inverse in the universal claim to be the certified matrix, contradicting the exact inequality. The existential formulation avoids any default value of an inverse selector. Rational literal and choice-based formulations are also refuted.

## Validation

The source-only packet was extracted into the new fresh-extracted directory. All four proof modules rebuilt with Lean 4.34.1, `-j1 -DwarningAsError=true`, a sanitized environment and read-only pinned package cache. Leanchecker passed separately on Basic, Certificates, Graph and RealBridge. Audit.lean inspected all 176 declarations belonging to those modules, including generated declarations, and recorded their module, complete type and body AST via `value? (allowOpaque := true)`, safety/partial flags and transitive axioms. Every declaration passed; only propext, Classical.choice and Quot.sound are permitted.

Three Lean negative controls failed as required: the prior −2Xij numerical value, substitution of the group inverse for the Moore–Penrose inverse, and a unit perturbation of the Moore–Penrose certificate. None timed out or hit the watchdog. See fresh-extracted/receipts/replay.json and fresh-extracted/logs/ for the authoritative fresh-run receipts and complete audit/control output.

Every Lean and leanchecker call had CPU affinity limited to two CPUs, CPU limit 120 seconds per process, wall watchdog 140 seconds, MALLOC_ARENA_MAX=2 and a sampled private-RSS watchdog at 6 GiB. A development attempt using the broad Mathlib import exceeded the memory threshold and was killed; the log and receipt are retained. Imports were narrowed before the successful build. Final fresh checks stayed within the caps. No jobs remain running.

All 17 required read-only inputs were SHA-256 bound before and after; their copied versions are byte-identical. The mandated exact-independent.json hash matches fd1e3a116188ccee76410656252c678bffa3ba743edc5921e6d79aaf981d5f59. The prior-art gate was not repeated. The root's qualified fidelity ruling and novelty limitations remain binding. The physical Definition 4.1 is not used as an endpoint, as explained in statement-correspondence.md.

No mathematical or formal proof gap is known in the two submitted endpoints. Root acceptance, novelty adjudication and independent review remain external to this implementation lane.
