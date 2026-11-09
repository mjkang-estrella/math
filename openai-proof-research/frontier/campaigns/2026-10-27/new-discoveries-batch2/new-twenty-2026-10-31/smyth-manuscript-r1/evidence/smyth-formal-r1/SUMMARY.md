# Smyth formalization handback

Completed the Lean formalization lane for MathDB 332037. Status: pending root review; no acceptance and zero credit claimed.

- Endpoint: `Smyth1512.not_conjecture15 : ¬ Smyth1512.Conjecture15` in `src/Endpoint.lean`.
- Literal universal definitions preserve the source quantifiers and domain-dominates-image orientation.
- The eight-generator down-set has checked cardinalities |S| = 1137 and |T| = 1134 at (A,a,B,b) = (3,20,2,19).
- Non-increasing rearrangement is proved sorted and a permutation. A nonempty identity-injection instance supplies the non-vacuity control.
- Fresh extracted replay: all 48 modules compiled with warnings as errors, and all 48 explicit-module leanchecker calls passed. Logs are in `replay/logs`; the driver transcript is `logs/fresh-replay-driver.log`.
- Endpoint axioms: propext, Classical.choice, Quot.sound. Local declaration metadata: no flags. Mathematical source scan: clean.
- Maximum per-call observed RSS: 2032588 KiB; maximum CPU time: 5.62 seconds. Every call ran under the prescribed watchdog, affinity and limits.

Deliverables: `source-only.zip`, `PROOF.md`, `STATEMENT-CORRESPONDENCE.md`, `REPRODUCE.md`, `results.json`, and full replay logs. Source zip SHA256: `82e134f245cd795d51695f1a1be8a15b4167212ff4742d18f2a2f0c5ce7ac0c2`.

Development limitations and failures are recorded in `logs/development-incidents.md`, `logs/CountsTest.log`, `logs/Audit-before-structural.log`, and `replay-failed-structural/logs`. No resource limit was increased. The final enumerator uses Nat.rec directly to avoid compiler-generated unsafe recursion helpers.

Root must reconcile the independent source-fidelity review and novelty requirements before any acceptance. This lane used only cached source material and did not inspect the published journal body.
