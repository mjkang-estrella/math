# Four-variable floor-sum certificate closure

Independent computational certificate: PASS in the local full-rule run; `final-verification-receipt.json` records the separate authoritative replay status. All 12,459 used proof rules are validated without Z3 or another SMT solver; no unsupported rule remains. The proof root is false with no remaining hypotheses. See `PROOF.md`, `check.py`, `query-map.json`, `dag.jsonl`, and `partial-check.json` (historical filename, now containing the full checker result).

The literal theorem is the independent Wong JIS 2018 p.15 four-variable bound S >= -3 floor(m/3), for every positive integer m and indexed a_i,K in [0,m-1]. The all-parameter floor-to-clamp correspondence, sorting, remainder variable, empty subset, equality thresholds, H=m and m=1 are proved in PROOF.md. This does not resolve full Conjecture 17. The 2017 predecessor does not settle this lower endpoint.

This is a computational proof, not Lean, a human-only proof, campaign acceptance, or a novelty clearance. An independent reviewer must audit the implementation and soundness explanation. Prior/eligibility remain HOLD. Counts remain 9 additional / 39 total / next 40; root alone accepts and counts. No Lean, manuscript, Git, public, MathDB, browser, shared-ledger or other-lane changes were made.

Sources, query, original solver scripts/status/checks, proof object and provenance were frozen before scientific inspection. `bindings.json` binds all original/copy pairs and their hashes. Final verification checks originals and copies before and after replay. The final manifest excludes itself and `final-verification-receipt.json` only. Existing immutable reference paths are retained without copying entire historical trees.

Access: this lane made no network requests. It reused the actual primary PDF bodies lawfully retrieved in r241 on 2026-10-30. Denied GitHub, ScienceDirect and challenge routes and inaccessible historical intervals remain parked. No current-registry or exhaustive prior-art clearance is claimed. Exact URLs, hashes and chronology are in `SOURCE-PROVENANCE.md` and the frozen receipts.

Two early diagnostic executions were stopped after shared-DAG formatting expanded subproofs rather than rendering them boundedly; failure files are preserved. A stricter per-rule BDD budget and bounded rendering fixed this. Arithmetic validation initially depended on an incomplete elimination order; bounded alternative orders now independently validate every arithmetic lemma. No resource cap was raised. The final separate guarded verifier is the authoritative execution receipt.

The first final-replay implementation hit MemoryError while copying growing lexical environments. `final-replay-initial-failure.json` preserves its guard failure. Persistent lexical scope sharing fixes the representation cost without changing semantics or raising the caps.
