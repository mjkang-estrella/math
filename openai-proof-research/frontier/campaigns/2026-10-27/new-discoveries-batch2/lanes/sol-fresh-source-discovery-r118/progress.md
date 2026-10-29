# Guarded replay and outcome

No eligible survivor after three screens; credit0. See discovery.md for exact
quantifiers, primary comparison bodies, chronology, failures and coverage limits.
No Lean or manuscript work.

All helper commands use this unchanged guard (absolute paths):

```
python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-fresh-source-discovery-r118/checks.py
```

research.py provides freeze/audit/fetch; prepare.py extracts source text and
streams the cached complete registry trees. Its initial main-branch receipt
is intentionally preserved as erroneous, superseded only for interpretation
by registry-correction.json. Do not use that receipt as fresh HEAD clearance.
seal.py freezes original notes, compresses audit metadata, records current
context drift and emits hashes/manifest. It never edits source copies after
their source-lock is made. Run seal.py after adding any result receipt to
update only the final manifest and drift/provenance observations.

The audit's completed own stream is95.315s,334950paths,203312distinct bodies;
not inherited coverage. User-requested full historical semantic reading is
not achieved, and no positive freshness judgment depends on it. No oversized
generated aggregate is read as mathematics. Source journal challenge was
stopped. Guard resource limits are unchanged; no cap raise or Lean invocation.

Final supporting checks:39 rational identities,44 source hashes PASS;
guard exit0,peakRSS10059776bytes,wall0.040518649s. Initial seal:
guard exit0,peakRSS20647936bytes,wall1.002128856s. NEXT has expected mutable
root-context drift; immutable source copies remain unchanged. No full
historical semantic coverage or current registry clearance is asserted.

Delivery-manifest failure preserved in initial-manifest-stale.json and
manifest-failure.json: seal.py was initialization-only, so its second call
did not update bindings after summary/progress edits. The strict verifier
correctly failed at SUMMARY.md. reseal.py preserves that baseline and failed
check, verifies the unchanged source-lock, and generates the final delivery
manifest. The same strict verify_manifest.py checks the corrected packet.
