# H030 C2 diagnostic: correct checked outputs, finite work/cycle losses

2026-10-08. Root admitted the sole command in H030-c2-admission-r2.md, then ran:

    timeout 60s python3 -B research/experiments/H030/c2_probe.py --execute > research/experiments/H030/c2_result.json

Shell exit0; experiment status INCONCLUSIVE_CAP, exactly1,000,000 events.
Recorded elapsed-before-encoding1.5564881829777732s is this diagnostic's own
Python time, NOT a curve throughput or256-bit benchmark. No reset/rerun/warmup.
Inner event guard caught termination during the eighth case's initialization;
no source/reference/Miller/recovery mismatch was reported. Source remains
dbfe5d542f726ab589c72fb0f185977a2fde4d1aa58f217515dc197169341c2a.
Protocol/support hashes match the admission. Both category and phase sums equal
1,000,000. Cap termination is not global success despite process exit0.

## Saved evidence

Raw JSON:6,085,395 bytes, SHA256
2d817c40eca05d3a9d98d35e217efd1dc89f91968fe7a17b87d644d8eafba867.
Lossless deterministic gzip (level9,mtime0):362,772 bytes, SHA256
f549054a0e543a426d6396e416478915e31384995b8a52beb3628fd14d317220,
committed at experiments/H030/c2_result.json.gz. Expanded JSON is ignored locally.
Decompression/data analysis is not a new solver experiment. Restore exact bytes:

    gzip -dc research/experiments/H030/c2_result.json.gz > /tmp/H030-c2-result.json
    sha256sum /tmp/H030-c2-result.json

Archive was generated after the run with Python gzip.compress(data,
compresslevel=9,mtime=0), preserving all failed/partial work and traces.

## Outcomes

Seven target cases completed all per-arm diagnostics. Candidate solved5/7;
control solved7/7. These fixed cases are NOT iid success-rate samples.

| q | seed | candidate committed steps / outcome | control committed steps / outcome |
|---:|---:|---|---|
|73|7|3 / verified DP recovery|3 / verified ring recovery|
|73|19|3 / verified DP recovery|12 / verified DP recovery|
|103|7|0 / verified initial identity|0 / verified initial identity|
|103|19|12 / verified ring recovery|3 / verified identity recovery|
|271|7|50 / all four null-ring retirements|1 / verified ring recovery|
|271|19|18 / verified DP recovery|4 / verified ring recovery|
|8053|7|69 /32 rounds, three null retirements|58 / verified DP recovery|
|8053|19|CAP during candidate initialization|not started|

The eighth case stored two candidate starts; only the first completed reference
validation and no terminal checks completed. It has no stopping comparison.
The precise cap site was independent reference Miller checking of the second
start, during an inverse with9M/10S already paid. Those partial operations stay
raw, with no completed-I substitution. Outer case status input_construction is
stale; pending=candidate plus arm/trace markers give the actual interruption.
Initial-identity case q103/seed7 supplies no transition-kernel evidence. Targets
were sampled over the declared full nonzero range, never replaced for difficulty.

All completed arms have four checked terminal states and start references.
Native Astra independently checked saved scalar-label/duplicate/cached-x and
terminal-label consistency; no fresh search or EC trial. Per-arm committed
counts equal summed walker counts; paid batch outputs equal committed plus
overshoot. Exactly two false-h matches occurred, both q271/seed7 candidate.
No completed candidate recorded a nonidentity zero-h output. Direct exceptional
checks cover support functions only, not unobserved candidate paths.

All four formal tables retain145 entries. Distinct point counts are61,79,111,145;
identity-entry counts3,3,1,1. Duplicates were paid and retained, not pruned into
hidden inverse advice. These very small groups do not predict full-size mixing.

## Matched complete recorded work under equal unit event prices

Full applicable setup is attributed to EACH single-target sheet. All expanded
field/integer/array/record/comparison events have weight1 in this particular
RAM price model. Diagnostic-only reference/certification work is excluded from
solver sheets but included in the global cap. No hardware equivalence claimed.

| q | seed | C first verified stop | B first verified stop | C solver end | B solver end |
|---:|---:|---:|---:|---:|---:|
|73|7|39,401|21,890|39,409|21,898|
|73|19|40,759|24,754|40,767|24,763|
|103|7|42,599|26,895|42,602|26,898|
|103|19|44,383|25,515|44,392|25,523|
|271|19|53,715|37,432|53,723|37,441|

These are the five matched verified first stops, not an average omitting failures.
Solver-end totals include3–9 further scheduling events after verification;
they are retained rather than omitted from complete-work reporting. Candidate
solver-end ratios are about1.435–1.800 times control under this unit model.
Candidate failures additionally paid65,106 events (q271/seed7) and103,717
(q8053/seed7); partial eighth candidate sheet68,635. Retain them separately;
they cannot be converted into successful-solve costs. Global work is not the
sum of attributed sheets because shared setup and diagnostics have different
accounting purposes.

The saved symbolic operation vectors allow other explicit weights. In these
matched cases candidate Fp arithmetic/I projections are lower, but metadata
and indexing/record work are higher. That restricted arithmetic comparison
omits necessary costs and includes different r8/r32 setup; it is NOT a verified
whole-solver gain. The complete symbolic condition remains sum w_i*C_i <
sum w_i*B_i with every required cost assigned, plus success limitations.

Reproduce equal-unit rows from saved data (does not run the candidate):

    python3 - <<'PY'
    import gzip,json
    r=json.load(gzip.open('research/experiments/H030/c2_result.json.gz','rt'))
    for f in r['fixtures']:
        for c in f['cases']:
            if c.get('matched_first_stop_comparison_admissible'):
                first=[sum(c['arms'][a]['first_verified_stop_single_target_expanded']['total_vector'].values()) for a in ('candidate','control')]
                end=[sum(c['arms'][a]['actual_or_partial_single_target_expanded']['total_vector'].values()) for a in ('candidate','control')]
                print(f['fixture'][3],c['seed'],first,end,end[0]/end[1])
    PY

## Disposition

This falsifies guaranteed success of the literal four-start policy on these
fixtures and loses all five matched complete-cost comparisons under equal
unit event prices. It does not reject h-based orientation or tag tracing in
general. No iid law, asymptotic failure rate, or256-bit memory price follows.
The finite implementation checks pass where completed; overall run is partial.
Verified improvement NONE; generic exponent1/2 reference unchanged.

No automatic rerun, seed replacement, cap increase or cycle-policy retuning.
Before any new test, require a concrete paid transition-index/cycle-handling
contract with a credible complete-cost premise against a competent matched
baseline. Otherwise park this literal configuration and explore other mechanisms.
No generic Lean infrastructure or hardware extrapolation is warranted.

Independent saved-evidence review: native Astra verified transitions/labels/
overshoot/coverage, native Sol reconstructed attribution and I projections from
recorded counters and checked Miller normalization identities. Both PASS in
that limited scope, with overall cap/incomplete status retained. Neither reran
the probe, imported it, recomputed an EC search or changed the evidence/source.
