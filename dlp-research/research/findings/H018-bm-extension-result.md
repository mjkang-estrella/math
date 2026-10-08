# H018 finite sparsity diagnostic: four threshold crossings

2026-10-08. One admitted extension executed; independent saved-data audit PASSED.
No ECDLP solver improvement. All four fixed features reached recurrence length64
after127 samples on the first eligible synthetic fixture. The exact claimed
exclusion is global representations with fewer than64 nonzero scalar-field
powers on THIS fixture, now independently certified.
It does not exclude64 terms, different features/curves, or asymptotic improvements.

## Execution and immutable provenance

Working directory /home/mj-kang/Documents/Dev/math/dlp-research. Exact command:

    timeout --signal=KILL 60s python3 -B research/experiments/H018/bm_probe_extension.py --approved-execution > research/experiments/H018/extension_results.json

Exit0; JSON status `completed_finite_diagnostic_only`. No repeated execution,
warmup, uncharged search or post-selection feature change. The prior failed
run remains recorded unchanged and charged. Review-only labels in source and
protocol record preparation; separate final GO/root approval is retained in
H018-bm-extension-admission.md.

- Extension source SHA256: f855b0b868fd01a9b7fcb51201bc968e5f0fe68b09491d9590acadc48907df65
- Frozen v2 protocol SHA256: c7405b4dad545348cde3ee64b735dce8343d0f7f422fe73d6f2f8d89573bc22e
- Output SHA256: acaaf3489a3a3bbddf6ae01f7980f4f79ea37ee48bfdc83f269ced9ec4ab4634

## Observations

Curve y²=x³+x+5 over F8191, full order8053, G=(0,789), w=2 primitive in F8053.
It was selected at order test121 of the extension. Factors of8052 are2,3,11,61.
The 127 shared samples feed centered x, centered y, integer kappa and centered
formal parameter; each reports L64, with all updates committed. The planted
three-power control reports L3 at16 terms; fixed LCG reports L32 at63 terms.
The LCG is not an iid null and supplies no p-value.

Current work508887 plus prior71755 = cumulative580642 events, below1M.
Phase counts: selection14985, count assertion1, order70508, primitive319,
controls28252, BM354188, features33074, orbit7560. No phase overrun or cap hit.
Recorded pre-JSON elapsed0.22632758400868624 seconds is an instrumented local
observation, not a hardware-throughput or full-solver measurement.

The event unit is the frozen bounded-word modular RAM convention; it excludes
administrative provenance/JSON and separately identified verification work.
No comparison to a differently metered baseline or hardware extrapolation.

## Independent verification and conclusion boundary

Native Sol /root/h010_early_dependencies executed ONE saved-data-only audit.
All four64x64 Hankel matrices over F8053 have rank64; the saved length64
recurrences also hold. Thus each127-term prefix has minimum recurrence length64.
A global t-power representation sampled geometrically has Hankel rank at most t,
which proves the exact t<64 exclusion without trusting the generating BM.
No new curve, sample, feature or search was generated.

Independent affine arithmetic verifies [8053]G=O; primality, nonsingularity,
Hasse condition, factors and primitive-w tests pass. Checked127 saved points,
126 recorded doubling transitions,508 feature values, and125 selection-point
and endpoint equations. Controls have independent ranks3 and32, with their
terms and recurrences checked. Category/carry sums reconcile; order, orbit and
feature category counts match the recorded schedules. Failed selection endpoints
were checked on-curve, not all recomputed as scalar multiples; this limitation
is retained. Root read the independent audit source and checked the Hankel
rank-to-sparse-power implication.

Exact verification command, same project working directory:

    timeout --signal=KILL 60s python3 -B research/experiments/H018/audit_extension_recorded.py

Exit0/PASS. Script SHA256:
10f5e84ae96199b5bcbda322838d8f864c938e23ea163c449f36d2355c6e4b79.
The already-produced output is retained in extension_audit_result.json; no
rerun to save it. Its SHA256 is
b1059a3fe8ac563dd3e0487ed7b64331692b57319c26aee4a1ae5da7ab6d1833.
Verification overhead is2887421 instrumented operations in a
DIFFERENT convention (composite assertions count once). It is additional work,
not included in the candidate580642 RAM events or1M candidate cap. Do not add
incomparable raw counts or present the diagnostic cost as including its audit.
Provenance/JSON administration is explicitly outside these event counts.
This is independently checked executable evidence, not a new Lean theorem.

No scaling experiment is justified merely by this threshold crossing. Park
these four direct sparse-power features unless a new structural reason revives
them. H018 implicit relations are independently reviewed, not automatically
added to this run. H019 independent proposals seek a concrete signal/detector
or credible complete-work gain capable of changing the main conclusion.
