# H018 finite sparsity diagnostic: four threshold crossings

2026-10-08. One admitted extension executed; independent saved-data audit pending.
No ECDLP solver improvement. All four fixed features reached recurrence length64
after127 samples on the first eligible synthetic fixture. The exact claimed
exclusion is global representations with fewer than64 nonzero scalar-field
powers on THIS fixture, contingent on the independent certificate audit.
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

Native Sol /root/h010_early_dependencies is assigned a saved-data-only audit:
provenance and ledger, certificate arithmetic, recorded group transitions and
features, controls, and independent64x64 Hankel rank over F8053 for each prefix.
No new curve, sample, feature or search may be generated. Full rank would rule
out a recurrence of order<64; a t-power representation sampled geometrically
has recurrence order at most t, so the exact finite negative follows.
This audit uses a different linear-algebra certificate from the generating BM.

No scaling experiment is justified merely by this threshold crossing. Park
these four direct sparse-power features unless a new structural reason revives
them. H018 implicit relations are independently reviewed, not automatically
added to this run. H019 independent proposals seek a concrete signal/detector
or credible complete-work gain capable of changing the main conclusion.
