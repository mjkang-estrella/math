# H018 initial diagnostic: fixture search exhausted, no feature evidence

2026-10-08. Status: **INCONCLUSIVE**. Root executed the frozen diagnostic ONCE
after independent protocol and full-source review. There was no numerical
warmup, off-ledger fixture search or control run. It exhausted the declared
96-order-test selection limit before finding an eligible full-prime-order curve.
No primitive root, controls or feature prefixes were computed. Consequently
this result supplies NO sparse-power exclusion, random-null evidence,
asymptotic conclusion or ECDLP improvement.

## Exact command and provenance

Working directory: /home/mj-kang/Documents/Dev/math/dlp-research.

    timeout --signal=KILL 60s python3 research/experiments/H018/bm_probe.py --approved-execution > research/experiments/H018/initial_results.json

Process exit0; the JSON status, not exit0, determines the research result.
`status=inconclusive`; halt reason is
`fixture not found: global 96 order tests exhausted`.

SHA256 at execution and checked afterward:

- Source bm_probe.py:
  `0865eac9be57655ec1ddde3d76f2aba79bff91ea5384110a7d2205041a764da7`
- Frozen protocol H018-bm-probe-v1.md:
  `6aea6695ec278f0804dcea3361a52d8d494bb1a3cf9f5559e73e74822a31094f`
- Output initial_results.json:
  `fc52157f888da32181c0b1ad749a965cc5539cf06f0e95fdefd26a00ee7843a0`

The output stores39 ordered prime candidates (excluding q=p=8191), the three
selected starting points, all96 projective endpoints, phase/category counts,
and the protocol hash. No inverse/log table or feature data is present.

## Observed work and scope

Total71755 bounded-word modular RAM events: selection14835 plus order tests56920.
The candidate curves b1 and b3 each used all39 q candidates; b2 was rejected by
the frozen rational2-torsion check; b4 used the first18 candidates before the
global selection counter stopped. All96 endpoints had Z≠0.

Neither the one-million-event cap nor the time guard was hit. The recorded
time before JSON encoding was0.029313264996744692 seconds, an instrumented local
diagnostic observation, NOT a curve-work throughput or hardware benchmark.
No event count is compared with H014's different accounting model. Observed
maxima were25 events/double,32/ordinary addition and676/scalar call; the last
is an observed maximum on these inputs, not a universal upper bound.

## Independent recorded-data audit

Native Sol `/root/h010_early_dependencies` read the saved data and source,
confirmed all three hashes, ordered candidate/test schedules and category sums.
Recorded scalar bit lengths/popcounts imply1192 doubles and653 ordinary adds;
their formula/loop/record costs reproduce every order-phase category exactly.
Verification-only arithmetic checked the three recorded affine starting-point
equations and96 recorded Jacobian endpoint equations. It did NOT recompute
the scalar multiples, generate another point or search another curve.
The audit passed at this precise scope. It cannot supply a missing feature
certificate or turn selection failure into a negative about the hypothesis.
The exact independently executed Python audit body is retained as
research/experiments/H018/audit_recorded.py. Reproduction command from the
project directory: `python3 research/experiments/H018/audit_recorded.py`.
This is saved-data verification overhead, not another charged candidate run.
Root retained the command and original PASS output without rerunning it.

## Next decision

No automatic rerun or feature/threshold change. A separately reviewed extension
of the PUBLIC fixture search may be considered because no feature outputs were
observed; it must charge the prior71755 events plus repeated setup within one
cumulative event cap, retain this failure and explicitly state any time-budget
change. The first run remains inconclusive regardless of a later outcome.
The main research goal and square-root reference remain unchanged.
