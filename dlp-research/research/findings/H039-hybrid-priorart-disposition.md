# H039 hybrid prior-art gate: known ingredients, conditional opening only

2026-10-08. Raw Claude Opus5.5 report in H039-hybrid-priorart-opus-raw.md.
Root inspected the primary passages below and assigned native Sol a separate
cost/scope qualification, now completed and confirming the corrected scopes. No numerical experiment or new Lean claim. The raw
three-digit hand estimates are not accepted quantitative thresholds here.

## Supported prior-art connection

[Kuhn–Struik, SAC2001, Section4](https://link.springer.com/content/pdf/10.1007/3-540-45537-X_17.pdf)
reuses distinguished points from solved logarithms, converting their labels to
known logs and detecting collisions with new target walks. Root freshly read
Section3 assumptions and Section4 through the urn analysis. The paper models
successive collisions and states its multiple-target approximation in a
restricted target-count regime. This is direct prior art for combining known
logs with new walk relations. It is not a theorem about this project's cheap
fixed progression table, negation walk, or full memory/cost contract.

The elementary ideal analogue is transparent: with b forbidden stored states
in a uniform N-state urn, t fresh independent draws avoid both the table and
each other with probability product_{j=0}^{t-1}(1-(b+j)/N). For b,t=O(sqrt(N)),
its leading exponent is -(bt+t(t-1)/2)/N. A uniform negation-quotient idealization
N approximately q/2 gives the H039 leading exponent. This derives an ideal
urn expression, not independence or mixing of an actual EC walk; useful
coefficients, infinity, cycles and reporting remain separate requirements.

[Bernstein–Lange, cuberoot, Section2](https://cr.yp.to/dlog/cuberoot-20120919.pdf)
describes stored traps checked by wild walks, ordinary BSGS memory tradeoffs,
and distinguished-point reporting. Root's web fetch failed; primary-site
curl plus pdftotext succeeded with lines190–280. Together with the previously
checked H019 block arithmetic, this establishes known components. The exact
asymmetric-price blend was not identified in the reviewed sources. Neither
novelty nor exact prior publication of that complete blend is established.

## Cost qualifications

The valid admission inequalities remain symbolic:

    P < [cw*(g(0)-g(beta))-cb*beta]/g(beta)
    (cw+P)*g(beta) < cb/(4*beta)

for comparison with the ideal no-table rho and the stated static signed-BSGS
invoice respectively. Other costs and stronger feasible controls still apply.
The report's approximate beta interval, six-percent ceiling and P/cw=0.07
cutoff depend on selected arithmetic prices and comparators. They are not
general gates, measured values or proof of hardware impracticality. No claimed
cache/DRAM latency or field throughput was measured. Fixed beta>0 does imply
square-root record storage; it does not itself establish a machine-capacity
threshold. Full H019 cannot be admitted merely because the cap exceeds
0.2 sqrt(q): its declared peak is about sqrt(2q) records plus workspace.

For amortized use, an online comparison alone is insufficient. H015 records
Bernstein–Lange's approximate setup sqrt(q*M) and online sqrt(q/M) under its
walk assumptions. Comparing this online term with q/b without matching setup,
memory and target count does not prove universal domination. Likewise
sqrt(2*cb*(cw+P)*K*q) follows by balancing cb*b+K*(cw+P)*q/(2b) only in a
regime where the large-beta approximation is valid and the balanced b fits.
The exact ideal shared-baby invoice is
sqrt(q)*(cb*beta+K*(cw+P)*g(beta)). The large-beta balance needs an inactive
cap and valid distinct-table range (for example K growing with K=o(q), plus
lower-order ancillary costs). Shared-table BSGS optimizing at beta=sqrt(K)/2
also needs that growing table to fit. Neither optimized expression is the
constrained finite-K invoice. No multiple-target
negation constant is accepted from a bare extrapolation of the source theorem.

Nonrandom transitions can affect both table hits and self-collisions; the claim
that they reduce ONLY the t² term is unproved here. Fingerprint false-positive
recovery cost depends on the specified record/reconstruction design and need
not always be a scalar multiplication. These are costs to specify, not reasons
to fabricate either an advantage or a universal rejection.

## Decision and next work

Park this known-components hybrid as a conditional, restricted-memory,
single-target constant-factor candidate. No exponent or complete-runtime gain
is supported, and no new run is admitted. A particular implementation could
reopen the gate only with a declared memory budget, justified useful-walk law,
and plausible matched full-cost ledger. Existing H034 cap remains consumed.
Broader independent H040 ideation proceeds; the final scope critic confirmed
the corrected record.
Verified improvement NONE; working baseline exponent1/2 unchanged.

Exact new source command:

```
curl --fail --location --max-time 20 --silent https://cr.yp.to/dlog/cuberoot-20120919.pdf | pdftotext -layout - - | sed -n '190,280p'
```

Kuhn–Struik primary PDF opened with web, Sections3–4 located/read there. No
primary PDF or generated data added to the repository. Validation result and
live review IDs are retained in STATE.md.
