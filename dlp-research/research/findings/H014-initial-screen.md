# H014 first exact feature screen: no gross signal, no solver gain

2026-10-08. Three increasing tiny synthetic curves completed in the ONE frozen
run. Neither predeclared public feature crosses the descriptive3RMS threshold.
Best supported general ECDLP work remains the square-root reference; verified
improvement NONE. This does not prove any asymptotic feature-decay law.

## Protocol, independent code review and run

Native Astra implemented character_screen.py only; root read all source. Native
Sol independently read the complete source/protocol and approved after a minor
cap-boundary reporting fix: final completed-field counters derive from retained
terminal statuses, so a cap during a charged counter increment cannot misreport
a finished field. The PRNG's alternating low bit was corrected BEFORE execution
by the fixed output bijection state XOR(state>>16); no iid claim follows.
Syntax-only compilations produced /tmp pyc files; no numeric warmup/import test.
Mathematical preflight by Claude Opus is retained with root corrections separately.

Frozen source SHA256:
`b5ff59aec44716d5762ab8693f5603799b43031c467b33baaef8cecef6790ff5`.
Frozen protocol SHA256:
`cf60cb9c8c077d6777de08d6b41601a8cc70086c55a1067e5e2bddc98c630611`.
From dlp-research, root ran exactly once:

```
python3 research/experiments/H014/character_screen.py > research/experiments/H014/initial_results.json
```

Process exit0; JSON status COMPLETE (JSON, not exit status alone, is authoritative).
All3 fields completed, no admission failure or cap reset. 738704 nested
instrumented events; arithmetic timer0.45910616201581433 seconds, excluding
source hashing/output. This is not a throughput or ECDLP runtime measurement.
Results SHA256:
`6f9ceaedcec72bfa521d6d2bf37fa60fa4d8fa4a9fad97621b8c376094b5d41e`.
Independent native Sol recorded-data audit PASSED; no field/group rerun. It
recomputed every recorded generator/permutation sum and prefix using separate
integer-pair arithmetic, all fixed-feature/planted/covariance/even controls, null
energies and flags, and reconciled phase/category/storage totals. Its first
audit assertion mistakenly omitted one reduction per field-power call; corrected
JSON-only arithmetic gives125429 reductions=123683 basic operations+1746 initial
power reductions. This was an audit-formula error, not an experiment discrepancy
or a rerun. Root retained the compact independent audit and ran it successfully:

```
python3 research/experiments/H014/audit_recorded.py
```

This only rechecks saved integer-pair rows/counters; it never imports or executes
the diagnostic and does not recompute curve/group operations. The experiment's
global cap was not reset or used for a second campaign.

## Exact outcomes

Write zeta=exp(pi*i/3), S=A+B*zeta and c=S/(q-1). The two public features are
centered-y sign and chi6 of centered(-x/y), with the order-six character and
phase convention frozen before observations. Every nonzero scalar is included.

| p,a,b; q | G0 | admitted candidate | sign S | formal-parameter S | sign squared magnitude | parameter squared magnitude |
| --- | --- | --- | --- | --- | --- | --- |
| 59,1,13;67 | (1,29) | 13 | 8-12*zeta | -10+6*zeta | 112/4356 | 76/4356 |
| 101,2,31;103 | (0,43) | 131 | 12+8*zeta | -24+14*zeta | 304/10404 | 436/10404 |
| 251,1,4;271 | (0,2) | 4 | -8+8*zeta | 38-6*zeta | 64/72900 | 1252/72900 |

Formal-parameter zero counts are0,2,2 respectively; sign has no zeros. Relative
to the exact IDEAL signed-pair null second moment, squared ratios are
(28/33,19/33), (76/51,109/50), (16/135,313/134). All are below the frozen9
threshold. This reference is a separate randomization model, not a p-value or
a claim the LCG produces iid samples. Three seed controls are descriptive only.

All nine generator traversals passed actual group arithmetic, membership,
closure and complete-orbit checks. 2G0 and -G0 rotate the sums exactly; these
are dependent consistency controls, NOT additional independent curves. Fixed
planted point functions recover the prescribed rotated unit correlation;
the even x-control has exactly zero correlation throughout. The three shuffled
signed-pair label controls per curve, seeds7,19,43, are all retained, with no
winner/phase selection. No control crosses the3RMS descriptive threshold either.

## Work and limitations

All148 candidate attempts were charged. Field totals are83191,315299,340210
events, plus4 outer/completion events. Admission alone costs11851,199853,15253.
Public sign feature phases cost198,306,810; formal-parameter phases8481,14628,
45898. These exclude the separately recorded character setup, cache/symmetry,
orbit and validation phases; none is presented as a complete online solver cost.

Total retained algorithm entries8979 (not bytes), group calls1326, field
multiplications80671, field additions34309, field subtractions8703 and
inversions1746. Powers perform actual multiplications; call-level categories
overlap their internal work deliberately. PRNG, comparisons, table operations,
failed candidates and controls are included. Interpreter/allocator/hash internals,
fixed-size records, ledger/output bookkeeping and final serialization are
explicitly unpriced. This is a disclosed abstract event model, not bit complexity.

The curves are first admitted cases of a frozen finite search, not random-curve
samples; p/a/b/order conditions are selected, but no scalar range is narrowed.
Neither the tiny size range nor three seed controls supports fitting an exponent.
The finite data show no gross correlation requiring immediate follow-up, not
that all coordinate predictors fail. Exhaustive known-label calibration here
costs Omega(q); it is diagnostic advice, never an online inverse oracle.

No larger sweep, training run or generic Lean engine is justified by this result.
Park these two feature instances pending a concrete new reason for larger useful
correlation. H014-coset-backend-cards.md retains two real conditional recurrences,
but neither supplies a predictor or a supported full-work gain. The next result
that could change the conclusion is a new cheap information source with a paid
recovery bridge, or a genuinely favorable complete collision-search mechanism.
