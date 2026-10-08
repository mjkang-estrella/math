# H001.2: delayed canonicalization fails the present decision gate

Verdict: reject the proposed schedule as currently justified; no demonstrated
end-to-end improvement. This is not an impossibility theorem for block walks.
Native Astra proposed/analyzed; Claude Opus independently criticized; coordinator
reproduced the arithmetic and reviewed the assumptions. No Lean claims added.

## Mechanism and baseline

The candidate makes t additions between canonical representatives, t=1,2,4,8.
At each block boundary multiply both point and scalar coefficients by the same
automorphism multiplier. The partition must depend on the mathematical point,
not incidental projective coordinates. Count table construction (including any
target dependence), coefficient updates or replay, cycles, failed denominators,
restarts, distinguished-point storage and final scalar verification.

Compare against the applicable existing automorphism-aware rho, not plain rho.
The usual heuristic useful-iteration scale is sqrt(pi*q/(2*h)), with orbit size
h and separate real costs. It is not a deterministic bound or GPU benchmark.

## Failure of the shortcut

Equal interior points at the same phase can coalesce; orbit-equivalent points
need not. In Z/11, C(x)=min(x mod11, -x mod11) and f(x)=x+1 give C(1)=C(-1)=1,
but C(f(1))=2 and C(f(-1))=0. Thus a boundary quotient map does not justify
retaining every micro-step's quotient collision advantage. This is a finite
counterexample to that inference, not an EC runtime experiment.

For a diagnostic model of independent uniform maps on N points with equal-size
classes h, a distinct input pair has endpoint orbit-collision probability
`1-(1-1/N)^t + (1-1/N)^t*(h-1)/(N-1)`, approximately `(h+t-1)/N`.
Converting this two-input calculation to a rho trajectory runtime needs further
assumptions about dependencies, cycles and collision detection. Actual EC
orbits also have exceptional sizes. No such runtime theorem is asserted here.

Under that additional heuristic, with addition/partition cost A and separately
removable canonicalization cost C, the relative work is
`sqrt(h/(h+t-1))*(t*A+C)/(A+C)`.

| h | t | Addition ratio | Break-even C/A |
|---|---|---|---|
| 2 | 2 | 1.633 | 3.449 |
| 2 | 4 | 2.530 | 4.162 |
| 2 | 8 | 3.771 | 5.243 |
| 6 | 2 | 1.852 | 11.481 |
| 6 | 4 | 3.266 | 12.348 |
| 6 | 8 | 5.435 | 13.832 |

These are model arithmetic, not measured EC costs or lower bounds.

[Bernstein–Lange–Schwabe, PKC2011](https://www.iacr.org/archive/pkc2011/65710132/65710132.pdf)
describes an optimized negation walk and reports under4% iteration-cycle cost
for negation-related work, including cycle handling. This applies to their
historical implementation/curve/hardware. It is not a current order-6 measurement.
Even removing all that work at unchanged walk length would miss our10% objective
on that baseline. The point representation also serves partitioning; its cost
cannot simply disappear while retaining an unchanged free partition.

## Reproduction

Original command: `timeout 60 python3 /tmp/H001_delayed_gate.py > /tmp/H001_delayed_gate.json`.
Coordinator copied the exact artifacts to research/experiments/H001 and ran:

```
timeout 60 python3 research/experiments/H001/delayed_gate.py > /tmp/H001_delayed_gate_reproduced.json
cmp research/experiments/H001/delayed_gate.json /tmp/H001_delayed_gate_reproduced.json
```

Both exited0, byte-identical output. Script SHA256:
`5029172cc96d84e367dd80e2d932e3f953332117b449bf04d5ecfeeff402b8c0`.
Output SHA256:
`f374fa6b58d066d7f518693525e32639f5b0340d0e1d6fec5c009b0f14c735f0`.
No random seeds: deterministic arithmetic only, zero synthetic EC runs.

Opus additionally reported a936k-event Z/262139 toy, but supplied no artifact
path in its final report. Those timings/counts are retained as unverified in
H001-opus-critic-raw.md; they are NOT used as reproduced evidence or an EC
comparison. Its order-6 overhead estimate and quantitative divergence assertion
are likewise not adopted. Agreement between reviewers is not a proof.

## Next conclusion-changing test

A new schedule needs an explicit coalescence/collision model and measured
separately removable canonicalization headroom in a specified optimized order-6
baseline before a matched complete-run scaling experiment is justified. No
generic machine refinements or larger simulation is funded for this rejected
version. Best supported reference remains square-root work; verified improvement
NONE. Coordinate-aware relation generation remains the active distinct candidate.
