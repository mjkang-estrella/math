# H025 changing-coefficient addition chains: arithmetic gate and lag-three component

2026-10-08. Native Astra proposal and independent root check. No supported
complete-work survivor and no experiment admitted. Verified improvement NONE.

A fixed target-independent signed schedule with t inspected points covers at
most t²+O(t) scalar candidates, including direct infinity. Hence uniform-target
mean outputs are at least(2/3)sqrt(q)−O(1). If EACH output costs a full batched
affine5M+S, even ideal coverage loses to H019's proved two-family coefficient:

    (2/3)*(5+s) > (2sqrt(2)/3)*(2.5+s), 0<=s<=1.

Both sides positive; squaring after cancelling2/3 yields
(5+s)²−2(2.5+s)²=12.5−s²>0. This is a literal operation/schedule screen,
not a lower bound for coordinate-adaptive or cheaper multi-output methods.

One concrete cheaper component uses full affine registers(A,B,C). Compute
D=C+A, emit x(D) and x(E) for E=C−A, retain full D, and update(B,C,D).
Both slopes share one inverse. Two slope products, two squares and D's
ordinate product cost3M+2S+I per two regular outputs. Across k independent
chains, leading per-key cost is3M+S+(I−3M)/(2k). Labels add/subtract, signed
collisions recover via nonzero denominators, and candidates require verification.
Pay all starts, exceptions, labels, tables, batching and final overshoot.

Ordinary Fibonacci gives an already-known subtraction output; lag-three avoids
that immediate duplicate. It does NOT prove favorable global coverage. At s=.8,
mean keys must be below about.819sqrt(q) to beat proved H019, .782sqrt(q) to
beat an empirical.9 grumpy comparator, and .737sqrt(q) for10% arithmetic saving
against H019. The independent-random-equation occupancy heuristic instead gives
about.886sqrt(q) and loses. No uniform initialization or anti-overlap argument
meeting these gates was supplied. No arbitrary random-label trial is admitted
merely because one local duplicate disappeared.

A future test would need fixed labels, number of chains, order, cap/fallback,
complete generation cost and exact signed candidate coverage. This is an
established addition-chain/anti-collision direction (BL sections4–6), with no
novelty or universal impossibility assertion. Keep the component without a
full-size performance claim; broader work needs a positive coverage rationale.
