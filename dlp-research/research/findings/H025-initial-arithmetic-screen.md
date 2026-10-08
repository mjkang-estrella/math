# H025 initial finite arithmetic screen

2026-10-08. Conditional algebra from already-recorded results, no new experiment.
Native Sol proposed this screen; root independently parsed the existing JSON and
checked exact rational arithmetic. NEW independent Astra artifact/arithmetic
review COMPLETED, GO with the conditional scope below. No measured
hardware weights, no complete-work or asymptotic rejection.

Use the literal H025-frontier-cost-bridge.md schedule with k=ell=1 and the
hypothetical ratios S/M=4/5, I/M=8. Ordinary per-key cost is Cx=112M/15; the
first centered block of each reached B family adds fork cost14M/5. The control
has one positive frontier and no corresponding two-frontier fork. All advances
are charged before checking the block, including terminal advances.

From the first four B blocks, the sum of reach probabilities is1877/509 and
3870/1009. Let Nc,Nb be the recorded control and B mean numerators. Before
setup, exceptions and other work, the5% credit from key counts is

    credit = (19*Nc-20*Nb)/(20q) *112M/15.

|q|credit in M|B fork in M|credit minus fork in M|
|---|---:|---:|---:|
|509|137732/12725|26278/2545|6342/12725|
|1009|203308/25225|10836/1009|-67592/25225|

The1009 residual is negative (about-2.68M); the509 residual is only about.50M.
Suppose B's extra initialization cost relative to the control is nonnegative,
and other overhead gives it no compensating benefit. Then the1009 result cannot
support a5% ordinary-arithmetic saving under this schedule and these weights,
even before deducting5% of shared setup/verification. This is NOT an assertion
that all real lookup/storage costs are equal or that all initializers have that
ordering. It does not reject larger sizes, different hardware weights, or an
independently specified cheaper stopping schedule. It does prevent treating
the finite5% key pass as an already-established5% arithmetic pass.

No fallback is present in these initial artifacts. A continuation must price
reached fallback and support separately; it may not omit them because these
six cases happened to complete in main. No EC p, concrete curve or throughput
measurement has been assigned to these cyclic-order coverage diagnostics.

Independent audit refinement: if all omitted costs are S_B,S_C, the exact
remaining5% margin is residual+(19/20)*S_C-S_B. The sufficient condition
S_B>=S_C>=0 makes the1009 rejection follow, but that cost ordering is NOT
proved here. Recorded first-block reach numerators were506,492,462,417 at509
and1006,992,961,911 at1009. Astra independently verified both sequences and
all fractions using only saved artifacts, without a probe rerun.
