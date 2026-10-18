# Cumulative winding budget: a conditional obstruction to repeating the resonant architecture

Author calculation, not an impossibility theorem for smooth flows.

In the ideal integer shear passage, old coordinates (Q,w) are replaced by new coordinates (w,b), b=Q-kw. Its induced matrix on angular covectors is

 A_k = [[0,1],[1,-k]].

If a_n,b_n are the two rows of the cumulative coordinate matrix, then a_(n+1)=b_n and b_(n+1)=a_n-k_n b_n. Starting from the identity and taking k_n>=2, alternating the signs of the rows yields positive continuants: the relevant integer sizes satisfy D_(n+1)=k_n D_n+D_(n-1). In particular D_n is at least the product of the previous k's. This statement concerns the homological linear part; periodic nonlinear coordinate terms can only require additional derivative estimates and are not discarded from an asserted full construction.

The resonant physical mode in the two-step calculation has frequency k_n in the old invariant w. After n coordinate changes, its homological covector is k_n b_n, of size at least k_n D_n. For a pure clock exp(2 pi i k_n w_n) times an amplitude that does not cancel this phase, physical derivative costs must account for this accumulated covector. A circle lift of degree D cannot have uniformly bounded first derivative below |D|; higher norm bounds cannot be estimated solely by the latest k_n.

The demonstrated stationary realization uses clock amplitude proportional to T_(n+1)^(-1/2), where T_(n+1) is the new orbit period. In the ideal coupled continuation T_(n+1)=k_n T_n, so T_n=T_0 product_(j<n) k_j. With the same fixed-normal-form stationary coefficient and no additional amplification, the required sufficient smoothness budget is

 (k_n D_n)^d / sqrt(T_(n+1)) -> 0

for every fixed d. Since D_n>=T_n/T_0, its left side is at least T_(n+1)^(d-1/2)/T_0^d. Thus the previously successful choice k=log N at a SINGLE freely chosen large initial N cannot be repeated indefinitely with N identified with the already fixed preceding period. Choosing the first period arbitrarily large pays finitely many stages, not this infinite sequence.

This is a conditional budget obstruction, not a general lower bound for all clocks. In particular an arbitrary modulated physical clock may not be a pure transported Fourier mode, and its orbit integral might use stationary interference without the same cumulative resonant covector. Even an improved coefficient cannot exceed the clock's supremum amplitude; achieving jitter 1/T requires amplitude at least a constant/T. Combined with a genuinely unavoidable pure frequency D comparable to T, this would still fail C^d smallness for d>1. But proving that EVERY useful clock has this frequency is not justified by the winding matrix alone.

A unimodular integer coordinate change has short covectors in its full dual lattice (the lattice is Z²). Therefore the assertion that all dual covectors become long would be false. What is unpaid is whether a short physical covector has a noncancelled, quantitatively useful orbit average AND the required dependence on the new invariant. The exact ideal two-step root-of-unity calculation proves that failure for nonresonant theta modes in that particular geometry; it does not classify all modes of an arbitrary later nonlinear orbit.

The full-flow target remains open. To bypass this budget one needs an actual operation decoupling orbit period growth from the resonant physical covector growth, a quantified short-covector stationary transfer, or a different coherent spectral passage. Merely alternating the two initial critical supports supplies none of these.

## Short covectors in the exact ideal model

The short-dual-vector caveat can be tested completely for the ideal two-step orbit. Expand any smooth physical clock as sum_l f_l(q) exp(2 pi i l theta); this allows arbitrary q Fourier frequencies and arbitrary smooth q cutoffs, not only a single product mode. The exact splitting calculation gives

 average_orbit f_l(q) exp(2 pi i l theta) = 0 if k does not divide l.

The l=0 term is integral f_0(q)dq, independent of the invariant b. Hence every clock with theta Fourier support |l|<k has EXACTLY CONSTANT orbit average in this ideal geometry, regardless of its q-frequency. Choosing a short two-dimensional physical covector with a large or cleverly selected q component does not evade the resonance requirement here.

For a general smooth clock b, subtract its theta frequencies |l|<k. The nonconstant orbit average is bounded in supremum by twice the supremum of the remaining Fourier tail, and consequently by C_s k^(1-s) ||partial_theta^s b||_infinity for any integer s>1. This estimate has no stationary phase assumption. It proves rapid suppression for uniformly smooth clocks as k grows, but by itself is not an impossibility at target size 1/(kN) when N can grow arbitrarily faster than k. It must not be confused with the stronger, architecture-specific cumulative-frequency budget above.

For the actual perturbed orbit, exact cancellation is lost. The O(k/N) comparison established for resonant modes is too coarse to infer either useful short-mode spreading or its absence at target scale 1/(kN). A claim that a short physical clock closes the induction would need a leading, nonzero short-mode transfer coefficient and a stable law, not merely this upper bound.
