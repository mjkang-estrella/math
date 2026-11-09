# H006 disposition: close the small exhaustive-tree claim

Verified factoring complexity improvement: **NONE**. The frozen experiment
remains inconclusive under its original threshold. A separate mathematical
review now rejects the proposed exhaustive tree bound; it does not change the
experiment's outcome retroactively.

The [independent review](H006-independent-review.md) replayed all 20 inputs and
checked 53,108 certificates, including their validity in ancestor nodes. It
also gives explicit examples showing that an uncertified node can contain
factors and that the full relaxation can be feasible when the restricted
certificate constructor fails. Thus this probe is not a complete factorer.

The coordinator checked the following chain in the new argument:

1. Interior tangent/chord gaps for powers 3,4,5 contain every residue modulo R
   in the stated intervals. After z2=t² is fixed, high-digit choices are free
   whenever the truncated inverse supplies q in the public interval.
2. Inner feasible witnesses remain feasible in every outer interval, so those
   nodes are reached by exhaustive exact-feasibility bisection.
3. The power-of-two complete-sum bound follows by writing an odd residue as
   y+2^ceil(m/2)*z and summing the linear phase over z. The square-root
   congruence has at most four roots; no unverified odd-prime estimate is
   imported at modulus 2^m.
4. Fourier interval bounds give R³/16+o(R³) qualifying positions in the aligned
   diagnostic box, uniformly in odd N. Those yield Theta(R³) full-tree nodes.
   The report separately handles actual clipped boxes with intervals of
   16–31 candidates at the frontier and an arbitrary-interval estimate.

Consequently the specified exhaustive tangent/secant route cannot satisfy
V=R*poly(K), with R=2^(K/6), on that broad range. Its node count instead has
Theta(2^(K/2)) scale. The general proof has an asymptotic threshold well above
the tiny experiment; it is not a fit to the sampled node fractions.

This is a reviewed mathematical derivation, **not a Lean theorem**. It concerns
the specified independent-power relaxation and exhaustive traversal. It gives
no early-stop factoring lower bound, no lower bound for different coupled
constraints, and no general factoring lower bound. More tangents alone cannot
remove the available high-digit choices.

Do not implement a generic IP engine for this closed full-tree hypothesis.
The next revised task, H011, asks for an explicit, costed inverse-interval
reporting construction that retains more exact coupling. An output count or
an unnamed nonlinear solver will not be accepted as that construction.
