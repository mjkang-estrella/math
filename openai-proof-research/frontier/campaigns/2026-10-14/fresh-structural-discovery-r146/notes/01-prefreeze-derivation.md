# PREFREEZE calculations: separable weights on common integer bases

No theorem is frozen. No author-proof nominee or independent grade is assigned. The investigation uses Source114 finite common-base counting and its required Source115 cell-bounded companion. Conservatively counting that companion as a family gives two; no third family was screened for research. The initial matroid catalogue query incidentally exposed Source111 and185 headings and an unrelated MUB title; no theorem/proof from those entries was selected. The companion is read to establish operative compatibility, not to fill the round with another nominee.

## Research question, not a frozen claim

Let r1,r2 be normalized monotone integral submodular ranks on a finite explicitly listed E, with equal total R given in binary, and exact value oracles. Write Ω for their common integer bases. Investigate a partition function Σ_{x∈Ω} ∏_e a_e(x_e), where the a_e are nonnegative log-concave sequences with interval supports. A meaningful algorithmic statement would have to specify exact evaluation versus approximate log-evaluation access, supplied range/bit bounds, zero detection, a compact log output when weights have exponentially long ordinary rational expansions, and polynomial cost in log R rather than R. None of those quantifiers is silently fixed into a theorem here.

Chen–Liu v1 Proposition C.20 ALREADY handles two arbitrary log-M-concave integer weights, including these separable factors, with unary capacities, initial positive vectors, and supplied logarithmic coefficient-range bounds. Its proof uses polarization and complementary factorial corrections, not an assumption that the hard intersection is log-concave. Source114's own binary theorem, geometry and count interfaces are stronger in a different direction. Source115/r57 already handles full binary exponentially tilted table weights by reduced-cost localization plus the operative source machinery. I29's entropy trace and r141's exact projection representation are also paid. Hypothesis removal alone is not evidence of substantial contribution.

## Compatible weighted root-direction reduction

The pinned signatures section proves a stronger normalized rank-factor property J−Q positive semidefinite, where Q_ij=G(z)G(z+σe_i+σe_j)/(G(z+σe_i)G(z+σe_j)), with invalid repeated steps set to zero. Its proof partitions nonloop copies into parallel classes. Count coordinates feeding the same physical coordinate are interchangeable.

Multiply one rank penalty by ∏_e a_e(v_e), where physical v_e=b_e+Σ_{i∈I_e}z_i, or the consistently reflected version. Assume at first the sequences are strictly positive on the finite range in use. For i,j in different physical groups, the unary normalized ratio is1. Within group e the ratio is

    β_e = a_e(v_e) a_e(v_e+2σ) / a_e(v_e+σ)^2 ≤ 1.

The rank ratio within a given physical group is constant q_e∈{1,exp(−2H)} on all valid repeated/double changes. This follows from the exact interchangeability argument in the source, including distinct spare copies for a repeated step. Therefore the new normalized matrix Q' obeys

    J−Q' = (J−Q) + Σ_e q_e(1−β_e) 1_{I_e}1_{I_e}^T

on valid displays, with the same nonnegative diagonal boundary corrections. It is positive semidefinite. Reflection handles removal/addition, and a positive power replaces β_e by β_e^s and H by sH. Thus both signatures remain available. These are direct source operations with a block correction, not a proposed substantial lemma.

Apply this to disjoint factor coordinates for the two source rank penalties. The balanced-summation proof remains compatible: its division only needs strictly positive pre-limit weights; the unary factors have not changed that. For the source difference encoding, grouped p,a_j coordinates carry the same physical unary factor. Hence the same proof supplies root-direction log-concavity for the weighted difference sum

    Y_a(d)=Σ_{x1−x2=d} 1_{x1∈B(r1)}1_{x2∈B(r2)} A1(x1)A2(x2),

where each Ai is a product of positive log-concave unary weights. Positivity approximations can handle interval supports: extend a finite concave logarithm linearly with slopes tending to +∞ on the left and −∞ on the right. Those finite extensions are concave and positive, then converge to zero outside the intended interval. Pass the GLOBAL interpolation inequality to the limit, as in the source, rather than inferring interval support from adjacent inequalities with zeros. Setting A1=A2=√(∏ a_e) recovers the desired weight at d=0. This does not prove a counter with binary complexity.

## Why large geometric slack alone is not enough

The source shift-average proof uses both root-direction log-concavity and the bounds 1≤Y(d)≤exp(K) throughout a large positive shift region. Feasible weighted pairs may have arbitrarily tiny weights; feasibility alone supplies no uniform lower bound. If all relevant original individual-factor weights lie in [exp(−L),1], the same secant proof DOES work, with K replaced by K+2L. This is a compatible composition, not an obstruction. An algorithm must obtain such a normalization/range at polynomial cost for the required retained region, without enumerating R units.

For any nonnegative separable loss representation w(x)=exp(−C*−Σ_e q_e(x_e)) on Ω, q_e≥0, with a common feasible x* for which every q_e(x*_e)=0, and B≥|Ω|, clipping to q_e(x_e)≤K loses at most B exp(−K) of the normalized mass. The normalized partition function is at least1. With K≥log B+log(1/δ), the lost fraction is at mostδ. Convex q_e makes each retained coordinate set an interval. This is exactly the elementary tail operation credited in r57 in its linear reduced-cost setting. It is valid CONDITIONAL ON such a representation; no oracle-efficient construction for arbitrary supplied nonlinear losses is asserted here. An arbitrary individually preferred endpoint need not be jointly feasible.

The natural classical way to seek the representation is separable convex optimization on the common-base intersection followed by a dual supporting-price split. This cannot be rejected just because the naive separate minimizers disagree. Its precise oracle and bit complexity, especially for approximate log-value input, needs actual primary support before it is used as a completed operation.

## Compression is a distinct operation

Source114 ports.tex represents each physical coordinate X_i(u,z) as an integral linear expression in small part totals u and large free coordinates z. It replaces the free lattice sum by an integral, convolves in u, and adds a quadratic regularizer. The proof needs a small GLOBAL logarithmic Lipschitz bound L0=N^330/W: it pays unit-cell quadrature, convolution error L0 b0, and finite-difference versus Hessian errors. A general separable log-concave weight composed with X_i need not have that small bound, even if its logarithmic range is polynomial. Nonlinear weights cannot simply be inserted while retaining the source's old constants.

The discrete balanced-summation reduction above remains available and retains the required signatures. It may involve exponentially many hidden values. The unary primary polarization makes that dependence explicit. Conversely ordinary Prékopa log-concavity of a free-coordinate integral is not sufficient for either discrete quadratic signature; note02 gives an exact rational diagnostic. The failure of one direct integral/regularizer step does NOT exclude compatible alternative compression, adaptive coordinates, exact discrete evaluation, or other source/classical compositions.
