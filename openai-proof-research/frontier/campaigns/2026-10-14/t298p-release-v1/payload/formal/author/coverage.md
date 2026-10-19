# Scoped coverage and explicit premises

Four support theorems and four counterexample controls only. This does not formalize T298P's two-variable free-entropy separation, its source theorem, or any analytic estimate. Original r104 candidate §§3–5 was read; its proof and scope are unchanged. No pending proof review was opened.

`coefficient_isometry` proves the real finite-column norm identity in an arbitrary real inner-product space. It assumes the complete column Gram identity, and allows nonorthogonal vectors xi. It does not prove that the particular matrix coefficients in the paper have that Gram identity, nor the trace normalization converting them into real coefficients.

`leading_score_energy` applies this identity after scaling by 1/(epsilon*k²), giving the denominator epsilon²*k⁴. It holds algebraically even at zero under Lean's total division convention; the paper only applies it at epsilon>0 and positive integer k. It does not identify these vectors as free conjugate variables or show an inner derivation is closable, a coefficient inverse converges, or projection contracts the proposed scores.

`gap_transfer` uses eleven finite real variables, c>=0 and nonnegative errors. Its substantive hypotheses are the microstates increment lower bound, nonmicrostates increment upper bound, and endpoint micro1<=star1. It proves c*(source gap0-source gap1)-(eMicro+eStar)<=output gap0. The nonnegative assumptions are explicit even though this rearrangement itself does not need them. There are no extended-real entropies or existence assumptions hidden in the types.

`strict_gap` additionally assumes c>0, source gap0>0, noisy source gap<=half the original gap, and total error strictly below c*source gap0/2. It concludes micro0<star0. It does not establish the existence of the large noise time, the small epsilon, either increment estimate, entropy finiteness, liminf passage, or Gaussian asymptotics. In the candidate c=k^-2 and the errors are supplied analytic O(epsilon) bounds.

Controls are kernel-proved explicit counterexamples: k² substituted for k⁴; missing endpoint entropy comparison; reversed source gap sign despite both increment bounds and endpoint comparison; and equality instead of strict error absorption. They check the scalar interfaces, not free-probability validity. All use standard axioms only.
