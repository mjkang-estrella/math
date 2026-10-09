# H043 full-work Grok raw report — UNACCEPTED

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h043-new-fullwork-constructions-grok-20261009-r1`.
Provider/model: grok / grok-4.7. Terminal result.
Formula prices, collision laws and general exclusions require independent review.
No numerical experiment or candidate admitted.

No new labelled search operator. Verified improvement stays **NONE**, and the working exponent stays **1/2**. Three public compositions were costed from primary formulas. Each one lands above the competent baseline once labels, detection, and memory are included, so none is submitted.

## Baseline this pass used

Low memory, under about \(0.19\sqrt{q}\) stored abscissae: Bernstein–Lange–Schwabe negation rho, heuristic \((1+o(1))\sqrt{\pi q/4}\approx 0.886\sqrt{q}\) iterations, each a batched affine addition of \(5M{+}S\). High memory: x-only interleaved negation BSGS at \((b+q/(4b))(2.5M{+}S)\). Negation, batch inversion, lazy-label replay, and rotated cycle checks are already in that baseline. No solver was run. The H034 cap was not touched. No other H043 proposal was read.

## Compositions examined

**1. Conjugate pair from one affine addition.** The EFD short-Weierstrass formulas give one sum as \(I{+}2M{+}S\). With the project’s batched \(I=3M\), that is the baseline \(5M{+}S\). The opposite sum uses the same denominator: one extra slope multiply, one square, and one \(y\)-multiply, so \(+2M{+}S\). Both full points cost \(7M{+}2S\).

The extra point’s relative cost is \(c=(2+s)/(5+s)\): about \(0.483\) at \(s=0.8\) and \(0.5\) at \(s=1\). In the ideal model where that extra point is an independent, always-detected sample, the work factor is \((1+c)/\sqrt{2}\approx 1.05\) to \(1.06\), above negation rho. If both points are stored and counted as independent samples, each emitted point costs \(3.5M{+}S\), against x-only keys at \(2.5M{+}S\). The ratio \((3.5+s)/(2.5+s)\) is about \(1.29\)–\(1.30\) for \(s\in[0.8,1]\). These ideal ratios are optimistic comparisons for this formula. They are not a lower bound on other coordinate schedules.

**2. Abscissa-only conjugate.** Dropping the second \(y\)-multiply leaves \(+1M{+}S\), so \(c=(1+s)/(5+s)\approx 0.31\) to \(0.33\). The ideal factor \((1+c)/\sqrt{2}\approx 0.93\) to \(0.94\) is the already-scoped chord-bonus figure. It is not a justified collision law: the side value is a function of the current point and the jump, a repeated jump reproduces an earlier point, and the walk does not move there, so later points do not coalesce. Detecting those satellites means storing them. Counting both images as independent samples then costs \(3M{+}S\) per emitted abscissa, still about \(1.14\)–\(1.15\) times the x-only key price. Equality of the field value \(x(W{+}J)+x(W{-}J)\) is a degree-3 rational feature of the abscissa. A match of that feature is not a point collision and does not produce a coefficient of \(k\).

**3. Shared-\(Z\) conjugate and x-only differential steps.** Goundar–Joye–Miyaji, CHES 2010 slides, charge conjugate co-\(Z\) addition (ZADDC) at \(6M{+}3S\), the conjugate itself at \(+1M{+}1S\), and only when the two inputs already share \(Z\). Their algorithm is a Montgomery ladder for scalar multiplication: the difference stays a fixed base. A hash-selected rho jump does not share \(Z\) with the walk point, and equalizing \(Z\) adds further multiplications. EFD `dadd-2002-it-3` is \(7M{+}2S\) and requires the difference point as an input. That is already above \(5M{+}S\) before the difference is maintained. A fixed-difference ladder is scalar multiplication, not a walk on the negation quotient.

**Cycle handling.** Search-index text of Wang–Zhang, ePrint 2011/008, Algorithm 1, still iterates \(F(Y)=\pm(Y+R_j)\). The added work is a block-minimum tracker (\(N=16\)) and a doubling escape. Their claim is a speedup close to \(\sqrt{2}\), the same negation factor already in the Bernstein–Lange–Schwabe iteration count. That is a rotated cycle check, which is baseline. Their experiments are finite and are not an asymptotic proof.

A direct ePrint fetch of 2010/309 and 2011/008 returned HTTP 403, and the 2010/309 web fetch stopped on a Cloudflare page. The ZADDC cost used here is from the CHES 2010 slides, which did load. The dedicated EFD affine-coordinate URL returned 404. The affine formulas came from the parent short-Weierstrass page, which loaded, as did the XZ page. A 2025 index-calculus abstract (Gupta, Jñānābha) still collects relations by Pollard rho and does not give a priced decomposition. The 2026 prime-field ECDLP hits found in search are quantum and are outside this classical schedule.

## What this does not close

No adaptive one-shot projection into a proper subset of the negation quotient was found. A sign choice inside an \(r\)-adding walk is the baseline walk. Rejection sampling at density \(\delta\) multiplies the step count by \(1/\delta\) in expectation, which removes the density gain in the ideal urn model. History-dependent rules were not given a free coalescence claim: the history would have to sit in the state, be reconstructed, or be shown irrelevant. No table/rho hybrid, fingerprint schedule, phase clock, or Farey/height-lattice construction was reopened. No birthday constant was taken from an ideal collision law.

## Wave report

- Best supported estimate: exponent \(1/2\), with the two comparators above. Assumptions are the recorded field ledger, negation-quotient heuristic for rho, and the x-only key price at the same \(s=S/M\).
- Verified improvement: **NONE**.
- Hypothesis under test: none. No card is submitted.
- Evidence: the three formula invoices above. Nothing was run.
- Next conclusion-changing object: one named public successor on canonical states no larger than the negation quotient, with an affine label update, a nonzero coefficient of \(k\), and a full invoice — useful collisions, nulls, cycles, detection, replay, memory, verification — strictly below both comparators. Only that object warrants a falsifier. No experiment is justified from this pass.
