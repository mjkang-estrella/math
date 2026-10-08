Provider: grok / grok-4.7
TaskId: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h019-fullwork-walks-grok-20261008-r1
Status: completed; no pending children. Raw report, NOT endorsed. Independent corrections pending.

No material complete-work gain. Four collision schedules close on the charged negation-rho baseline: the cheap chord bonus, a Fibonacci one-point stream, an isogenous differential model, and a residue filter. Verified improvement remains **NONE**.

Baseline used: one full scalar on an ordinary prime-field curve of prime order \(q\), automorphism group \(\{\pm 1\}\). Negation-aware rho costs about \(\sqrt{\pi q/4}\) batched affine additions. Bernstein–Lange–Schwabe charge each such addition as \(5M+1S\) once a batch of inversions is amortized. Setup, memory, failed checks, verification, and extraction are extra. The completed four-feature length-64 run on the single \((p,q)=(8191,8053)\) fixture is a finite diagnostic only. It is not an asymptotic input, and this report does not authorize another test.

Sources read for this pass: `RESEARCH_LOOP.md`, `RESEARCH_TEAM.md`, `research/STATE.md`, the H013 collision baseline, the H015 preprocessing baseline, the H017 and H018 hybrid dispositions, and the H018 raw hybrid note. Primary text checked this session: Bernstein–Lange–Schwabe (the \(5M+1S\) and \(\sqrt{\pi\ell/4}\) iteration), the Explicit-Formulas Database short-Weierstrass XZ page, and Bos’s EPFL thesis §4.6 on ECDLP tag-tracing. Cheon–Hong–Kim tag-tracing and Bernstein–Lange grumpy giants are treated as prior art, not as new schedules.

## 1. Chord-bonus sidecar

**Operation.** Keep the negation-aware \(r\)-adding walk. On the addition \(P+J_i\), the slope inverse is already known. The Bernstein–Lange–Schwabe intermediates then give the other branch
\[
x(P-J_i)=x(P+J_i)+t(2\lambda+t),\qquad t=(2y_{J_i})(x-x_{J_i})^{-1},
\]
at two extra multiplications. Store walk \(x\)-classes, and optionally these bonus classes, and look both up. A hit \(P-J_i=\pm R\) has known labels. The coefficient of \(k\) is \(b_P-d_i\mp b_R\). Discard a zero coefficient in \(O(1)\) scalar arithmetic and verify a nonzero one by one scalar multiplication.

**Why it looked better.** Each step emits the ordinary class and one extra affine image at
\[
c=\frac{2M}{5M+1S}.
\]
With \(S\le M\) this is at most \(1/3\). If ordinary collisions and bonus collisions behaved as two or three disjoint uniform channels, the ideal addition-equivalent ratios would be
\[
\frac{1+c}{\sqrt{2}}\approx 0.94,\qquad \frac{1+c}{\sqrt{3}}\approx 0.77,
\]
at memory \(\Theta(\sqrt{q})\).

**What the schedule actually does.** The bonus is not an independent sample. With the sign left unflipped, \(B_t=W_{t-1}-J_t\). Whenever the jump index repeats, \(B_t\) is the predecessor, the labels match, and the coefficient of \(k\) is zero. Those hits are automatic, about \(1/r\) of the steps, and must be rejected locally. The third channel, a bonus matching an older bonus, is another linear form on the same trajectory, not a fresh uniform stream. Distinguished points do not see these hits: \(x(P-J)\) is not a later ordinary iterate, so the walks do not coalesce. Capturing the channel means storing a positive fraction of all iterates, which puts memory at \(\Theta(\sqrt{q})\).

**Ceiling.** After removing the repeated-jump atom, the optimistic one-extra-channel ratio sits near \(0.95\) in addition-equivalents, before the second hash and the label word. That is not a material complete-work gain over negation rho. The \(0.77\) figure is the old ideal doubling count; this image does not earn it.

**Unsupported assumption.** Away from repeated jumps, \(B_t\mp W_s\) is uniform on the negation classes and the coefficient of \(k\) is nonzero at the first hit.

**Prior art.** The \(2M\) identity and the ideal factor \((1+2\delta)\) are the H018 sidecar, corrected there and not re-derived here. Negation coalescence and lazy endpoint labels are Bernstein–Lange–Schwabe.

**Paper falsifier.** Substitute \(B_t=W_{t-1}-J_t\) into a claimed bonus–bonus or bonus–walk hit and count the distinct useful equations. The claim dies if every hit reduces to an ordinary walk collision, a repeated-jump identity, or a zero coefficient of \(k\). No curve run is required to reject the \(0.77\) ceiling.

## 2. Fibonacci one-point stream

**Operation.** Run \(P_n=P_{n-1}+P_{n-2}\) with labels obeying the same integer recurrence. Keep three consecutive \(x\)-coordinates so the difference \(P_{n-1}-P_{n-2}=P_{n-3}\) is on hand. Store one \(x\)-class at a time, not the pair. A hit \(P_n=\pm P_m\) gives
\[
(b_n\mp b_m)k\equiv a_m-a_n\pmod q.
\]
Restart when a coefficient repeats or a cycle in the pair state returns. This is the sampler and stopping rule the differential kernel did not have.

**Ledger.** The difference is a running point. The EFD formula that applies is general XZ differential addition, \(7M+2S\), plus the curve parameters. Mixed \(6M+2S\) applies only when the difference is normalized once and then reused, which is a fixed jump, not this recurrence. Against \(5M+1S\),
\[
\rho\ge\frac{7+2s}{5+s}\ge\frac{3}{2}\quad(s\le 1).
\]
The pair map is invertible, so trajectories do not merge. With storage probability \(\theta\), the expected number of differential steps to a stored hit is \(\sqrt{\pi N/(2\theta)}\) under a uniform-orbit heuristic, where \(N=(q-1)/2\). In baseline additions that is \(\rho/\sqrt{\theta}\) times negation rho. Every \(\theta\le 1\) and every \(\rho\ge 3/2\) gives a ratio at least \(3/2\).

Forcing runs of a constant jump, so that mixed \(6M+2S\) applies, replaces rho with an arithmetic progression and still has \(\rho=(6+2s)/(5+s)>1\). Memory at \(\theta=1\) is \(\Theta(\sqrt{q})\). Setup is two scalar multiplications per restart.

**Unsupported assumption.** The first \(x\)-repeat on one orbit has \(b_n\mp b_m\neq 0\) and occurs by \(\sqrt{\pi N/2}\) steps.

**Prior art.** EFD `dadd-2002-it-3` and `mdadd-2002-it-3`. Montgomery \(4M+2S\) / \(6M\) differential addition needs a rational \(2\)-torsion point, which this group does not have. Bos’s tag-tracing (§4.6) already skips work between distinguished points and loses to negation: the published non-negation saving is about \(6/5\), and dropping negation costs \(\sqrt{2}\).

**Paper falsifier.** An explicit short-Weierstrass step, with no rational \(2\)-torsion, whose multiplication count is strictly below \(5M+1S\) and whose state equality is one \(x\)-class. The EFD XZ table does not contain that step. Specifying the recurrence without that step leaves the ratio at least \(3/2\).

## 3. Isogenous differential model

**Operation attempted.** Move the walk across an \(\mathbb{F}_p\)-isogeny of small degree to a curve whose differential addition beats \(5M+1S\), take the collision there, and pull the labels back.

**Obstruction.** Let \(\varphi:E\to E'\) be an \(\mathbb{F}_p\)-isogeny of degree \(\ell\ge 2\). Then \(\varphi(E(\mathbb{F}_p))\) is a rational subgroup of order \(q\) or \(1\). Degree \(\ge q\) is useless as a model change. So \(q\) divides \(\#E'(\mathbb{F}_p)\). Both orders lie in the Hasse interval of length \(4\sqrt{p}\). For \(q>4\sqrt{p}\) the only multiple of \(q\) in that interval is \(q\) itself, so \(\#E'(\mathbb{F}_p)=q\). A Montgomery or twisted-Edwards model over \(\mathbb{F}_p\) needs a rational point of order \(2\) or \(4\). An odd prime order supplies neither, on \(E\) or on \(E'\). The faster differential step does not become available anywhere in the rational isogeny class.

**Prior art.** Vélu, the Hasse bound, and the EFD Montgomery XZ row. This is a property of prime-order rational points, not a generic-group bound and not a runtime read off from isogeny degree.

**Paper falsifier.** An \(\mathbb{F}_p\)-isogenous \(E'\) with \(\#E'(\mathbb{F}_p)\) divisible by \(q\) and even, inside the Hasse interval, for some prime \(q>4\sqrt{p}\). The interval arithmetic forbids it.

## 4. Residue-filtered walk

**Operation.** Canonicalize by negation, then try the jump list in order and accept the first image whose \(x\)-coordinate is a quadratic residue. On failure of the whole list, take the first jump anyway. Shift the starting point by at most a few multiples of \(G\) so the start lies in the same set. A collision inside the set is still an affine relation for \(k\).

**Ledger.** Character-sum cancellation puts about half the negation classes in the residue set, up to an \(O(q^{-1/2})\) error. If each trial is an independent full addition, the mean number of additions per accepted step is \(2\). The logical collision time on a set of size \(N/2\) is \(\sqrt{\pi N/4}\). Physical cost
\[
2\cdot\sqrt{\pi N/4}=\sqrt{2}\,\sqrt{\pi N/2},
\]
which is \(\sqrt{2}\) times negation rho. The same arithmetic with a subset of density \(\delta\), paid for by \(1/\delta\) retries, costs \(1/\sqrt{\delta}\) times the unfiltered walk whenever the step does not land in the subset by itself.

Computing \(x(P+J)\) already spends the slope. A Legendre test does not avoid that addition. Negation is the case this filter does not imitate: both signs are produced by one addition, and the hash reads only \(x\).

**Unsupported assumption.** Successive jump images have independent Legendre symbols, so the retry mean is exactly \(2\).

**Scope.** This is the ledger for this explicit retry rule. It does not price a future step that would land in a free subset with no extra addition.

**Paper falsifier.** A partition rule, computable from the intermediates of the single accepted addition, whose accepted set has density \(\delta<1\) and whose mean number of additions per accepted step is strictly less than \(\sqrt{\delta}\). The residue rule has mean \(2\) and \(\sqrt{\delta}=1/\sqrt{2}\).

## Wave report

Best supported work remains negation-aware Pollard rho, about \(\sqrt{\pi q/4}\) batched affine additions of \(5M+1S\), with distinguished-point memory, seed replay, and known automorphism constants. Signed BSGS and grumpy-giants constants are baselines. This is not a coordinate-aware lower bound.

Verified improvement: **NONE**.

Concrete schedules above: chord-bonus detection, Fibonacci one-point stopping, rational-isogeny model change, and residue retry. All four are complete enough to price. None clears the baseline after arithmetic, detection, labels, and memory.

Evidence against: the only sub-addition bonus on an adding step repeats the predecessor on a repeated jump; EFD differential addition is \(7M+2S\) against \(5M+1S\); a rational isogeny preserves prime order; a residue retry multiplies work by \(\sqrt{2}\). Tag-tracing’s published \(6/5\), without negation, remains slower than the negation baseline.

Next paper check that would change the conclusion: an explicit image, produced from one batched addition, whose incremental cost is below \(1/3\) of \(5M+1S\), whose equality is not a repeated-jump identity, and whose detection does not require storing \(\Theta(\sqrt{q})\) keys. No such formula is on the EFD XZ page. A curve census is not the next step.
