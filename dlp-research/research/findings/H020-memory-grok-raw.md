Provider: grok / grok-4.7
TaskId: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h020-memory-constrained-hybrids-grok-20261008-r1
Status: completed; terminal result read, no pending children. Raw report NOT endorsed. Root flags recurrence of previously corrected baseline/DP claims and an undefined residue-shadow primitive. Independent reviews requested before any experiment.

No unconditional complete-work improvement. The only schedule that can beat both low-memory negation rho and high-memory x-only block BSGS is a signed jump-word macro-step walk, and only if a short 2-adic shadow stays exact for the whole word. That primitive is missing, not merely unproved as a runtime bound. Verified improvement remains **NONE**.

## Baseline at a memory budget

One full scalar on an ordinary prime-order curve, automorphism group \(\{\pm 1\}\). Let \(q\) be the group order and \(s=S/M\in[0,1]\).

**Low memory.** Bernstein–Lange–Schwabe (PKC 2011, as already used in this project): \((1+o(1))\sqrt{\pi q/4}\approx 0.886\sqrt{q}\) batched affine additions, each \(5M+1S\), once a batch inversion is treated as negligible the way that paper treats it. Distinguished-point storage at any \(M\ge 1\) does not change the leading term. This is the best prior art for every budget \(o(\sqrt{q})\).

**High memory.** Galbraith–Wang–Zhang, *Adv. Math. Commun.* 11 (2017), 453–469 (ePrint 2015/605). I read §§3–5, Lemmas 3.1–3.2, Algorithms 1–2, and Table 3 in the journal PDF. Lemma 3.2 gives average \((2\sqrt{2}/3)\sqrt{q}\approx 0.943\sqrt{q}\) group operations for interleaved negation BSGS. Their block schedule (Montgomery inversion plus one shared denominator for \(X\pm Y\)) is what makes those lists cheap. Their published constants 0.38 and 0.36 multiply by about 0.40 because they take a *serial* inversion at \(I=8M\). In the Bernstein–Lange–Schwabe model that factor is already inside \(5M+1S\), so it must not be applied again.

Dropping the unused \(y\)-multiply on side points, which are never chain heads, changes their per-point ledger. With batch width \(k\) and half-width \(\ell\), neglecting the single inversion,

\[
\frac{(\ell+1)(5k-3)}{k(2\ell+1)}\,M+1S\to 2.5M+1S.
\]

At \(k=\ell=8\) the same count is \(2.45M+1S\). Field-work ratio against negation rho, at \(s=1\), is

\[
\frac{0.943}{0.886}\cdot\frac{3.5}{6}\approx 0.62.
\]

So at memory \(\Theta(\sqrt{q})\) this interleaved x-only block schedule is about 38% fewer field multiplications than negation rho. Their grumpy-giant experimental constant \(0.9\) (Table 5, 28–32-bit trials, not a proof) would land near \(0.59\) if the same per-point cost applies. I use \(0.62\) as the proved high-memory comparator.

**Where the switch happens.** Average-case negation BSGS with \(b\) stored \(x\)-coordinates costs \((b+q/(4b))(2.5M+S)\). That undercuts rho only for

\[
b=\theta\sqrt{q},\qquad \theta\in(0.19,1.33)
\]

at \(s=1\) (the lower end is \(0.18\) at \(s=0.8\)). Below \(0.19\sqrt{q}\) group elements of memory, rho is the better prior art. Above it, x-only interleaved block BSGS is.

**Chord-bonus at this same high memory.** An optimistic extra channel at incremental cost \(c\le 1/3\) was aimed at \((1+c)/\sqrt{3}\approx 0.77\) times rho, or about \(0.95\) after the repeated-jump atom. Both sit above \(0.62\). Spending \(\Theta(\sqrt{q})\) memory on those side images loses to spending it on the block dictionary. Endpoint non-coalescence is unchanged from H017–H019. This pass does not reopen chord or Fibonacci schedules.

Sources not re-read in full this session: the PKC 2011 negation paper (used through the project baseline and the \(5M+1S\) ledger), Bernstein–Lange grumpy giants ePrint 2012/294 (used through the GWZ analysis), and van Oorschot–Wiener (distinguished points as already in the baseline). Bos’s EPFL thesis §§4.5–4.6 were read in the thesis PDF; the rest of the thesis was not.

## Card 1 — Signed jump-word macros, with a full solver

**Operation.** Keep a negation \(r\)-adding walk, canonicalized by the even-\(y\) rule (exactly one of \(\pm P\) has even \(y\) when \(p\) is odd). That bit is \(y\bmod 2\). From an exact point \(U\), a shadow of width \(w\) bits emits the next \(k\) jump indices and canonicalization signs. The unfolded point is

\[
U_k=\varepsilon_{\mathrm{tot}}U+\sum_{t=0}^{k-1}\sigma_t J_{s_t},
\]

with every \(\sigma_t=\pm 1\) a suffix product of those signs. The sum is one table lookup. One affine addition applies it, and the global sign is a negation. Coefficients \((a,b)\) update from the same word. A distinguished point inside the word uses the stored prefix sum, so the endpoint is materialized, then stored with its label. Cycle escapes stay inside the word; a shadow that misses an escape disagrees with the exact walk and is rejected by the falsifier below.

The table is per target, because each \(J_s=u_s G+v_s Q\). Build it by prefix extension: one addition per entry, not \(k\) per entry. Ordered signed words give at most \((2r)^k\) entries. Two field elements each.

**Why a gain is possible.** This is the fine walk, computed in chunks. Collision time stays \(\sqrt{\pi q/4}\) fine steps. Macro additions are that quantity divided by \(k\). Bos’s thesis §4.6 already records Cheon–Hong–Kim’s multiset table for \(\mathbb{F}_p^\times\), and records that an elliptic version which only skips \(y\) saves about \(6/5\), loses to negation, and is incompatible with negation because negation needed \(y\). The signed word above is the negation-compatible elliptic form of that table: one full addition per \(k\) fine steps, not a skipped \(y\)-multiply. It is not GWZ’s block BSGS (those points are an arithmetic progression of known multiples, not a rho word).

**Costs at budget \(B\) table entries.** \(k=\lfloor\log B/\log(2r)\rfloor\). Full additions: \(B+T/k\), where \(T=\sqrt{\pi q/4}\), plus one final scalar multiplication. Schoolbook charge for the shadow, Jacobian-sized \(c_m\approx 12\) multiplications of \(w\)-bit integers:

\[
12\Bigl(\frac{w}{\log_2 q}\Bigr)^2
\]

field-multiplication equivalents per fine step, on top of \((5+s)/k\). Distinguished-point memory is separate and small. Example, only if the shadow is real: \(r=16\), \(B=2^{20}\), \(k=4\), \(w=32\), \(\log_2 q=256\). Shadow \(\approx 0.19M\) per fine step and amortized addition \(1.5M\), against \(6M\). Setup \(B\) is negligible next to \(T/4\) once \(\sqrt{q}\gg B\), i.e. roughly \(q>2^{42}\) for this \(k\). On the admitted \((p,q)=(8191,8053)\) fixture, \(\sqrt{q}\approx 90<B\) for every \(k\ge 2\), so setup alone loses there. The schedule is a large-field proposal.

At the same \(B=2^{20}\), x-only BSGS pays about \(q/(4B)\) giants. For a 256-bit prime that is far above rho. Any win here is in the rho regime, not the BSGS regime.

**Missing primitive, not a missing runtime proof.** The solver, labels, and endpoint rule are determined. What is missing is a shadow of width \(w=t+O(k)\), not width \(\log_2 q\), whose scale-normalized residue predicts those \(k\) indices and even-\(y\) bits. Polynomial formulas mod \(2^w\) are exact on the residue, but the common \(2\)-valuation and the affine quotient can still demand more bits. If the width must track the field, the macro-step is a full addition and the factor \(k\) is gone.

**Falsifier, not run.** One ordinary prime-order curve, one predeclared triple \((r,k,w)=(16,4,32)\), \(10^4\) exact steps from one seed. Iterate the residue in parallel. Kill the card if the median length before the jump index or the even-\(y\) bit disagrees is \(<4\). A pass on a 16-bit field does not prove a 256-bit shadow; a failure kills every size. No feature sweep.

## Card 2 — Grow one x-only dictionary; do not restart it

**Operation.** Under a hard cap of \(b\) stored \(x\)-coordinates, fill one negation baby list with the \(2.5M+1S\) block schedule, stride \(2b\), then run giants until the match. The other policy people reach for is a restart: many grumpy or interleaved herds of length \(L\le b\), each thrown away after a miss.

**Why it looked better.** GWZ Table 4 has coverage constant \(c(0)=6\) at the start of a negated grumpy run, against an average near \(0.9\). Short herds live entirely in that high-\(c\) region.

**Ledger.** One herd of \(L\) steps on each of three lists costs \(3L\) block-points and covers about \(6L^2\) scalars while \(c\) stays near 6. Success probability \(6L^2/q\). Expected cost \(q/(2L)\) block-points, which falls as \(L\) grows. Extending the same lists beats discarding them. The cap is therefore a single dictionary: average

\[
\bigl(b+q/(4b)\bigr)(2.5M+S)
\]

and this is below rho only for \(b>0.19\sqrt{q}\) as above. Restarts do not move that threshold.

**Unsupported assumption.** Early abort is uniform in the giant index, and \(c(L/\sqrt{q})\) does not rise again after a restart in a way Table 4 missed. The closed form already kills the restart under GWZ’s own \(c\).

**Falsifier.** No curve. Substitute any coverage \(|\mathcal{L}|\le c_0 L^2\) with \(c_0\) fixed and the same per-point cost: expected block-points on fresh restarts are \(\Theta(q/L)\), minimized at maximum \(L\).

## Card 3 — Anchor fingerprints do not change the memory exponent

**Operation.** Keep the same baby arithmetic progression. Store a full affine anchor every \(m\) babies. Store every baby as a \(t\)-bit fingerprint plus its index. A giant hit recomputes at most \(m\) x-only steps from the anchor and checks the point.

**Why it looked better.** A field element is \(\log_2 q\) bits. A short fingerprint would seem to multiply the number of babies that fit in a fixed RAM, and push the \(0.19\sqrt{q}\) crossover down.

**Ledger.** Set the false-hit rate so that verification adds only a \(1/(2\lambda)\) fraction of a giant step. That forces

\[
t=\log_2(Bm\lambda).
\]

Bits per logical baby, including the anchors (two field elements) and the index:

\[
2\log_2 B+\log_2(m\lambda)+\frac{2\log_2 q}{m}.
\]

At \(B\sim\sqrt{q}\) and \(m=8\), \(\lambda=10\), this is about \(1.25\log_2 q\) bits against about \(1.5\log_2 q\) for a full \(x\) plus an index: roughly 20% more babies, and giants are 5% slower. Rebalancing a \(\sqrt{q}\) search by that factor does not change \(\theta=\Theta(1)\). The crossover memory stays a constant fraction of \(\sqrt{q}\). H007’s fingerprint BSGS note already required a concrete budget where compression beats a baseline allowed the same compression. This is that budget, and the inequality fails for every realistic \(\beta<1/2\).

**Unsupported assumption.** Fingerprints of \(x([j]G)\) behave like uniform \(t\)-bit strings on the giant queries. A large deviation would have to be enormous to create a polynomial gap; the falsifier is the bit count above, which does not use that randomness except to set \(t\).

**Falsifier.** No curve. Any \(t\le\log_2(Bm\lambda)\) that keeps verification inside a constant factor of one giant step leaves \(\Theta(1)\) bits of a field element per baby. Then \(b=O(W/\log q)\) for a RAM of \(W\) bits, and \(b>0.19\sqrt{q}\) still forces \(W=\Omega(\sqrt{q}\log q)\).

## Card 4 — Replay buckets for a noncoalescent side stream

**Operation.** A side image that does not merge walks cannot use distinguished points (H017–H019). The stream is replayable from seeds. With memory \(b\), partition the \(x\)-line into \(T/b\) buckets, replay the walk once per bucket, and store only the hits in the current bucket. A bucket of \(b\) images is sorted and matched. Labels ride with the seed and the step index. A hit \(B_i=\pm W_j\) is checked for a nonzero coefficient of \(k\) and verified by one scalar multiplication.

**Why it looked better.** Replay converts a noncoalescent stream into an external-memory collision search, so a cheap side image might be recovered without storing \(\Theta(\sqrt{q})\) keys and without coalescing.

**Ledger.** Producing \(T\) images and replaying them across \(T/b\) buckets costs \(T^2/b\) walk steps, plus the side-image arithmetic each time. A useful collision wants \(T\sim\sqrt{q}\), hence \(\sim q/b\) steps. Rho at the same memory is \(0.886\sqrt{q}\) steps. Block BSGS at the same memory is \(b+q/(4b)\) listed points at \(2.5M+S\), and those points are systematic rather than replayed. The bucket algorithm is worse than both whenever \(b<\sqrt{q}\). This prices this detector only. It is not a claim that every implicit detector costs \(q/b\).

**Unsupported assumption.** Bucket hashes split the side images evenly and a replay has the same cost per step as the original walk.

**Falsifier.** No curve. Count passes: \(T/b\) replays of a length-\(T\) walk is \(T^2/b\) before any match logic. The inequality with rho is \(T>b\).

## Wave report

Best supported work is negation rho at \(0.886\sqrt{q}\) additions of \(5M+1S\) when memory is below \(0.19\sqrt{q}\) group elements, and x-only interleaved block BSGS at about \(0.62\) times that field work when memory is \(\Theta(\sqrt{q})\). Verified improvement: **NONE**. The hypothesis worth a later look is Card 1’s shadow, and only as a kill test. Evidence against a present gain: setup already exceeds the solve on the admitted 13-bit fixture, and the shadow width is unproved. Next conclusion-changing step is the single predeclared \((16,4,32)\) shadow disagreement count. It was not run. No Lean, no feature sweep, no other live H020 proposal was read.
