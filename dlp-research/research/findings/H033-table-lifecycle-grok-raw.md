# H033 table lifecycle initial report

UNREVIEWED report; broad exclusions and costs require corrections before acceptance.
Task: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h033-table-lifecycle-grok-20261008-r1
Provider/model: grok / grok-4.7. COMPLETED, no pending children.

No survivor. For one full-range prime-order target, reusing, retiring, or rebuilding an explicit collision table across phases does not beat one optimal signed table at the same peak, and in the low-memory regime it does not beat negation rho. Three concrete schedules die on closed-form comparisons. Nothing here was run.

## What survives eviction

A useful relation is a resident equality \(X_1=\pm X_2\) of labeled points \(X_i=[a_i]G+[b_i]Q\) with \(b_1\mp b_2\not\equiv 0\pmod q\). It determines one \(k\). Same-coefficient matches, including tame–tame matches, have coefficient \(0\) and determine nothing.

| Surviving state | Scalar content left | What it costs later |
|---|---|---|
| The solved \(k\), or the two coefficient pairs | One integer in \(\mathbb Z/q\mathbb Z\) | Search stops. \(O(\log q)\) bits. |
| A public interval (or \(O(1)\) arithmetic progressions) already tested | \(k\) lies outside that set | \(O(\log q)\) bits. This is a BSGS checkpoint. The baby keys are still required for every later giant that uses them. |
| A replay seed for a deterministic trail | No equation until the trail is rebuilt | Seed-replay distinguished points, already the low-memory baseline. Replay length is paid. |
| Resident abscissa plus coefficients | Lookup works only while both sides are available | This is the live table. Evicting it removes those candidates from every later probe. |
| A filter or checksum of evicted keys | Negative membership at best; a checksum is one group element | Not a coefficient. Positive hits still need paid reconstruction. |

Evicting both the point key and \((a,b)\) leaves no equation. Keeping \((a,b)\) without a key leaves nothing to match. Keeping the key without \((a,b)\) leaves an equality that does not yield \(k\) until reconstruction, which is another discrete log unless a seed was stored.

Cumulative coverage under a resident cap of \(b\) keys is therefore the set of scalars actually tested while those keys were resident. One structured negation-BSGS probe against \(b\) stored \(x\)-coordinates certifies \(O(b)\) candidates and, in the project schedule, averages \(b+q/(4b)\) generated points with worst case \(b+q/(2b)\). One unstructured probe against \(b\) stored \(x\)-classes hits with probability about \(2b/q\), so the expected probe count is \(q/(2b)\). Rebuilding an evicted arithmetic progression of length \(b\) costs \(b\) incremental additions. Doing that once and holding the result is a new resident phase. Doing it on every probe multiplies the probe cost by \(b\).

## Named regimes

These are stored-\(x\) / generated-point regimes. H020 records that \(b+q/(4b)\) is one capped listing schedule, so the numerical crossover is not a matched-DRAM-bit theorem. Bit packing, seed replay, and the H030 hierarchy stay on the baseline side of any bit comparison.

Write \(s=S/M\in[0,1]\), \(\rho=\sqrt{\pi/4}\approx 0.886227\), and \(c_x=2.5+s\), \(c_\rho=5+s\).

- **Regime L.** Resident collision keys at most \(\theta_{\mathrm{lo}}(s)\sqrt q\), where \(\theta+1/(4\theta)=\rho\,c_\rho/c_x\). At \(s=1\), \(\theta\in(0.1878,1.3315)\); at \(s=0.8\), \(\theta\in(0.1817,1.3759)\). Baseline: negation rho, heuristic \((1+o(1))\rho\sqrt q\) iterations on the negation quotient, \(5M+S\) each, plus \(\Theta(1/\sqrt r)\) fruitless-cycle overhead. \(O(1)\) memory uses Brent/Floyd and has no table to retire.
- **Regime B.** \(b=\theta\sqrt q\) stored \(x\)-coordinates inside that interval. Baseline: one negation-BSGS table, average \(b+q/(4b)\) points at \(2.5M+S\). The point-count minimum is \(\sqrt q\) at \(\theta=1/2\). Field work there is \(c_x\sqrt q\), which is \(0.658\) times rho field work at \(s=1\) and \(0.642\) at \(s=0.8\).
- **Regime H.** \(\Theta(\sqrt q)\) abscissae, interleaved. Baseline: Galbraith–Wang–Zhang average \((2\sqrt 2/3)\sqrt q\approx 0.943\sqrt q\) generated points, with the H019 \(x\)-only limit \(2.5M+S\). At \(s=1\) that field work is \(0.621\) times negation rho. Bernstein–Lange grumpy giants and the H024 multi-family counting floors are the same regime.

One-shot use of the peak resident set is the comparator. A temporary larger table still counts as peak memory: the one-shot table at that peak is available to the baseline. Amortizing a table across unrelated targets is out of scope, including Kuhn–Struik retention and the Bernstein–Lange \(K\)-target balance.

## Card 1 — rebuild or slide interval tables

**Premise.** Cover a public interval of \(C\) scalars, evict the babies, retain only the interval bounds, and solve the complement with a fresh table. The hoped-for gain is that the checkpoint is \(O(\log q)\) bits and the second table is smaller.

**Accounting.** Let \(\alpha=C/q\) and \(\beta=b/\sqrt q\). With \(k\) uniform, phase 1 hits with probability \(\alpha\) at average cost \(b+C/(4b)\) and misses at worst-case cost \(b+C/(2b)\). The complement then costs at least \(\sqrt{q-C}\) under the same schedule. In units of \(\sqrt q\),

\[
\frac{E[W]}{\sqrt q}\ge \beta+\frac{\alpha(2-\alpha)}{4\beta}+(1-\alpha)^{3/2}.
\]

The minimum over \(\beta\) is \(f(\alpha)=\sqrt{\alpha(2-\alpha)}+(1-\alpha)^{3/2}\). For \(u=1-\alpha\in[0,1]\), \(\sqrt u\,(1+u)\le 2\), with equality only at \(u=1\). That is exactly \(f(\alpha)\ge 1\), with equality only at \(\alpha\in\{0,1\}\). Checked: \(f(0)=f(1)=1\) and \(f(1/2)\approx 1.220\).

So any nontrivial partition is strictly above one table of size \(\sqrt q/2\). Overlap only shrinks the union. A third phase repeats the same deficit on what remains. An adjacent rebuild from a saved endpoint still costs one addition per new baby. Sliding a window of width \(b\) while the giant stride stays large enough to avoid gaps never holds more than \(b\) keys, and every extra baby beyond the single optimal table is extra work. Both phases at \(x\)-only prices multiply the inequality by \(c_x\); a phase of full \(5M+S\) additions is wider of Regime H.

**Falsifier.** Already applied. A counterexample would be an explicit public two-phase schedule whose uniform-\(k\) expected generated-point count is strictly less than \(\sqrt q\), with peak resident \(x\)-keys at most \(\sqrt q/2\), both builds paid, and a miss paying a full cover of its phase. No curve run is needed to reject the card as stated.

## Card 2 — promote retired endpoints to a new lookup table

**Premise.** After a low-memory phase, keep \(M\) seeds or endpoints, discard the walk, and probe the retained set as the next table. The hoped-for gain is that the first phase’s points become free babies.

**Accounting.** Those points are not an arithmetic progression, so the factor \(4\) in \(q/(4b)\) is not available. Each stored \(x\)-class covers two group elements. Expected probes are \(q/(2M)\), and producing the set already cost the retired phase. The probe minimum alone is \(\sqrt{2q}\approx 1.414\sqrt q\) at \(M=\sqrt{q/2}\), before build cost, against structured \(\sqrt q\) and against rho’s \(0.886\sqrt q\) iterations. In Regime L, \(M\le 0.188\sqrt q\) gives \(q/(2M)\ge 2.66\sqrt q\) probes before the discarded phase is added. H015’s one-target reading of reusable endpoint tables has the same shape: setup of order \(\sqrt{qM}\) plus online of order \(\sqrt{q/M}\) is at least two square-root terms. For \(K=1\) that balance does not improve total square-root work. A second rebuilt table adds another setup term.

**Falsifier.** Already applied in the listing model. Reviving it requires a probe that certifies more than one unstructured resident key’s worth of candidates with a nonzero coefficient of \(k\), at incremental cost below one \(x\)-only key, without storing those candidates. That certificate is the whole claim.

## Card 3 — retire coalescent traps and rebuild the walk

**Premise.** Fill a distinguished-point table to a cap, evict part of it, and start a fresh phase whose collisions still use the retired work. The hoped-for gain is more coverage per retained slot than van Oorschot–Wiener seed replay.

**Accounting.** Under the same step function, group-collision time on the negation quotient stays the rho baseline. Resident traps affect detection delay, of order \(1/\theta\), and the chance of deleting the witness. Deleting a positive fraction of traps lengthens detection or forces replay. It does not reduce the leading iteration count below \((1+o(1))\sqrt{\pi q/4}\). Rebuilding with a different step function removes coalescence: the old endpoints fall into Card 2. Parallel walks that share one trap table are ordinary parallel collision search. Extra walks add group operations; they do not reduce total work for one target below serial negation rho. \(O(1)\) Brent/Floyd already stores no retireable table.

**Falsifier.** Already applied inside this heuristic model, which is the same model the rho baseline uses, not a proved expectation. A counterexample would be one named step function, one eviction rule, and a heuristic expectation strictly below that iteration count plus the baseline tail, with replay, null cycles, and restarts paid. A different collision law is a different algorithm and needs its own contract.

## Withheld on purpose

No new premise was available for these, so they are not re-carded:

- Retained giants across targets, and the memoryless hazard \(2R/q\). For \(K=1\) earlier targets contribute nothing. H031 replaces that hazard by the overlap recurrence on \(F_j\); the \(0.906\sqrt{qK}\) figure stays unestablished and is many-target.
- H032’s single frozen batch. Keeping the builder’s sorted descriptors matches endpoint capacity under the same construction peak. Lookup speed versus binary search is a separate claim and has no full-work premise here.
- Clocked or nonconfluent walks, and minhash or distinguished-point burst schedules. H031’s corrected burst and block-minhash ledgers already sit above negation rho on their own hypotheses.
- Pure reuse that never evicts. That is one BSGS table or one rho store.

## Scope

This is a listing-schedule result for explicit tables on one ordinary prime-order curve, full scalar range, \(\mathrm{Aut}=\{\pm 1\}\), synthetic input. It does not bound coordinate-adaptive walks, implicit equations, or a new image cheaper than the H019 gate. Rho iteration counts remain heuristic. The \(0.19\sqrt q\) edge is a field-work crossover for this schedule, not a bit-identical memory theorem. Primary PDFs were not re-fetched in this pass. The constants above are recomputed from the accepted in-repo ledgers in H015, H019, H020, H024, and the STATE baseline. In-repo texts read for the boundary include H031’s memory disposition, H032’s retrieval cards and capacity falsifier, H029’s trajectory screen, H030’s hierarchy scope, and H031’s packed-storage scope.

## Wave lines

- Best supported full work: unchanged. Regime L is negation rho; Regimes B and H are optimal signed \(x\)-only BSGS / interleaved GWZ.
- Verified improvement: NONE.
- Hypothesis tested: single-target phase reuse, retirement, or rebuild of collision tables.
- Evidence: the partition identity \(f(\alpha)\ge 1\), the unstructured \(q/(2M)\) probe count, and coalescent eviction adding detection cost rather than coverage. No numerical run.
- Next conclusion-changing object: an explicit schedule that breaks one of the three falsifiers above, with peak resident keys, reconstruction, and the nonzero coefficient of \(k\) written down. Another listing variant of the same three cards does not do that.
