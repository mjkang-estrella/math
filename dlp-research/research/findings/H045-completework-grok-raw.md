# H045 raw Grok complete-work report — UNACCEPTED

2026-10-09 UTC. Provider grok / grok-4.7.
Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h045-independent-completework-grok-20261009-r1`.
Terminal task_status completed, no pending child runs. All new cost,
probability, scalar-extraction and lower-bound claims are unaccepted as written.
Completed independent review and corrections: H045-completework-disposition.md.

No changed complete-work construction. The exponent stays 1/2, and verified improvement stays **NONE**. Three schedules were invoiced far enough to compare with negation rho and with the proved x-only interleaved negation BSGS; none reduces complete work.

Baselines used are the accepted project records, not a new primary-paper audit. Low memory: Bernstein–Lange–Schwabe negation rho, heuristic \((1+o(1))\sqrt{\pi q/4}\approx 0.886\sqrt{q}\) iterations on the negation quotient, batched affine step \(5M{+}S\). High memory: the H019 specialization of Galbraith–Wang–Zhang interleaved negation BSGS, average \((2\sqrt{2}/3)\sqrt{q}\approx 0.943\sqrt{q}\) keys at limiting \(2.5M{+}S\) per abscissa. Square/multiply ratio \(s=S/M\) is kept symbolic. Expected storage is the stopping inventory, not a hard cap.

## 1. Sidon translates lose to signed BSGS on key count

**Operation.** Precompute \(n\) known-log points \(U_j=[s_j]G\). For centers \(C_i=a_iG+b_iQ\), emit the abscissae \(x(C_i+U_j)\). Hash those abscissae. A hit is an equality of negation classes.

**Extraction.** A positive hit \(C_i+U_j=C_m+U_h\) gives
\[
(b_i-b_m)k\equiv a_m-a_i+s_h-s_j,
\]
when \(b_i\neq b_m\). A negative hit \(C_i+U_j=-(C_m+U_h)\) gives
\[
(b_i+b_m)k\equiv -a_i-a_m-s_j-s_h,
\]
when \(b_i+b_m\neq 0\). One scalar multiplication checks \(kG=Q\).

**Collision cap, unconditional for this shape.** For an odd-order group the map \((C_i,C_m)\mapsto(C_i-C_m,C_i+C_m)\) is bijective. One unordered center pair therefore hits with probability at most \((\Delta+\Sigma)/q\), where \(\Delta=|S-S|\le n(n-1)+1\) and \(\Sigma=|S+S|\le n(n+1)/2\). Repeated differences only shrink \(\Delta\). So
\[
\Delta+\Sigma\le \tfrac32 n^2-\tfrac12 n+1.
\]
Generating centers sequentially, the cumulative hazard is at most \(0.75\,T^2/q\) at \(T=nB\) keys. The corresponding mean is
\[
\mathbb{E}[T]\ge \tfrac12\sqrt{\pi q/0.75}\approx 1.023\sqrt{q}
\]
keys. Interleaved x-only BSGS averages \(0.943\sqrt{q}\) keys at the same \(2.5M{+}S\) emission price. About 8.5% more keys, before center construction.

Independent centers are double scalar multiplications, \(\Theta(\log q)\) full additions each, \(\Theta(T\log q/n)\) group operations. A single orbit \(C_i=C_0+[i]R\) does not evade the cap: the covered scalars are at most \(T\cdot|S-S|\) values, and a Sidon set of size \(\sqrt{q}\) costs more to build than the AP already used by BSGS.

**Costs.** Offset precomputation is \(O(n\log q)\) full additions and an \(O(n^2)\) integer sort of sums and differences. Storage at stopping is about \(1.023\sqrt{q}\) abscissa/label records. Vanishing-coefficient hits are \(O(1/q)\) per colliding pair. This is high-memory work, so the matched comparator is signed BSGS, not rho.

**Prior art.** Same \(\pm\) abscissa emission as the H019 block schedule. The change is an unstructured offset set. That change lowers the collision rate.

**Premise.** None for the inequality. Distinct sums and differences are the optimistic case.
**Falsifier.** A set of \(n\) offsets with more than \(n(n+1)/2\) distinct sums, or more than \(n(n-1)+1\) distinct differences. Both are impossible.

## 2. Conjugate side probe: optimistic laws already lose at high memory

**Operation.** Negation-canonical walk \(W\leftarrow W+J_{h(x(W))}\), jumps precomputed. From the same denominator emit the full sum and the opposite abscissa \(x(W-J)\). Accepted H043 invoice: \(6M{+}2S+\varepsilon_K\), with \(\varepsilon_K=(I-3M)/K\), against \(5M{+}S+\varepsilon_K\) for the sum alone. Incremental opposite abscissa is \(M{+}S\).

**Extraction.** \(W-J=\pm S\) for a stored labelled point \(S\) is the ordinary linear equation in \(k\). The coefficient is nonzero when the \(Q\)-coefficients differ. Repeated jump \(J_{h(W)}=J_{h(W_{\mathrm{prev}})}\) makes the side the predecessor and the coefficient vanishes.

**Invoices, premises separated.**
- All-pairs among \(2n\) IID samples, every pair eligible: about \(0.443\sqrt{q}\) rounds. Work \((6+2s)0.443\sqrt{q}\). At \(s=1\) this is \(3.54\,M\sqrt{q}\), against \(0.943(2.5+s)=3.30\,M\sqrt{q}\) for x-only BSGS. About 7% more multiplication/squaring work. Both schedules use \(O(1)\) field additions per abscissa from the same chord formulas; that does not close the gap.
- Main-key two-probe, side not stored, IID hazard \(2t/N\): about \(\sqrt{\pi q/8}\approx 0.627\sqrt{q}\) rounds at \(6M{+}2S\). At \(s=1\), about \(5.01\,M\sqrt{q}\), roughly \(1.5\times\) the BSGS field invoice.

Storing every sample puts the schedule in the high-memory regime, where BSGS is the matched baseline. Under either optimistic IID law the schedule loses there. It beats plain rho only in the all-pairs IID model, and that model stores \(\Theta(\sqrt{q})\) keys.

The real side point is the translate \(W-J\), not an independent second sample. Correlation is not priced as harmful by default, and no dependence was found that adds enough useful hits to close the 7% gap. A low-memory distinguished-point table does not inherit the two-probe mean \(\sqrt{\pi q/8}\).

**Prior art.** H043 conjugate arithmetic and H019 chord bonus. Not a new quotient.
**Falsifier of a future gain claim.** Account every detected hit as predecessor, repeated-jump identity, or zero coefficient of \(k\), on one ordinary prime-order curve, and show the remaining useful hits do not pay for the extra \(M{+}S\).

## 3. Within-block negation does not repair progression blocks

**Operation.** Block \(i\): center \(C_i\), then \(P_{i,j}=C_i+[j]D\) for \(j=0,\ldots,\ell-1\), with \(D\) known-log and offsets not wrapping. Block arithmetic is \(C_f+(\ell-1)C_x\), not \(C_f+\ell C_x\).

**Extraction.** Positive matches inside one block are impossible under that offset rule. Negation \(P_{i,j}=-P_{i,h}\) is
\[
2C_i+(j+h)D=O,
\]
coefficient \(2b_i\). For \(j<h\) the sums \(j+h\) are exactly the \(2\ell-3\) integers \(\{1,\ldots,2\ell-3\}\). For a uniform center the hit probability is \((2\ell-3)/q\), not \(\ell(\ell-1)/(2q)\): repeated pairs witness the same sum.

**Leading term.** Cross-block hazard still sets the stopping scale \(B\sim\sqrt{\pi q/(8\ell-4)}\) under the H044 illustration (independent uniform centers, Poisson approximation). Expected within-block hits up to that time are
\[
B(2\ell-3)/q=O\bigl(\sqrt{\ell/q}\bigr)=o(1)
\]
for every \(\ell=o(q)\). They do not change the leading coefficient. The H044 illustration with \(C_f=6\), \(C_x=3.5\) stays near \(4.83\,M\sqrt{q}\), against \(3.5\,M\sqrt{q}\) for the field-only BSGS coefficient at \(s=1\), and against \(0.943(2.5+s)\) for the proved key count.

Using only within-block hits is a point-in-a-known-set test: \(\Theta(q/\ell)\) centers, which is BSGS when the set is large.

**Premise.** Cross-block independence is the H044 illustration, not a theorem about a one-addition remix. The within-block count for a uniform center is exact.
**Falsifier.** An offset interval of length \(\ell<q/2\) whose distinct negation sums exceed \(2\ell-3\). They do not.

## Preserved failures

The degree-2 sum feature \(\phi(t)=x(W{+}J)+x(W{-}J)\) has the H044 Möbius partner as its nontrivial fiber. Specified recovery: on a feature hit, solve for the partner abscissa, take both square roots, and test the linear equation. The partner is not a group translate when the anchor has odd prime order, so each square root is an unlabelled point whose discrete log is a new instance. No scalar is extracted.

A co-Z step at the accepted H043 counts \(6M{+}3S\) or \(5M{+}3S\), plus a later inversion to canonicalize an abscissa, is not cheaper than batched affine \(5M{+}S\). Jacobian walks that invert only at distinguished points still pay a mixed addition above \(5M{+}S\).

One arithmetic progression with a changing \(Q\)-coefficient, advanced by full additions, has only the within-block negation event. That is \(O(T/q)\) success after \(T\) steps, not a birthday.

## Wave report

- Best supported estimate: exponent \(1/2\), with negation rho at low memory and H019 x-only interleaved negation BSGS at square-root memory. No tighter complete-work bound.
- Verified improvement: **NONE**.
- Hypothesis under test: none retained. The Sidon-translate schedule is an unconditional loss for that shape; the side probe has no justified useful-event surplus; within-block negation is \(o(1)\) on the birthday scale.
- Evidence for a gain: none. Evidence against: the three invoices above.
- Next conclusion-changing object: a public successor on at most the negation quotient whose full step is strictly below one batched \(5M{+}S\) addition, with an affine label, a nonzero coefficient of \(k\), and a useful-hit law; or an x-only key generator at \(\le 2.5M{+}S\) whose eligible collisions give hazard \(\alpha T/q\) per new key with \(\alpha\) large enough that the mean key count times that price undercuts \(0.943(2.5+s)\). A one-addition remix is not that law.

No experiment, file change, import, or child process. H034 was not touched. H006 and the H038 Farey/height-lattice route were not reopened.
