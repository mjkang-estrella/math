# H047 Grok autonomous-search report — UNACCEPTED

2026-10-09 UTC. Provider grok / grok-4.7. Terminal completed, no pending children.
Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h047-autonomous-search-grok-20261009-r1`.
Raw proposal retained for independent review. No experiment admitted; H034 cap remains consumed.
Root preliminary concerns: card1 numerical cost ratios omit a squaring; card2 uses
negation labels for an affine reflection quotient; matching transition seeds,
restart scalar-multiplication costs, zero jumps and non-DP cycles need explicit handling.
These are objections awaiting review, not global impossibility claims.

The three H046 gates stay parked. No experiment is admitted. Verified complete-work improvement remains **NONE**: low memory is Bernstein–Lange–Schwabe negation rho, and square-root memory is x-only interleaved negation BSGS.

These three maps are different geometries. Each is a public function of its stated state, so equal states share a future. Usefulness is the replayed residue \(b_t-b_s\neq 0\), including opposite signs at the same power of 2. None is a survivor. The sibling map is the only one whose extra arithmetic is tied to a real branch a one-addition table cannot see.

## Card 1 — Sibling-min successor

**Operation.** The state is the canonical point \(\kappa(W)\) and a seed. Build \(r=16\) jumps by an explicit chain: \(T_0=O\), \(T_i=T_{i-1}+G\) for \(i<16\), and \(J_i=T_i+Q\) for odd \(i\), else \(T_i\). That is 23 additions, all charged. Let \(i=h(x(W))\). Compute the ordinary sum \(W+J_i\). From its saved denominator, form the sibling abscissa \(x(W-J_i)\) by the H019 identity (2M). Walk to whichever class has the smaller abscissa, then apply \(\kappa\). Finish \(y(W-J_i)\) only if the minus class wins.

**Detector.** A public hash of the canonical abscissa, independent of which sibling won. Store \((x,\mathrm{seed},\mathrm{step},\mathrm{walker})\). A match replays both seeds through \(g\) and accepts only when the replayed residues differ. Verify \(kG=Q\). There is no private ring. Unstored interior meetings are seen only at the later shared distinguished point; that is valid because \(g\) reads only \(\kappa(W)\).

**Labels.** Lazy, as in the negation-rho baseline. Replay applies \(\varepsilon(a\pm c_i,b\pm d_i)\) for the selected sign, then the canonical flip. Initialization is \((a,b)=(0,\sigma_0)\) when \(\kappa(Q)=\sigma_0 Q\). Handle \(Q=O\) before walking.

**Invoice.** One batched addition per walker, \(I+3(K-1)M\) for the \(K\) denominators, then \(+2M\) for every sibling abscissa and about \(+2M\) more for \(y(W-J_i)\) when minus wins. The ordinate identity is an unchecked derivation from the same intermediates as H019 and must be confirmed before any use. Leading step price \((7+2\rho_-)M+S\), where \(\rho_-\) is the fraction of steps that actually select minus. No second inversion. Equal-hash or fruitless patterns are not given the Bernstein–Lange–Schwabe \(\Theta(1/\sqrt{r})\) formula; this is not their map.

**Memory, restarts, cap.** Peak is \(K\) points, one sibling scratch each, 16 jump points, and distinguished records of one field plus seed and step. Match the control’s slot count. Two null replays, or a zero denominator, retire that walker and start \(\kappa(Q+[\rho]G)\) with a fresh public \(\rho\); abandoned steps and the start addition are charged. The cap is the paired control invoice, not \(4\times 0.886\sqrt{q}\). A cap hit is a censored failure at cap cost.

**Needed law.** Let \(T\) be the first distinguished match with replayed \(b_t\neq b_s\), including tails, null replays, and restarts. A low-memory win needs \(E[C(T)]<E[C_{\mathrm{BLS}}]\) at the same \(K\), slot count, and batch size. At \(s=S/M=1\) the step is at least \(8/6\) times a batched addition when \(\rho_-=1/2\), and \(7/6\) times even when minus is rare, because the sibling abscissa is always paid. So \(T\) must shrink by more than that factor. Image bias is not that shrinkage. If the slot count reaches the region where x-only baby-step giant-step is the stronger comparator, the control is \((b+q/(4b))(2.5M+S)\), not rho.

**Prior art.** A one-addition \(\pm J\) table is ordinary \(r\)-adding and is cheaper. H019 computes this sibling and does not walk to it. H031 pays two full additions. Bos tag-tracing is a different omission of \(y\).

**Assumption.** The min-of-two-classes map shortens useful distinguished hitting enough to pay the sibling. Uncertain and unproved.

**Falsifier.** Kill on paper if some point-only rule matches this successor and uses one addition. Otherwise the later paired test, not admitted now, is two full-order seeds at \(q\approx 2^{16}\): kill unless the summed \(M,S,I\), replay, retirement, and cap invoice beats a matched negation-rho control. Do not compare a median with \(0.886\sqrt{q}\).

## Card 2 — Sorted-pair translation, double only on \(z>u\)

**Operation.** The state is the H023 sorted pair for difference \(G\), size \((q+1)/2\), plus a seed. Always compute the differential translate \(z=(c_1+c_2/u)/u-v\). If \(z\le u\), the successor is the re-sorted pair. If \(z>u\), that is the label-cancelling 2-cycle bit already on the tape: discard the translate and double the represented point, emitting the sorted pair of \(([2]P,[2]P-G)\). Doubling is not evaluated on \(z\le u\). Translation is evaluated every step and is the accepted output only when \(z\le u\).

**Detector.** Hash the pair. Store the H022 one-field identifier \(\lambda\), the seed, and the step. Confirm by whole-pair equality on replay, then require \(b_t\neq b_s\). Equal powers of 2 with opposite signs are useful. Different powers can still be null. The test is the residue, not the valuation.

**Labels.** Replay only. An accepted translate increments the \(G\)-coefficient and applies the sort reflection \((a,b)\mapsto(1-a,-b)\) when the coordinates swap. A selected double sends \((a,b)\mapsto\varepsilon(2a,2b)\). Start at \((0,\sigma_0)\). Pure-\(G\) self-collisions are not automatically null, because a sign flip makes \(\Delta b=\pm 2b\).

**Invoice.** H023’s discarded-translate schedule: leading \(5M+\rho(11M+3S)\), plus \((I-3M)/n\) and a second inversion batch only in rounds that contain at least one double. Here \(\rho\) is selected doubles over trajectory steps, not a uniform density and not a hash rate. Setup is the pair constants and one inverse of \(2y_G\).

**Memory and failures.** Each walker holds two fields; scratch grows only on doubles; each distinguished record is one \(\lambda\). Same retirement rule as Card 1: two null replays, or an exceptional pair \(O\), \(G\), \(x=x'\), or a zero denominator, starts a fresh public translate of \(Q\). Shared slot count with the control. Same cap rule.

**Needed law.** At equal useful hitting time, the leading price beats \(5M+S\) only for \(\rho<s/(11+3s)\): about \(0.071\) at \(s=1\) and \(0.060\) at \(s=0.8\). Equal hitting time is not granted. Small \(\rho\) removes 2-cycles but also removes the non-injective branch that creates merges, so \(T\) can grow as \(\rho\) shrinks. The win condition is the product, \(E[(5+\rho(11+3s))T+\text{remainders}+\text{replays}+\text{restarts}]<E[C_{\mathrm{BLS}}]\). Above the x-only crossover, the control is again \((b+q/(4b))(2.5M+S)\).

**Prior art.** The pair, the \(5M\) translate, the \(z>u\) cycle, and the \(11M+3S\) escape price are H023. H046’s low-\(x\) and parity gates are not this bit. Negation and reflection give the same quotient size.

**Assumption.** Some trajectory occupation \(\rho\) makes the product smaller than negation rho. High uncertainty. No claim that \(\rho\) is small.

**Falsifier.** A uniform count of \(z>u\) is not an occupation. Kill only through the paired invoice, or by a proof that every trajectory has \(\rho\ge s/(11+3s)\) and \(T\) at least the control’s. Specified, not run. The H034 cap is not a license to census it.

## Card 3 — One pre-chosen operation, add or double

**Operation.** The state is only \(\kappa(W)\) and a seed. Use Card 1’s 23-addition jump table. Read \(\beta\), the least significant bit of \(x(W)\), before any arithmetic. If \(\beta=0\), add \(J_{h(x)}\). If \(\beta=1\), double. Evaluate only the chosen operation. Do not assume the occupation of \(\beta\) is \(1/2\).

**Detector and labels.** The same distinguished-point store and lazy replay as Card 1. Accept the replayed residue difference, with opposite signs included. No eight-point ring and no claim that a ring plus distinguished points sees every earlier visit.

**Cycles.** This map does not inherit a fruitless-cycle constant. A repeated null replay retires the walker and charges a public restart. That is the failure policy, not a proof that 2-cycles are absent.

**Invoice.** \((5M+S)+\rho S\), with \(\rho\) the observed doubling occupation, plus one batch remainder per round. Strictly dearer than an \(r\)-adding step whenever \(\rho>0\). Peak memory is \(K\) points, one-operation scratch, 16 jumps, and the shared distinguished-point slots. No \(8K\) history.

**Needed law.** \(E[C]<E[C_{\mathrm{BLS}}]\) requires the useful hitting time, tails, null replays, and restarts to shrink by more than \((5+s)/(5+s(1+\rho))\). Nothing in the marginal distribution of \(x\), and nothing in Miller–Venkatesan, supplies that shrink. A plausible outcome is a loss for every \(\rho>0\).

**Prior art.** One branch chosen from the current point is Pollard’s iterator; many jumps without doubling are Teske and Bernstein–Lange–Schwabe. Those are the comparators. This card is only the H046 double gate with the evaluation, label, detector, and stopping errors removed.

**Assumption.** Doubling on a positive-density bit shortens useful search more than one extra squaring costs. Unsupported.

**Falsifier.** The same paired censored invoice. Also kill a seed immediately if the first 32 replayed abscissa matches all have \(b_t=b_s\). That kills this jump schedule, not every double.

## Next decision

Do not admit a synthetic run, a cap reset, or a median-versus-\(0.886\sqrt{q}\) census.

The cheapest conclusion-changing step is a read-only review with three questions. Does any one-addition rule reproduce the Card 1 successor? If it does, Card 1 is strictly dominated. Is there a proof that Card 2’s trajectory occupation stays at least \(s/(11+3s)\)? If there is, Card 2 loses at equal hitting time, and it still needs a separate hitting argument if occupation is smaller. For Card 3, treat a loss at every \(\rho>0\) as the default until a trajectory invoice says otherwise.

Best supported work stays exponent \(1/2\). Verified improvement stays **NONE**.
