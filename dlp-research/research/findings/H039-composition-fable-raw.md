# H039 complete-work composition report — raw testimony

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h039-completework-composition-fable-20261008-r1`

Provider/model: acpRegistry_factory_droid/claude-fable-5.1. COMPLETED, no pending
children. Terminal summary referred to an earlier full report, so root recovered
that untruncated report from backing-thread message position34 via t3_thread_read.
No child-thread continuation or new review round was sent. All claims below
remain subject to independent review; no primary source was freshly fetched.

# H039 independent proposer report (Factory Claude Fable 5.1), lens: compositions across memory tiers, reusable preprocessing, restart/search policies

**Outcome: no surviving card.** Verified improvement remains NONE; best supported classical exponent 1/2 unchanged. Three compositions were worked out far enough to be killed on paper with exact formulas; the rest reduce to in-repo baselines. I report the computed negatives because they are cheap for root to recheck and they close this lens more tightly than the existing H033 restart screen does.

Process: read-only. Read RESEARCH_LOOP.md, RESEARCH_TEAM.md, STATE.md (through the H022/H023 history), and findings H002 tradeoff cards/review, H013, H015, H019, H020, H029 parallel, H030 hierarchy, H031 memory/packed-storage, H032 retrieval, H033 stopping/lifecycle/self-reduction, H038 low-memory. Did not open `hypotheses/H039-independent-briefs.md` or any H039 proposal. No runs, imports, edits, files, children, network fetches. All arithmetic below is by hand and needs independent recomputation. Unit conventions follow H019: walk step c_w = 5M+S, paired progression key c_b = 2.5M+S (asymptotic limit; finite Cx(k,ℓ) is larger), s = S/M, numbers quoted at s = 1. Field additions, DP tail, cycle handling and verification omitted equally on both sides unless stated.

## Screen 1: rho walk boosted by a per-step-queried progression table (hybrid rho/BSGS)

**Operator.** Precompute b signed babies x(iG), i ≤ b, in a hash table (reusable, target-independent, charged). Run ordinary negation rho with DP detection. Additionally look up every walk point's x in the baby table. Hit X = aG+bQ = ±iG gives k = (±i − a)/b, b ≠ 0; verify. Walk–walk collisions are detected as usual via DPs.

**Why it looked worth pricing.** A baby is a visited point costing c_b that offers the same per-step hazard against the walk as a walk point costs at c_w, so W'(0) = c_b − c_w − P_L < 0 whenever per-step lookup P_L < 2.5M: small tables always help in the ideal model. The question is how much.

**Exact ideal-model expectation.** In the negation quotient (size q/2), hazard at step t is 2(t + b)/q, so survival is exp(−(t² + 2bt)/q) and with b = β√q

  E[T] = √q · e^{β²} · (√π/2) · erfc(β).

β = 0 recovers 0.886√q. Total work W(β)/√q = c_b β + (c_w + P_L) g(β), g(β) = e^{β²}(√π/2)erfc(β). Numbers (P_L = 0): β=0.05: 5.21; β=0.10: 5.12; β=0.20: 5.00; β=0.33 (optimum, from βg(β)=0.208): 4.95, versus rho 5.32. Maximum saving 6.8%. Signed BSGS at the same memory costs c_b(β + 1/(4β)): 3.81 at β=0.33 and 5.07 at β=0.20; crossover near β≈0.205. So the hybrid beats BSGS only where its gain over rho is ≤6%, and that gain is before per-step lookup: at β=0.2, P_L must be < 0.44M to break even against rho (rho's DP lookups are negligible). H035 prices the fused hash alone at about M+A, so a realistic P_L ≥ 1M makes the hybrid lose at every β. Interleaving baby growth b(t)=γt does not help: W ∝ (c_w + c_b γ)/√(1+γ), minimized at γ = 0 in this model (the birthday square root penalizes cost rate more than added hazard helps).

**Full-range regime.** Gain ≈ (2.5M − P_L)β√q to first order; feasible β at 128-bit scalars is ≤ 2^-80, so the saving is nil for the full-range task. Only memory-rich synthetic sizes see a few percent, where signed interleaved BSGS is already the stronger comparator.

**Prior art (not re-opened this session).** This is the tame-set/table idea of Gaudry–Schost and Bernstein–Lange precomputation (H015) with full per-step lookup instead of DP filtering; the exact erfc expression and the dominance comparison are my only additions. **Unsupported assumptions:** ideal uniform collision law for walk points and babies, c_b asymptotic cost, nonadaptive table. **Cheapest falsifier:** already done on paper; a run would only recheck g(β). **Verdict:** rejected, scoped to this ideal model.

## Screen 2: distinguished-point compression of a known-log progression table

**Operator.** Generate the progression iG, i ≤ N, store only the θN distinguished ones; make giants translation walks (stride sG) that are looked up only at DPs, so memory is θN and per-step lookups vanish.

**Why it fails exactly.** A wild stride walk hits the stored set only through its own DP points; intermediate points cannot be detected (no trail from an unwalked baby ever reaches a DP record). So each wild DP is one effective giant with hit probability 2N/q... but it is a DP only with probability θ, so per 3.5-unit wild step the useful hazard is 2θN/q = 2M/q. Work is c_b(N + q/(4M)) with M = θN, strictly worse than plain BSGS c_b(M + q/(4M)) with the same memory M: identical giant work, N ≥ M babies generated. DP compression of a progression table is equivalent to a smaller progression table bought at the larger generation price. Also the general lesson: cheap (2.5M+S) known-log coverage can only be exploited through per-point lookup, never through DP detection; cheap coverage + DP detection is incompatible. This complements, but is not, the H033 "probe minimum √(2q)" correction. **Verdict:** rejected, no assumption beyond the uniform-target coverage count.

## Screen 3: observable-dependent restart/abort policies (closes the gap H033 left open)

H033 screened time-only IID cutoffs and fixed portfolios and explicitly left "informative observations" open. Claim for root/independent check: in the generic group model, before the first nontrivial collision the transcript (labels of distinct formal combinations aG+bQ) is distributed as uniformly random distinct strings for every k, so any adaptive policy's query sequence is independent of k; the posterior on k after a collision-free prefix is uniform on the non-excluded scalars (exclusions being exactly H033's paid-information set), and the hit probability of any next query is a deterministic function of the retained formal query set. Hence (i) no observable-dependent restart/abort policy can beat the best deterministic-time policy, (ii) retaining accumulated coverage is never worse than discarding it, and (iii) parallel DP rho, which starts a fresh walker after every DP while keeping the table, is already the maximal retained-coverage "restart" policy. Together with H033's renewal argument under increasing hazard, this leaves no restart/search-policy card in the generic model. **Scope:** generic model only; coordinate-aware observables are not excluded, but none has been supplied with a correlation to k. Not a Lean claim; needs an independent reader. **Verdict:** no card; scoped lemma recommended for retention.

## Compositions discarded without a new screen (all reduce to in-repo baselines)

- **Two-tier DP store (RAM + disk sort-merge) to cut the W/θ tail.** The tail term is H020's n/D; raising capacity via a disk tier is known practice (H030 Fable raw §bandwidth, W004/W009) and must be granted to the baseline. No mechanism, regime statement only: it matters when walkers/capacity is not negligible.
- **Memory-rich disk BSGS (β≈0.3–0.5 on slow media, batched sort-merge giants).** Field work c_b(β+1/(4β)) beats rho by 25–35%, but this is the existing "H019 where memory permits" comparator; infeasible at full range.
- **Fixed-difference paired walk steps.** Two full successors from one inversion cost 7M+2S (3.5M+S each) but one branch must be dropped: dropped siblings are undetectable ("dark"), so cost per continued step is 7M+2S > 5M+S. Storing siblings for per-step lookup reduces to Screen 1 economics. Same as H029 Card A; nothing new.
- **Walk–giant lookups, retained giants, self-reduction, lifecycle eviction.** H031 Card 1 (multi-target), H033 self-reduction, H033 lifecycle; same economics as Screen 1.
- **Preprocessing with K = 1.** √(qM)+√(q/M) ≥ 2√q (H015); any generic preprocessing+online algorithm is a generic algorithm, so no exponent change from composition. Not a coordinate-aware exclusion.

## Source access

No primary PDF was opened this session. References used are those already read and recorded in-repo with URLs: GWZ 2017 (H019), Bernstein–Lange cuberoot (H015), Bernstein–Lange–Schwabe negation (H013), van Oorschot–Wiener (H029/H030), Luby–Sinclair–Zuckerman (H033), Kuhn–Struik and grumpy giants (H031). Gaudry–Schost and the generic-model preprocessing bounds (Shoup; Corrigan-Gibbs–Kogan) are cited from memory and are unverified here; no novelty claim depends on them.

## Suggested next decisive step for this lens

None warranting a run. The structural reason is that, at feasible memory, generic compositions can only buy ≈(2.5M − P_L)β√q, and at infeasible memory signed interleaved BSGS dominates. A conclusion-changing result would need a coordinate-aware observable correlated with k (reopening Screen 3) or a known-log coverage source priced below 2.5M+S with per-point detection cheaper than a RAM lookup; neither is supplied by this proposer.

## Terminal summary

Report delivered above. Summary for root: no survivor under this lens; three exact paper screens (hybrid rho/BSGS erfc formula with ≤7% ideal headroom dominated by BSGS and erased by per-step lookup; DP-compressed known-log tables equivalent to smaller tables; generic-model transcript independence closing observable-dependent restart policies) plus a list of compositions that reduce to existing H015/H019/H020/H029/H031/H033 baselines. No files, runs, edits, children or primary fetches; H039 proposals and briefs unread.

---
*Factory usage — local bridge. This turn: 1,003,315 tokens · ≈2,253,348 Factory credits. Saved session total: 1,003,315 tokens · ≈2,253,348 Factory credits (including recorded subagents). Credits are a local estimate, not a dollar charge.*
