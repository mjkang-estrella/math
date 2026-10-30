# Independent adversarial review: all-odd randomized subtraction

Date: 2026-10-26. Reviewer: matrix lane. Verdict: **mathematics PASS; exact primary-source scope PASS; independent formal replay PASS for the audited bytes; novelty screen provisionally favorable.** This is one proposed resolution of a primary-source open question, not a resolution of the neighboring MathDB363319 conjecture.

The reviewed proof snapshot is `proof-reviewed.md`, SHA256 `a2c2b57f332aef39de699815633d8def114d67edc96651051eb710f8ff4eae2d`. Source bytes and hashes are in `provenance.json`. The candidate and its formal modules remain owned by the originating worker/parent and were not edited during this review.

## Exact target

I independently retrieved and read Capitelli–Somma, [arXiv:2405.19593v1](https://arxiv.org/pdf/2405.19593v1), particularly the complete game definition in §1, the opening of §3, Proposition3.1, the discussion surrounding Question3.4, and §4.1. The game chooses uniformly among **currently legal** subtractions; an empty legal set loses. The missing general all-odd nonconvergence result is explicitly identified in §3. Question3.4 asks for nonvanishing of the coefficient of the root−1 in that context. The source already handles sets of size below3.

The proposed result covers every nonempty finite set of positive odd integers and the actual recursively determined winning-probability sequence, including every initial heap. It is a substantive universal extension beyond those known cardinalities. An additional gcd1 hypothesis belongs only to the claimed two-limit/amplitude formula. No new claim is needed for singleton sets, two-element sets, or sets containing1 individually.

The neighboring MathDB363319 record (UUID `6ae41215-5eb0-4498-ae0d-7b2e9ce64872`, snapshot preserved) extracts **Conjecture3.3: all characteristic roots simple**. This proof bypasses that conjecture. Do not identify the present outcome as proving MathDB363319. The primary-source question is the correct target identifier. The omission of “all odd” in the isolated wording of Question3.4 is resolved by its immediately preceding context, not used to manufacture a typo counterexample.

## Independent proof checks

Write E_n={k∈S:k≤n}, D=maxS, t=|S|, K=Σk. I checked the following deductions independently.

1. The coupled induction proving a_(2m)≤a_(2m+1) and a_(2m+2)≤a_(2m+1) uses only previous inequalities. At an odd heap and the following even heap the eligible sets coincide. Subtracting any odd move gives the previous even/odd pairs in the needed order. For an even heap and the following odd heap, the only possible newly legal move is the entire new heap; its follower has probability a_0=0. Adding that zero lowers the average when the old set is nonempty. **The old empty-set branch must be explicit:** the old probability is0 and the new probability is nonnegative (indeed0 or1). The worker has confirmed this branch is explicit in the current Lean proof.

2. For c_n=(-1)^n(1−2a_n), the complete eligible-move recurrence becomes |E_n|c_n=Σ_(k∈E_n)c_(n−k). This also holds when E_n is empty, as0=0. It does not impose the eventual full recurrence on the initial positions.

3. For an odd h=2q+1, C(h)=Σ_(j<h)c_j equals1+2Σ_(j=1..q)(a_(2j−1)−a_(2j)), so C(h)≥1. All terms, including index0, are accounted for.

4. The finite-window quantity I_n=Σ_(k∈S)Σ_(j<k)c_(n+D−k+j) satisfies I_(n+1)−I_n=t c_(n+D)−Σ_(k∈S)c_(n+D−k)=0. Every index is nonnegative; all moves are available at n+D, including n=0.

5. Summing the variable-eligibility recurrence over n<D gives Σ_k(C(D)−C(k))=Σ_k C(D−k). This proves I_0=Σ_k C(k)≥t>0. The k=D term is an empty inner sum on both sides where appropriate. The argument requires only the equality of the **total** suffix and prefix sums; an equality for each k separately would be false and is not used.

6. If a_n→L, the eventual full recurrence gives L=1−L, so L=1/2. Therefore |c_n|=|1−2a_n|→0. Each finite shifted term of I_n tends to0, contradicting the positive constant I_0. This proves nonconvergence without gcd or root-simplicity assumptions.

7. Under gcdS=1, the root localization in Proposition3.1 gives exactly one unit-modulus root,−1, and it is simple. Repeated roots strictly inside the unit disk contribute polynomial factors times decaying powers, so no assumption that all roots are simple is needed. Thus a_n=1/2+α(-1)^n+o(1), c_n→−2α, and I_n→−2Kα. Consequently α=−Σ_k C(k)/(2K)≤−t/(2K)<0. Both the sign and normalization are correct. The source's general simple-root display should not be invoked without the standard repeated-root correction just described.

For gcdS>1 there may be more than two peripheral modes, so the two-limit formula must retain gcd1. A broader convergence classification for arbitrary finite sets must first normalize S by its gcd: an unqualified claim “contains an even move implies convergence” would be false, for example S={2,6}. The reviewed candidate does not make that broader unqualified claim.

## Prior-art screen

I independently read the primary companion Capitelli–Privitelli, [arXiv:2012.06768v1](https://arxiv.org/pdf/2012.06768v1), §§2–4. It supplies the general noisy-channel recurrence, a sufficient fairness criterion (Lemma7), and unrestricted Nim examples. It does not establish the all-odd finite-subtraction nonconvergence or amplitude result; §4 explicitly lists other subtraction sets as further study.

I also read the relevant primary Cairns–Ho paper, [*Ultimately bipartite subtraction games*, AJC48 (2010),213–220](https://ajc.maths.uq.edu.au/pdf/48/ajc_v48_p213.pdf). Its Theorem1 covers the forced-parity case containing1; its Theorem3/Lemma3 gives a related qualitative predecessor property for losing positions under optimal play. Those results concern nim values/strategies, not the uniform-random winning probabilities or their positive limiting amplitude for all odd sets with minimum greater than1. They deserve acknowledgement as related parity/coupling context, but do not resolve the present probability statement.

Live searches on2026-10-26 included exact title, arXiv identifier, author pair, and combinations of randomized/randomly played subtraction games with odd, nonconvergence, amplitude, and zigzag. The current arXiv abstract record lists onlyv1 and no journal reference. Results located the original preprint and mirrors, the earlier noisy-channel paper, and optimal-play periodicity/bipartite papers. No primary subsequent resolution of this exact probability question was located. Citation/profile mirrors are search leads only, not evidence proving absence of literature.

**Novelty assessment:** unlike the excluded coefficient-positivity candidate, I found no explicit older theorem containing this full result as an immediate specialization. The2024 primary source explicitly leaves it open. This is favorable evidence for pursuing the candidate, not a guarantee of priority or an authorization to increase the strict tally before complete formal review.

## Independent formal replay

I read all five substantive modules independently. `Model` includes the empty-set rule, probability bounds and the full eligible balance. `gameWin` recursively averages legal positive moves; `gameWin_model` supplies the source-to-model bridge under positive moves. `model_unique` independently guarantees that any sequence satisfying this complete recurrence coincides with the recursively defined game. These interfaces match the source.

The parent's `GameInvariant.lean` exactly formalizes the centered balance, finite prefix/suffix identity, and conserved window. Its `GameLimits.lean` proves the half-limit implication, the norm-based centered limit, vanishing finite shifted windows, and the final contradiction. Natural subtraction is always guarded by the supplied bounds where finite identities require it; eventual natural subtraction in limits is correctly handled by atTop lemmas.

I copied the modules into this review's owned directory and added `ReviewEndpoint.lean`, whose theorem `OddSubtractionReview.actual_game_not_tendsto` instantiates the complete model with `gameWin`. Its only assumptions are nonempty finite S and k%2=1 for every k∈S; its conclusion is nonconvergence to every arbitrary real L. Positivity of each move follows from oddness. There is no invariant, zigzag, spectral, nonvanishing, or unproved existence hypothesis.

Fresh independent replay of **35 authored declarations, including the Model structure and the review endpoint**, passed Lean4.34.1 with warnings treated as errors. All inspected axiom lists are subsets of {propext, Classical.choice, Quot.sound}. The build uses fresh local oleans and the assigned pinned dependency build. No git operation was performed. Script: `audit.py`; complete receipt: `build/fresh-audit-450totn2/receipt.json`; logs and explicit declaration checks are in that directory.

| Audited module | SHA256 |
|---|---|
| GameRecurrence | `9fd50c479ec8a3337ee645647ab6442883d2ef007eb8a13ae000c8d90297c71c` |
| GameZigzag | `c74b0854bafe888a1221ced4c89524b36f149096b66d53a3584c6038413a8957` |
| GameDefinition | `76f521523cb91743e8a6d65b2b4d34b5d17ce886ea34409adc0f3becb856f5ec` |
| GameInvariant | `aa06a5ec44d9a8391297f9f8a84c7ee9ad429e6862191436cc578a6c613f5e4b` |
| GameLimits | `fe84aaebb4e7714f171354c41ce4aed395a78ffb7a94ce160d05376c1e651b47` |
| ReviewEndpoint | `3f774ff9ee106820fe683b9016ed248cdc6ec72ceaaa245b625359af320313ba` |

### Frozen six-module canonical replay

The final parent-owned endpoint was subsequently frozen and independently reviewed. Its sixth module is `GameNonconvergence.lean`, SHA256 `715e19596e3f7fc79dc24dba6c603c744c967bbbae279807501ef42c8591d597`; its first five module hashes are exactly those in the table above. This supersedes the review-only wrapper for release purposes. I read all three additional declarations: the invariant lower bound is proved for every full-move window, the actual-game nonconvergence theorem negates existence of any real limit, and the final invariant endpoint uses the exact `gameWin` definition. No additional assumptions or scope narrowing were introduced.

I copied the exact final six modules and manifest into `final-replay/` and ran the root `verify_candidate.py` there at the parent's explicit request. Its read-only pinned dependency metadata checks passed; output remained in the owned review directory. **Canonical replay PASS: 37 authored declarations, warnings-as-errors, only propext/Classical.choice/Quot.sound.** The count includes `Model`. Receipt: `final-replay/build/verified/audit.json`, SHA256 `96bdd3a6b598ba3d23d8aeb46340bdff6a3021f118d31b21ad1341d2bfbfc3df`. Invoked root verifier SHA256: `83220516930d62995ce2db3587e854389be6d25270f37d38dbe0836357062479`.

The formal certificate proves the full counted nonconvergence target and positive invariant. The parent has confirmed that the manuscript will claim those certified conclusions; Question3.4 is motivation and no formal spectral/existence/amplitude bridge will be asserted. This is the appropriate scope.

**Acceptance recommendation:** accept the mathematics, source interpretation, and frozen formal certificate as one complete substantive resolution of the primary §3 all-odd nonconvergence conjecture. The independently searched novelty evidence is provisionally favorable; retain the explicit search limitation rather than claiming demonstrated exhaustive priority. Do not credit the still-open neighboring root-simplicity conjecture, auxiliary lemmas, or known small cases separately.

### Final frozen manuscript review

I independently read the complete final `candidates/odd-subtraction/main.tex`, SHA256 `81af255744b239ebd6eafae5ab91c1f1ced1361f65263cc50d3b995b2a2e31fb`. **Text, mathematics, source scope and formal-scope review PASS.** The stated recurrence includes all initial empty/legal branches; the induction, prefix computation, conserved window and initial-value identity have the correct ranges. The theorem has no gcd restriction. The formal claims match the replayed37 declarations and two endpoints. No spectral/amplitude existence bridge is claimed; the distinct MathDB363319 problem is clearly excluded. The prior-art limitations and the known small-cardinality cases are presented accurately. No mathematical or scope correction is required for these frozen paper bytes. This is a TeX text/mathematics review; the parent owns PDF rendering and visual layout checks.

Final layout-only delta: the release TeX SHA256 is `2305a466e1632f06f1f749a86f38b6b47f4fc7aaa253711c631e5983804285e7`. I verified byte-for-byte that replacing its geometry option `[margin=1in,top=0.9in,bottom=0.9in]` by `[margin=1in]` reconstructs exactly the reviewed `81af255744b239ebd6eafae5ab91c1f1ced1361f65263cc50d3b995b2a2e31fb` bytes. All mathematical and textual content is unchanged; this final layout hash is covered by the same PASS. Parent owns the reported clean three-page visual inspection.
