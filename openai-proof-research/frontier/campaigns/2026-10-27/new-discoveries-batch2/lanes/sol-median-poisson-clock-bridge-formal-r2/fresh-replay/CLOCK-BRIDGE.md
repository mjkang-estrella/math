# Unclosed clock-realization theorem

This is a mathematical construction and specification, **not a kernel-certified theorem**. `ClockMarginals` and `MarkedCounts` do not establish the assertions below. In particular, a different space for each prefix length does not supply clock paths.

Fix an arbitrary real T>8. A tractable candidate probability space is the disjoint union, over n≥0, of

`Config × (Fin n → Fin 10) × (Fin n → [0,T])`.

Its n-th component has mixing weight exp(-10T)(10T)^n/n!, initial law `initialLaw`, independent uniform marks, and independent uniform times. Conditional on n, all three factors are independent. The count is finite at every sample. Except on a null set, all sampled times are distinct and avoid 0,T. Sort by time and carry each mark with its time. Every t∈[0,T] uses the prefix with time≤t from this single sorted list; this supplies consistent trajectories on the whole horizon. No ineffective update is removed.

## Joint increments, not terminal counts

For every integer m≥1 and strictly increasing partition 0=a₀<…<aₘ=T, let cᵢⱼ be any array of nonnegative integers, indexed by vertex i and interval j. Put Δⱼ=aⱼ₊₁-aⱼ and n=Σᵢⱼ cᵢⱼ. Before sorting, each time-mark pair falls in cell (i,j) with probability Δⱼ/(10T). The multinomial number of assignments of n labelled events to the cells is n!/∏ᵢⱼ cᵢⱼ!. Multiplying its conditional probability by the Poisson mixing weight gives

`P(∀i,j, Cᵢⱼ=cᵢⱼ) = exp(-10T) ∏ᵢⱼ Δⱼ^(cᵢⱼ)/cᵢⱼ!`

`= ∏ᵢⱼ [ exp(-Δⱼ) Δⱼ^(cᵢⱼ)/cᵢⱼ! ].`

This factorization for **every** partition proves joint independence of all vertex/interval counts and rate-one Poisson increments. Arbitrary disjoint intervals can be refined to a common partition, adding the unused gaps and marginalizing their counts. Zero-length intervals have deterministic zero increments; repeated partition points can consequently be admitted. Independence of the ten whole clock paths follows first for finite collections of evaluations and then for their generated cylinder sigma-algebras. Initial configuration is independent of the entire event sample by product construction, hence independent of every such clock cylinder. These last sigma-algebra and measurability steps must also be formalized; a one-time count factorization is insufficient.

For t≤T, the number Kₜ of times≤t is Poisson(10t), by the two-cell version followed by summing the second count (or binomial thinning). Conditional on all times and the total count, sorted marks remain iid uniform because sorting is a permutation determined only by times. Selection of the prefix also depends only on times. Hence conditional on Kₜ=k, its chronological word has mass 10^-k, and for each ordered length-k word w,

`P(Kₜ=k and wordₜ=w) = exp(-10t)t^k/k!.`

The common mark in two rings need not differ. Ineffective rings are included. Endpoint nullity justifies closed versus open interval choices. At t=0 the empty word has probability one.

## Exact missing theorem, with all residual assertions exposed

Required existence statement `exists_finiteHorizon_independentClocks(T,hT)`:

There exist a measurable probability space (Ω,P), measurable S:Ω→Config and a measurable finite marked event-list variable E:Ω→List(ℝ×Fin10), such that:

1. `P.map S = initialLaw`.
2. Almost surely E has strictly increasing time coordinates in (0,T), so all counts are finite and no two clocks ring simultaneously, simultaneously for all t∈[0,T].
3. For **all** m≥1, **all** strictly increasing partitions a of [0,T], **all** count arrays c, and **all** configurations s,

   `P{S=s ∧ ∀i,j, #{e∈E: e.mark=i ∧ aⱼ<e.time≤aⱼ₊₁}=cᵢⱼ}`

   `= initialLaw{s} * ∏i,j poissonMeasure(Δⱼ){cᵢⱼ}`.

4. For **all** real 0≤t≤T, natural k, predecessor words `w : MedianTemporal.Word k`, and configurations s, the event `S=s` and the chronological marks up to t equal w has real probability

   `MedianTemporal.weight s / 5^10 * exp(-10t)t^k/k!`.

5. Let `Xₜ(ω) = MedianTemporal.wordUpdate (marks(E(ω)≤t)) (S ω)`. Prove its measurability and identify its expectation at predecessor `bit` with

   `exp(-10t)/5^10 * Σ'k, t^k/k! * Σs, weight s * iterate k bit s`.

Here `poissonMeasure(Δ)` means the pinned distribution with nonnegative real parameter coerced to NNReal. The Word/list conversion must be defined and verified. Items 2–4 must concern the **same** E, S, P, not horizon- or query-dependent replacements. The statement is specified mathematically with exact quantifiers; it is not advertised as a compiled Lean declaration. No existence axiom or assumed instance implementing this interface has been added.

Once 1–4 are proved, 5 requires countable disjoint partition of Ω into (s,k,w) fibers, integrability of the [0,1]-valued bit observable, the already checked `iterate_all_words`, and the summation rearrangement. None of these analytic/probability links is claimed proved here. The fixed-horizon construction suffices locally around t=8; no extension to all positive horizons is needed for a local derivative counterexample, but the derivative/tails and median transfer are separate open formal obligations.

The checked contribution is the initial product measure and independent count/mark-prefix cylinder laws. `marked_mass` accepts an explicit arbitrary probability measure q on ℕ; it does **not** assume or assert that q comes from clocks, nor that its marks are chronologically sorted event marks. Instantiating q with a Poisson distribution and calling that the source process would leave precisely the missing theorem above.
