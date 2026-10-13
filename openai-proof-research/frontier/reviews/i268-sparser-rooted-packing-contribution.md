# I268 — Independent contribution review of sparser rooted packing

2026-10-12. **Verdict: TECHNICAL.** I267 makes a meaningful polynomial enlargement of I248's density range and crosses its coarse-concentration barrier. The additional mechanism is nevertheless a standard optimum-witness self-bounding argument, coupled with stopping an existing permutation martingale at the last relevant position. On the actual primary comparisons and the mathematical mechanism, this is a useful technical strengthening of the same chain, insufficient for a substantial finding under this project's bar. **No full proof-gate PASS or FAIL is issued.** Exact worldwide priority remains unresolved; KNOWN is not supported by an identified prior rank-transfer theorem.

The complete 129-line I267 proposal was independently read and authenticated against the requested SHA256 `1c78b41082673289a3740200bc5e0c0ed17776e49a3bf02dc561ba6a3261878f`. Its analysis, read record, authentication and literature, including both original BLM excerpts, were read in full. Original I248 proposal and complete analytic proof, completed I257 review and reconstruction, and completed I258 review, analysis and literature were independently read. I257's PASS concerns only the old density range and supplies no correctness verdict for I267. All OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. Own-thread configuration confirmed GPT-6.1 Sol/high/default (Standard). No author rebuttal or acceptance is inferred.

## Exact statement assessed

Fix d≥2. For sufficiently large n depending only on d, let 1≤s≤10 log n, 0<r<1, b=ds+binom(d,2), and

    r^b ≥ δ_n = n^(-1/3)(log n)^2,
    p = 1−(1−r)^(128d).

The proposed deterministic source and target classes D(n,r,s,d), E(n,r,s,d) have probabilities 1−o(1) under G(n,r), G(n,p), uniformly over permitted r,s. For every G∈D, H∈E, root set Y with |Y|≤n^(2/3), and family R of d-slot edge-presence patterns,

    ν_R(H;Y) ≥ min{2d ν_R(G;Y), floor((n−|Y|)/(16d²))}.

Each slot has at most s required root neighbors; its internal required graph is arbitrary. Nonroots of different packed blocks are disjoint. Root reuse, overlap and repetition are unrestricted. Roots and the family can be chosen after seeing both hosts: this is the entire Cartesian product D×E. There are no nonedge constraints or nonroot candidate lists; d is fixed; the linear cap and bounded-component application are unchanged. Uniformity of errors does not mean one pair of classes for every real r simultaneously. The application is part of the I248 chain, not another finding.

## What the new range actually accomplishes

Let ρ=r^b, N=n−|Y|, τ=1−(1−r)^2 and μ_Q=Eν_Q(G(n,τ);Y). Compression retains O_d(ρ^(-1)) patterns. A predetermined partition alone gives μ_Q≥floor(N/d)ρ. At the new endpoint the **guaranteed lower supply** is of order n^(2/3)(log n)^2. This is a lower bound; individual tests can have much larger actual means. All root and compressed-family tests cost

    A_d(n)=O_d(n^(2/3)log n+n^(1/3)).

The old relative-deviation exponents μ_Q²/n and q²/n, evaluated on the new guaranteed scale with q comparable to μ_Q before the cap, are only of order n^(1/3)(log n)^4. They do not dominate n^(2/3)log n. Improving just the source/size tails leaves the old avoidance tail inadequate. I267's two changes are both necessary to close this particular uniform proof with that lower supply.

For fixed s, the permitted lower density changes from n^(-1/(100b)) to n^(-1/(3b))(log n)^(2/b). The polynomial gain is n^((1/3−1/100)/b), up to logarithms. This is not a constant improvement or a cosmetic change of a displayed tail exponent. For s=c log n with fixed c>0, however, the condition still requires log(1/r)≤1/(3dc)+o(1), so r remains bounded away from zero. The extension creates a genuinely wider polynomial sparse range when s is fixed, not a vanishing-density theorem for logarithmic neighborhoods.

Accordingly, I258's precise objection that μ_Q≥c_d n^.99 makes coarse bounded differences overwhelmingly sufficient **must be retired for I267**. The technical verdict below does not repeat that obsolete premise. What remains is the generic nature of the new mechanism and the absence of a demonstrated new structural or problem-scale consequence.

## Why the new mechanism remains technical

The crucial inequality is correctly aimed at an optimum rather than an independent collection of compatible-block indicators. Assign graph edges to independent nonroot-owned coordinate blocks X_v. For either ordinary packing or the smoothed weighted optimum, define Z_v by forbidding v as a nonroot image. Every edge owned by X_v is then irrelevant, so Z_v is independent of X_v even though other coordinates still hold edges incident to v. Fix one maximizing packing P. Removing its unique block U containing v loses at most its weight w_U≤1, while retaining every other term. Consequently

    0≤Z−Z_v≤w_U≤1,
    sum_v(Z−Z_v)≤sum_(U∈P)|U|w_U=dZ.

This is a legitimate and useful verification for the dependent rooted-block model. It does not require independent block weights or uniqueness of an optimum. But the argument uses only locality of item weights, bounded item size and disjointness of feasible items. It contains no new property of roots, overlapping patterns or the compression-selected family. The weighted case is paid by charging each deletion to the weight of the item in a single optimum. The ordinary case is its 0/1 specialization.

[BLM, Theorem 1](https://www.maths.tcd.ie/EMIS/journals/EJP-ECP/article/download/690/690-2335-1-PB.pdf) then supplies the mean-scale upper and lower tails. The statement and relevant proof were read, not merely cited. BLM also records earlier mean-scale self-bounding inequalities; the sharp constant (3d−1)/6 is not necessary for the density exponent. Thus no new concentration theorem, optimal constant or specially rooted tail phenomenon is produced.

More concretely, [Blum et al., *Opting Into Optimal Matchings*, §2.2 and Appendix A.3](https://arxiv.org/pdf/1609.04051v1) already replace the n-scale Lipschitz variance by a mean-scale self-bounding lower tail for optimal packings of bounded directed cycles. Their proof deletes vertices, loses one bounded cycle, and charges nonzero deletions to vertices of an optimum. Their random model is vertex sampling in a fixed directed graph, and their objective counts covered vertices. It is **not** I267's random-edge rooted-family transfer. Nevertheless, it is a close primary precedent for precisely the proposed concentration upgrade and its optimum-witness reasoning.

[Ezra et al., *Prophet Inequalities via the Expected Competitive Ratio*, Proposition 1 and Appendix F.2, Proposition 5](https://arxiv.org/pdf/2207.03361v4) prove self-boundedness of normalized weighted optima under general downward-closed packing constraints and extended-XOS objectives. The proof charges coordinate loss to one maximizing feasible set. Their weight coordinates differ from I267's vertex-owned graph coordinates; one cannot substitute independent hyperedge weights for I267's dependent local weights. I267 pays that distinction by the deletion construction above, which is a short general locality argument. This comparison supports TECHNICAL without asserting that the exact theorem is an existing corollary.

The second improvement exposes only the dq positions used to construct a q-matching. The same prefix-preserving transposition coupling from I248 changes at most two block-avoidance indicators. Once those dq positions are exposed the statistic is measurable, so the martingale needs dq increments, yielding exp(−c q/d). The proof's probability space, coupling, occupied-set bound and layer selection are unchanged. This removes an unnecessary n-exposure variance charge; it provides no new way to pack through depleted reservoirs or asymmetric candidate capacities.

The enlargement is therefore meaningful in scope but attributable to applying established, closely precedented concentration at its natural witness scale and eliminating unused exposures. Large exponent improvements can be substantive; the reason for this judgment is the specific generic derivation and primary antecedents, not a rule that classical concentration can never support a substantial result.

## Pinned and rooted-embedding comparison

The complete pinned 175 graph-decomposition manuscript was read, freshly retrieved and authenticated. `lem:compression` works on arbitrary support coordinates. `prop:transfer` already imposes source and target tests against common smoothed means for all small root sets and compressed families and then handles repeated demands by Hall. Arbitrary root overlap and adaptive family choice are inherited from that architecture. The d-block rank functional and layer amplification remain genuine additional formal steps of I248. The companion introduction/consequence and density-restoration sections read concern covers and unions, not disjoint rooted packing ranks. No duplicate exact rank theorem was established there.

[Ferber–Luh–Nguyen, §2.4](https://arxiv.org/pdf/1606.05923v3), read in full, already supplies compatible-block hypergraphs, independent rounds, all-subfamily matching requirements and Aharoni–Haxell. The sets W_ij and W_i'j' are disjoint for different block indices; their different-block Janson covariance calculation uses this. I267 permits arbitrary root reuse, so FLN's calculation does not directly apply. I267 does not improve FLN's sparse embedding theorem: its hypotheses, overlap contract and source-rank formulation are different. It adds no new block architecture beyond I248.

[Nenadov–Škorić, §3](https://arxiv.org/pdf/1601.04034v2), read in full, already proves simultaneous rooted matching via a copy-after-deletion property, rooted density m(F,x), and greedy rounds. It permits growing F but requires disjoint prescribed root tuples and contains no two-host rank comparison. Neither source can justify calling I267 KNOWN. They also show why simultaneous rooted matching by itself is not the new contribution and identify a substantive sparse mechanism—subgraph-density/covariance control—which I267 does not supply.

At I267's endpoint, a fixed maximally specified pattern still has expected ordered embeddings of order n^d r^b≥n^(d−1/3)(log n)^2 outside a fixed small root set. This does not prove a packing threshold or handle covariance; it illustrates why the lower bound from just n/d predetermined blocks is a coarse witness-supply bound rather than a rooted-density characterization. The statement has no test-sensitive subgraph-density hypothesis or conclusion. Its remaining freedom of nonroot images and cap keep the amplification lemma in its symmetry-and-reservoir-slack setting.

## Remaining objection and possible substantive repair

**Decisive contribution obstruction:** I267 crosses the artificial μ²/n-versus-test-entropy barrier of the submitted proof, but the bridge beyond pinned scalar transfer and classical block matching is still the same generic weighted-optimum/exchangeable-layer lift, now using standard mean-scale concentration. The revised theorem's larger polynomial range is real. No new rooted scarcity, asymmetric capacity, shared-interface obstruction or concrete application beyond that lift is established. The cap still uses only asymptotically 1/(16d) of a full d-matching; arbitrary lists remain unavailable; fixed d and edge monotonicity remain essential to this argument.

This is a contribution objection, not an identified false inequality or an outstanding access failure. I267's key proposed estimates have been examined sufficiently to assess the mechanism, but full constants, floors, deterministic-class construction and every inherited proof transition have not been certified anew. A separate independent proof review is still required for the enlarged range.

A substantive repair would need new mathematics or a demonstrated new consequence: for example, a feasible test-sensitive sparse transfer with explicit capacity/entropy hypotheses that replaces the blanket full-root union bound; candidate-set restrictions with a proved capacity condition replacing permutation invariance; or an application resolving a specified shared-interface problem that existing scalar transfer and rooted matching do not resolve. A sharp threshold is not a mandatory acceptance criterion, and these directions are not proved repairs. Merely invoking a still smaller exponent after another standard concentration substitution would need its own substantive case. No author edit or rebuttal is made here.

**Disposition: TECHNICAL; exact priority unresolved; no proof-gate verdict; same I248 chain; target twenty and accepted count ten unchanged.**

## Read record and written artifacts

Fully read: I267 proposal and all specified I267 notes/literature/BLM excerpts; I248 proposal and 167-line analytic proof; I257 52-line review and 238-line reconstruction; I258 64-line review, 35-line analysis and 55-line literature (plus authentication/read record). Primary reading: pinned graph manuscript all 841 lines; integral/fractional introduction 208 and consequences 50 lines; discrete-convexity introduction 173 and density restoration 84 lines; FLN all §2.4; NS all §3; BLM Definitions/Theorem 1 and relevant §§4–5 proof excerpts; Opting Into Optimal Matchings complete §2.2 and Appendix A.3 plus bounded context; Prophet complete cited structural and weighted-self-bounding arguments plus definitions. External papers are not claimed fully read. No original AH topological proof, original BLM modified-log-Sobolev antecedent proof, or new Yang argument was read or used.

Only this review, `frontier/experiments/i268_sparser_rooted_packing_contribution/{analysis.md,reading-and-failures.md,input-authentication.json}`, and `frontier/sources/i268_sparser_rooted_packing_contribution/literature.md` plus completely read primary excerpts were written. The manifest gives input, primary PDF/Git-blob and output SHA256s; the manifest's own hash is detached at handoff. No subagents, live I263/I265/I266 reads, shared edits, candidate edits, counts, staging, commits, publishing, research code/tests/numerical scans or snapshots occurred.
