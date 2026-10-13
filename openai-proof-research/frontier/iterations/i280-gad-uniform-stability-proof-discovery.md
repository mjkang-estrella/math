# I280 — uniform GAD stability: constructive proof discovery

**Full (U) unresolved; proved uniform partials. No substantial finding is nominated and no acceptance is claimed.** Eleven accepted findings toward twenty remain unchanged. All OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. The exact all-n, pure-input target, with absolute entropy excess in nats and unhalved trace norm, remains

    dist_1(P_ψ,M_n)^2≤K(γ,ν)[S(A_(γ,ν)^⊗n(P_ψ))−n s0],

for one finite K at each fixed interior parameter pair, every n, and every pure ψ.

The [complete analysis](../experiments/i280_gad_uniform_stability_proof_discovery/analysis.md) independently checks I279's cat construction, including its output cross-block norm √(1−4γν(1−ν)), the dimension factors in entropy continuity, and its entropy excess tending to log 2. It refutes the summed-marginal sufficient condition (LP), while leaving (U) intact.

Retaining conditional populations before the pinned branch proof's Jensen step gives a useful uniform mechanism. For q the full computational-basis probability law and r_n=Bernoulli(ν)^⊗n,

    D_n(ψ)≥2γ(1−γ)ν(1−ν) KL(q||r_n).

An affinity argument proves uniform entry into the manifold of states with amplitudes √r_n and arbitrary phases. In particular, **(U) holds for every pure input whose phases separate by site, with arbitrary correlated amplitudes**, with K=2/[γ(1−γ)ν(1−ν)]. This includes entangled states and the I279 even-parity cat. Its single parity constraint incurs a bounded relative-entropy cost.

A dimension-independent trace-norm concavity remainder strengthens the conditional tree bound. It avoids the Hilbert–Schmidt spectator-purity loss but still measures noisy branches. Applying it at the last two-site stage proves a second complete nonlinear partial: for every subset T, every real α, every n, and any latitude product Φ,

    ψ=exp(iα Z_T)Φ

satisfies (U) with K=1/[4γ²(1−γ)ν²(1−ν)²]. The support of T can grow without bound. This is a special entangled input family, not a parameter subregime or a proof of arbitrary-phase stability.

The exact remaining step is a robust uniform phase inequality. If ψ=Σ_x√q(x)e^(if(x))|x⟩, put

    G_q(f)=1−max_θ |Σ_x q(x)e^(i(f(x)−θ·x))|².

Proving G_q(f)≤C(γ,ν)D_n(ψ) for all n,q,f would finish (U); conversely (U) implies this phase inequality up to the already proved amplitude constant. The analysis also states a stronger sufficient inequality using the weighted trace-norm branch tree. Neither is proved. Flat-amplitude phases alone do not settle the robustness for arbitrary q through dimension-dependent entropy continuity.

The [reading/failure log](../experiments/i280_gad_uniform_stability_proof_discovery/reading-and-failures.md), [authentication](../experiments/i280_gad_uniform_stability_proof_discovery/input-authentication.json), and [primary-literature note](../sources/i280_gad_uniform_stability_proof_discovery/literature.md) specify exact read extents, pinned raw/blob checks, retained limited excerpts, and failed routes. A depolarizing stability paper was inspected at proof level but provides no GAD transfer or paid uniform nonlinear/global argument for this target. Search absence is not novelty.

Work used no subagents, live sibling reads, shared edits, staging, commits, publishing, numerical scans, or history replay. Only assigned I280 documents and fully read limited primary excerpts were written. Source and count files were preserved. Detached hashes are returned with the handoff; the authentication JSON excludes its own hash.
