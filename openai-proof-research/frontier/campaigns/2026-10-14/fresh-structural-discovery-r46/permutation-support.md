# Family238: an observation threshold obstruction and an unpaid upper interface

This is a pre-freeze screen. No sharp-threshold theorem is frozen or nominated. The source already proves two independent convolutions mix from averaged observations of7n/8 labels plus small sign mean, and gives a general disjoint-block Fourier theorem. I132 already treated dependence/retained observations and excluded arbitrary dependent products. The present calculation keeps independence.

## A fully proved elementary obstruction

Fix an integer r≥2 and a real α with 0≤α<1/r. For n≥2 there exist probabilities μ_n on S_n with exactly zero sign mean, such that for every subset S⊆[n] of size k_n=⌊αn⌋ the law of π|_S under π∼μ_n has total variation at most n^(−2) from the uniform injection law, while

    ||μ_n^{*r}−U_{S_n}||_TV → 1.

The construction is existential finite sampling, not an efficient sampler claim. Let K=(n)_k=n!/(n−k)! and B=binom(n,k), and put M=ceil(n^4 B² K). Sample M independent uniform permutations; let ν be their empirical law. For any fixed S its K possible injection outcomes have empirical probabilities p_j, with E p_j=1/K and Var p_j≤1/(MK). Hence Cauchy–Schwarz gives

    E ||ν_S−U||_TV ≤ ½√(K/M).

Summing over all B subsets gives expectation at most1/(2n²). Therefore there is a sample with Σ_S ||ν_S−U||_TV≤1/n². Fix such a sample. Let t be a fixed transposition of the positions, and set μ=(ν+tν)/2, where tν is the pushforward by π↦t∘π. Signs cancel exactly. Left multiplication by t permutes the injection outcomes for every fixed S, so convexity of total variation gives the same bound for μ, simultaneously for all S.

Its support has size at most2M. The product of r independent samples lies in a set of at most(2M)^r permutations. Thus

    ||μ^{*r}−U||_TV ≥ 1−(2M)^r/n!.

For k=⌊αn⌋, logK=αn logn+O_α(n), logB=O(n), and logM=αn logn+O_α(n). Stirling therefore gives

    log((2M)^r/n!)=(rα−1)n logn+O_{α,r}(n)→−∞.

This includes α=0 directly. The arbitrary finite small-n choices do not matter. The lower bound is on full total variation; no false L2-to-TV converse is used. It applies to independent identically distributed factors and exactly balanced parity.

The operation is generic empirical approximation of a finite family of marginals plus support counting. It is technical, not a substantial nominee. In particular, it does NOT refute any conclusion when α≥1/r, nor the stipulated source result.

## Source-paid upper estimates and the precise gap

In source introduction/core, if b disjoint complementary block subgroups have a common nonnegative retained measure f of mass1−o(1) with bounded coset caps, then

    ||f̂(ρ)||_HS² ≤ b B C_u D_ρ^(−1+(u+2)/b).

Squaring for two factors and multiplying by the Plancherel dimension gives exponent −1+2(u+2)/b. Choosing u>0 small only requires b>4. The two-sided section explicitly already states b>4 completion and retains joint-type counts K_λ² D_λ^(−1+4/b). Consequently7/8→4/5 and comparable parameter substitutions are source-paid, not discoveries.

For b=2, the same exponent is nonnegative. Using overlapping random omitted sets is not itself a new operation: the domains section already averages their small-type projections, whose scalar lower bound is c≥1−1/(qξ), and recovers vectors after removing bad omitted sets. This retains the same small-type dimension loss. It does not close a half-observation threshold by assertion.

A possible full question would be: for every fixed α>1/2, does averaged αn-label total-variation convergence plus vanishing sign mean force μ_n^{*2}→U? The calculation above explains why1/2 is a natural necessary boundary. No proof, counterexample, or credible completed new upper mechanism was found here. It is NOT frozen merely because it has a clean sharp-looking formulation. An attempted proof would need a new positive-measure/Fourier estimate beyond the source's small-type HS-square bound; optimizing its constants or renaming its overlapping-set projection does not pay that debt.

## Closest primary comparison and limits

Keevash–Lifshitz, arXiv2307.15030v1, §§1.1–1.3, was read (local extraction lines1–385). It defines globalness by L2 control under every coordinate restriction, and gives sharp spectral/mixing statements under substantially stronger density/norm hypotheses. For example Theorem1.11 assumes an r-biglobal density with L2 norm at most exp(c r^(−2) n^(1−1/M)) to get M-fold L2 mixing. Our marginal hypothesis gives neither that all-restriction L2 condition nor that density bound. Sparse empirical laws above live on a scale exp(αn logn+O(n)), far below a constant fraction of n!; there is no automatic application of that theorem. The operative proofs later in that primary paper have NOT been read, and no global novelty claim is made.

The five other source238 manuscripts were identified via the authoritative catalogue and reconciled with the actual I132 discussion (lines65–75). Their bodies have not been read in this lane; no claim that all companion operations have been exhausted is made. The transfer manuscript's introduction/core are fully read; two-sided lines1–100 and205–end, domains115–200, and characters1–180 were read. Other retrieved sections remain unread or keyword-only. A prior combined output of domains1–200 was truncated and is not counted as full reading.

Disposition: no nominee; the support obstruction is established technical evidence, and the ambitious upper threshold remains a pre-freeze question rather than an asserted result.
