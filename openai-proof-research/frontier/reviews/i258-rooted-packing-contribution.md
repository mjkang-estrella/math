# I258 independent rooted-packing contribution review

2026-10-12. **Verdict: TECHNICAL.** The unchanged I248 candidate is a useful packing-functional extension of the stipulated 175 neighborhood-transfer method, but does not clear the requested standard for a substantial discovery. The precise theorem is **not classified KNOWN**: none of the primary arguments read states or implies it without an additional argument. Worldwide priority remains unresolved. This is a contribution judgment, **not a proof-gate verdict**.

This fresh independent round replaces interrupted I255. I255 was neither read nor modified. No author rebuttal or revised candidate exists in this round. The full candidate proof was read and its SHA256 independently matched: `47a0fa44fdc57a1c2009da17f14a6dab8aa6d05fec63d49e55f013d49487886b`. All pinned results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true and were not audited. The user target remains twenty total substantial findings, ten accepted; this reviewer changes no count or shared state. Own-thread configuration confirmed GPT-6.1 Sol/high/default (Standard).

## Exact scope judged

For fixed integer d≥2, n≥N_d, integer 1≤s≤10 log n and 0<r<1, let b=ds+binom(d,2), require r^b≥n^(-1/100), and put p=1−(1−r)^(128d). The claimed deterministic classes D(n,r,s,d), E(n,r,s,d) have probability 1−ε_d(n) under G(n,r), G(n,p), with ε_d(n)→0 uniformly over allowed r,s. For every G∈D, H∈E, Y⊆[n] with |Y|≤n^(2/3), and every family R of rooted d-slot patterns,

    ν_R(H;Y) ≥ min{2d ν_R(G;Y), floor((n−|Y|)/(16d²))}.

Patterns require present internal edges and at most s root neighbors per slot. Additional edges are allowed. Nonroot blocks must be disjoint; roots may be reused without bound. Requirements can overlap and repeat arbitrarily, and R can be chosen after seeing both hosts. This is a Cartesian-product assertion, not a coupling. Nonedges, nonroot candidate lists, growing d and near-spanning packing are excluded. Uniform error does not mean one pair of classes works simultaneously for all parameter choices.

The anchored bounded-component extension has at most n/(1000d³) nonroots, components of order at most d, at most s root neighbors per nonroot, and no required root-root edges in the new host. It uses Aharoni–Haxell. It is an application of this nomination, not a second finding.

## Contribution boundary

The strongest positive case is real. Dependent, overlapping candidate blocks require disjoint packing rank rather than scalar supply. Sequentially applying the one-vertex transfer does not automatically preserve internal block edges. FLN cannot simply be quoted when different blocks reuse roots without bound. The source-relative rank interface is useful and formally stronger than a fixed-list embedding assertion. This is more than a literal substitution of d=2 for d=1 in a statement.

Nevertheless, its new work is a standard weighted-functional lift and a sprinkling argument for small packings, with substantial quantitative slack:

1. Bernoulli compression in 175 already applies on arbitrary finite coordinates. Encoding the at most b required edges of a rooted block and symmetrizing slots introduces no new compression phenomenon. Arbitrary overlap and repetitions are already admitted by the source mechanism.
2. For a fixed feasible packing, the sum of conditional compatibility probabilities is its expected successful count after smoothing, bounded by the conditional expected optimum. Maximizing and averaging is the general inequality max E≤E max. It is not a new extremal property of these rooted patterns.
3. Resampling coordinates owned by one nonroot affects only blocks containing that vertex. A disjoint packing uses at most one such block. Vertex bounded differences is the natural replacement for the source's independent-row concentration. The compressed-test count and common comparison means then provide simultaneous/adaptive tests as in 175.
4. The principal additional lemma is layer amplification. Symmetric random hosts and equivariant optimum selection give a uniform d-matching after averaging the host and conditioning on cardinality. This is not uniformity for a fixed realized graph. With the stated cap, an occupied set hits only a small fraction of blocks in the next uniform matching. A permutation concentration estimate and O(d) independent layers produce constant amplification. This generic symmetry-and-deletion step is useful, but does not supply a new sparse embedding mechanism in this range.

This assesses the nature of the bridge. It does not certify all candidate inequalities, concentration estimates, cardinality conditioning or floor arithmetic; those belong to a separate proof gate.

The stipulated source enables the attempt at the level of its compression-and-transfer method. The candidate re-proves the bounded-support compression operation and its rank argument does not invoke the graph-decomposition theorem, discrete-convexity conclusion or integral/fractional rounding theorem. It therefore does not demonstrate a new substantial consequence of those resolved conjectures merely by citing their companion family.

## Restrictions and significance

The density hypothesis makes every individual required block have probability at least n^(-.01). A predetermined partition into d-blocks already gives the candidate's reference mean μ_Q≥c_d n^.99. Relative vertex concentration then has exponent n^.98, far larger than the test entropy O_d(n^(2/3)log n+n^.01(log n)²). The difficult low-supply regime is deliberately avoided.

For fixed s, r≥n^(-1/(100b)), a very dense polynomial scale for a fixed rooted configuration. For s=c log n with fixed c>0, log(1/r)≤1/(100dc)+o(1); r is bounded away from zero. At the largest allowed s it must be close to one. The theorem is not vacuous—fixed s still permits r→0—but logarithmic root-neighborhood size here does not come with a sparse-density breakthrough.

Fixed d keeps symmetrization, layers and packing losses constant. Sublinear roots leave nearly n freely permutable vertices and cheapen the root-set union bound. Arbitrary root overlap genuinely exceeds FLN's hypotheses, but exceeds neither scalar 175 compression nor its repeated-demand treatment. Source rank ensures that demands are promised only when the source can realize them.

The rank cap is asymptotically only 1/(16d) of a full d-matching. The application occupies an even smaller fixed fraction n/(1000d³). A linear-size conclusion has value, so small support alone is not a rejection. Here, unused-vertex slack is exactly what makes the generic layer argument easy. No spanning, candidate-list, growing-component or global shared-embedding obstruction is resolved. Root-root edges need a separate host or prior embedding. No new expectation-threshold decomposition follows in the submitted application.

## Primary comparison

The complete 841-line pinned graph-decomposition manuscript was read, including `lem:compression`, `prop:transfer`, direct embeddings and assembly. The transfer proof already defines source and target tests against common smoothed means for every root choice and compressed family. Its repeated-neighborhood Hall argument already supports adaptive source demands. Deterministic target classes and cross-product reasoning are visible in that proof even though its stated conclusion is weaker. These features are inherited strengths, rather than entirely new quantifier obstacles. The relevant companion sections read contain covering and two-union operations, not the packing-rank transfer.

[Ferber–Luh–Nguyen, arXiv:1606.05923v3, §2.4](https://arxiv.org/pdf/1606.05923v3) is serious prior art: compatible-block hypergraphs, all-subfamily matching conditions and independent embedding rounds are already present. Its roots are disjoint across different blocks, and its Janson calculation separates same-block and different-block covariance. It does not establish I248's unrestricted-overlap source-rank comparison. Its substantially sparser bounded-degree setting prevents calling I248 an improvement of its embedding theorem.

[Nenadov–Škorić, arXiv:1601.04034v2, §3](https://arxiv.org/pdf/1601.04034v2) is an additional primary comparison. The Connecting Lemma is simultaneous for all allowed families of disjoint prescribed root tuples, uses rooted-density control and allows growing structures. Its proof combines a uniform copy-after-deletion property with greedy rounds. It requires disjoint roots and contains no comparison of ranks across two typical hosts. Simultaneous rooted matching alone therefore cannot establish novelty, while the exact overlap/rank distinction remains.

The [Yang primary record](https://arxiv.org/abs/2609.20864) explicitly marks the manuscript withdrawn. Actual v1 §3, §4.1, concluding remarks and Appendix A were read. These discuss common Hall-function demand/supply approximations, biased DNF complexity and repeated/overlapping neighborhood lists. They are untrusted overlap evidence for ideas and framing only. No correctness or decomposition claim is used. The read arguments contain no maximum d-block packing or exchangeable-optimum layer lemma. Withdrawal neither proves I248 known nor erases the shared-idea comparison.

Bounded searches found no exact primary rank-transfer match; they do not certify worldwide absence. No direct MathDB prominence for this result was established and no score is assigned. The accompanying literature record specifies read extents and limits; authentication records every retained excerpt's hashes.

## Objections, repairs and disposition

**Decisive objection:** beyond 175 and classical rooted-block matching, the contribution is a generic weighted-optimum/symmetry lift operating where coarse concentration and substantial unused-vertex slack suffice. It is a potentially reusable technical lemma, rather than an independently demonstrated nonroutine substantive advance under the stated project bar.

**Presentation repair available now:** retain one technical nomination, credit 175's overlap/adaptivity mechanism and FLN's block architecture, and identify the layer lemma as the additional ingredient. Do not use publication absence, an unestablished MathDB score, or the application as a second nomination. This reviewer made no candidate edits.

**Substantive repairs would require new mathematics:** a rank theorem at low supply or rooted-density scales; candidate restrictions with an explicit capacity condition replacing exchangeability; or an application resolving a specified shared-interface obstruction beyond existing methods. An abstract amplification theorem with demonstrated consequences outside the present slack setting could also change the assessment. These are directions, not proved repairs. Minor constant changes, another fixed d or a marginally larger support cap would not answer the objection.

Final boundary: **TECHNICAL; exact literature priority unresolved; no proof PASS/FAIL.** No unfinished access check is being used to avoid the contribution decision. No acceptance, count increment, author rebuttal or repair is claimed. Only the assigned new I258 files and fully read primary excerpts were written.

Supporting paths: `frontier/experiments/i258_rooted_packing_contribution/{analysis.md,reading-and-failures.md,input-authentication.json}` and `frontier/sources/i258_rooted_packing_contribution/literature.md`.
