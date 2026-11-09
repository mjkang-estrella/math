# r143 — fresh geometric source, no full resolution

Decision: zero nominees, zero credit. No PROOF.md, Lean or manuscript. The largest sharp interval in the selected source is not determined here. This is neither a refutation of its proved theorems nor a claim of independent novelty for the diagnostics.

## Literal source and complete target

Javier Martín Goñi, *Improved Brunn–Minkowski inequality for θ-convolution bodies*, arXiv:2610.37066v1, submitted 27 October 2026 11:33:02 UTC. The actual retrieved PDF is dated October 28. The live abstract/history has v1 only. Read primary pp1–15, especially definitions (1.2)–(1.4), the question on p2, Theorems1.1/1.2, Lemma3.1 and its full proof, the supporting-line proof, Remark3.1 and §4.2. Do not replace its question with proving the already-established interval.

For every integer n≥2 and arbitrary full-dimensional compact convex K,L⊂Rⁿ, set M=max_z |K∩(z−L)| and K+_θ L={z∈K+L: |K∩(z−L)|≥θM}. The source defines

    φ_n(θ)=inf_{K,L} |K+_θ L|^(1/n)/(|K|^(1/n)+|L|^(1/n)), 0≤θ≤1.

With c_n=binom(2n,n)^(1/n)/2 and β_n the unique root of

    I_n(β)=n∫₀¹ t^(n−1)(1−βt)^n dt=2^(−n),

the source proves φ_n(sⁿ)≥min{1−β_ns,c_n(1−s)} and equality φ_n(sⁿ)=c_n(1−s) for s≥s*=(c_n−1)/(c_n−β_n). Equality for s<1 characterizes opposite translates of the same simplex. The question is the **largest interval ending at 1** on which that simplex value is optimal. Equivalently determine the infimum a_n of all a such that the simplex formula holds for every s∈[a,1], including whether equality holds at a_n. This must cover every n≥2 and every legal pair, not merely balls, boxes, opposite bodies or dimension two. No named conjectural value is invented: the source explicitly says its bounds do not determine the interval.

The source itself proves simplex failure for 0<s≤(c_n²−1)/(c_n²+1), so global all-θ simplex optimality is already excluded, not fresh. Neither that exclusion nor source Theorem1.1 is nominated.

## Early duplicate, classical and public screens

Before primary download, complete retained original report bodies were searched for the exact ID/title/authors and convolution-body aliases (initial and expanded history JSON). No selected-source match. The final refreshed screen uses the qualified r140 hash/path aliases, themselves based on r137/r133, reopens complete matching originals, records changed/new bodies and omits generated copies by directory role. It includes original r111–r113 science rather than excluding those rounds. The final receipt covers 1,021 distinct bodies/1,447 paths with no hit for the selected source/author/companion/claim aliases. This is lexical, not semantic, clearance; newly nested reports outside retained paths are not guaranteed. Every matched original from the rejected leads was reopened in full and byte-copied with hashes in reopened/; no hit cutoff was applied.

Gaussian Radon log-concavity was caught as r47/r116/r129, and Krasniqi2609.28707 as r5/r97/r123/public-proof duplication. They were stopped before any primary download or mathematical investment here. No old family is reopened. Full original source/disposition files, not search snippets, underpin these two exclusions.

Closest primary companion: Alonso-Gutiérrez–Martín Goñi, arXiv:2211.17069v1 (30 November 2022), actual journal *J. Geom. Anal.*34,58 (published29December2023), DOI10.1007/s12220-023-01508-2. Both PDF and actual full journal HTML retained. Theorem1.1 and its proof establish the old (3/4)^n interval, and the published remark explicitly lacks a conjecture below it. Theorem1.2 is a Ball-body inclusion, not the new full optimal-interval answer. Read journal introduction/Theorems1.1/1.2 and actual proof bodies, as well as the later source's stronger proof. Chronology: the 2026 paper is an author follow-up improving the 2023 theorem. Exact-title/source-ID and author/follow-up public searches found no later answer; this is bounded search, not exhaustive author-page/citation coverage.

Current registry observation is intentionally fixed, not chased: Omega a19a578cd06b57a4ea4d287cb0df92f9085117ae and OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a, inherited from r140. Reuse of r140 aa026→a19a is restricted: six commits, CAPPED 300-path comparison; direct-tree comparison closes only Blueprint/Library/Problems Markdown and README, with three unrelated sphere bodies. It does **not** close formal, Meta, docs, other paths or historical semantic coverage. This lane additionally retrieves untruncated fixed Library, Problems and docs path trees, then actually reads the nearest lexical convolution bodies: Sen–Balakrishnan is sums of geometric waiting times; Metya–Mukherjee is finite probability-vector L1 convolution. Their actual quantified objects differ from convex-body overlap levels. No matching optimal-interval theorem found in these bodies. Unrelated Martin-name hits are catalogued, not silently treated as relevant proofs. The OpenAI catalogue's logarithmic Brunn–Minkowski family concerns origin-symmetric Minkowski combinations, a different functional, and no full subsumption bridge was located or asserted. **Registry semantic novelty remains HOLD**, not PASS. No badge/HEAD-only exclusion or acceptance is used.

## Sustained route 1: endpoint versus genuine geometry

Lemma3.1 gives H(s)=|K+_(sⁿ)L|^(1/n)/S, S=|K|^(1/n)+|L|^(1/n), continuous, decreasing, concave, H(0)≥1 and

    n∫₀¹ t^(n−1)H(t)^n dt=|K||L|/(M S^n)≥2^(−n).

Equality in the mass inequality forces opposite translates. For such pairs H(1)=0. The source's first extremal affine profile 1−β_nt has positive endpoint. It is tempting to add H(1)=0, exclude this profile and conclude a stronger sharp interval. This fails at the scalar-relaxation stage.

Take b<β_n, let g=I_n(b)−2^(−n)>0 and δ=g/(2n). Keep H_b(t)=1−bt through 1−δ; thereafter use the line from (1−δ,1−b(1−δ)) to (1,0). Both pieces decrease, the second slope is no larger than −b, and H_b is concave with H_b(0)=1,H_b(1)=0. The loss of weighted mass relative to the affine profile is at most nδ because 0≤H_b≤1 and the changed interval has length δ. Hence its mass remains at least 2^(−n)+g/2. As b↑β_n, δ↓0, and for every fixed t<1 the values approach 1−β_nt. Thus adding the zero endpoint alone does not uniformly improve the lower first branch. These profiles are not claimed to be realizable as covariogram volume profiles.

research.py independently integrates both affine pieces exactly with Fractions at five bisection stages for every n=2,…,9 (40 controls). It checks mass, endpoints through construction and slope order; the formula used is a finite binomial polynomial integration. This finite evidence is not a proof of any all-body bound; the preceding analytic argument explains the obstruction.

Potential next bridge: near equality in the overlap mass forces |K|≈|L|≈M, so after maximizing translation the bodies have small symmetric difference. An affine normalization and a quantitative compactness/stability theorem might couple this to the profile and eliminate the scalar approximants. But no quantitative estimate sufficient to determine a_n, or complete reduction of arbitrary pairs to opposite ones, is proved. A compactness argument giving merely some strict improvement would still be a partial/routine result under the task's rules.

## Sustained route 2: geometric variations and competitors

For the unit cube K=−L up to translation, overlap is ∏(1−|z_i|)_+. Direct product integration gives the familiar competitor

    H_cube(θ)^n=1−θ Σ_(j=0)^(n−1) (−log θ)^j/j!.

This is an elementary classical family, not a new source resolution. For n=2, compare it with (3/2)(1−√θ)^2. Exact rational atanh-series enclosures for log2 certify square improvement at s=1/4 and no improvement at s=1/2. This only constrains a threshold from one side. It supplies no universal lower bound between these points and no reason that boxes minimize there.

A less symmetric route truncates a vertex of Δ={(x,y)≥0:x+y≤1}: K_ε=Δ∩{x+y≥ε}, with |K_ε|=(1−ε²)/2, L=−K_ε. The original covariogram on z=r u, u∈∂(Δ−Δ), is (1−r)^2/2. Away from sector boundaries, truncation removes ε²/2 in the two sectors z∈±Δ and zero in the other four. An independent exact rational half-plane clipping implementation tests 180 interior ray values (two ε, three r, six sectors, five ray positions) and agrees with that local pattern. It also checks the actual polygon area and original simplex covariogram, rather than assuming the pattern in the clipping algorithm.

Heuristic shape-derivative calculation: if the transition strips contribute o(ε²) uniformly for a fixed interior level s, their omission yields

    d/dA [ |K_ε+_(s²)(−K_ε)|/(4|K_ε|) ] at A=ε²/2=0
       =3(1−s)(1−1/(3s)).

The putative sign changes at s=1/3, already too low to prove optimality in the unresolved interval. This formula is **not certified**: controlling the transition strips and differentiating the exact level-set volume remain necessary. Exact isolated clipping values do not justify this limiting step. Even a complete local derivative would only test local simplex stability in n=2; global competitors and all dimensions remain.

## Strongest objection, falsifiers and precise missing bridge

Strongest objection: all closed calculations are classical competitors or scalar method obstructions. The source already proves its abstract scalar theorem optimal; modifying its proof cannot establish more without new geometric constraints. A partial endpoint or local perturbation theorem cannot be rebadged as the full source answer.

A falsifier of any proposed interval [a,1] is a concrete dimension n, legal convex K,L and level s∈[a,1) for which the literal normalized overlap-superlevel volume is strictly less than c_n(1−s). Failure of a supporting-line relaxation or one sampled ray is not such a falsifier. A falsifier of the tentative derivative is a non-negligible transition-strip term at order ε² or an exact covariogram-sector identity failing away from the claimed transition range.

Missing bridge: determine a_n with a universal inequality for **all** convex K,L throughout [a_n,1], and matching geometric competitors arbitrarily below a_n, including endpoint attainment, for every n≥2. Neither direction is supplied outside the source's established bounds. No independent clearance, full proof, public-prior-art clearance, formalization or paper is requested.

## Reproducibility and access limits

All downloaded primary bytes, real UTC timestamps, HTTP status/final URLs/byte counts/SHA256 are in http.jsonl and provenance.json. Direct public HTTP only; no browser tabs, auth mutations, access bypass, uploads, git or children. All HTTP requests succeeded; journal redirected through its cookie-error query but delivered the actual full article body, including proofs. PDF extraction emitted a harmless font-type mismatch warning for the new source, recorded in progress.md; extracted text is not a visual PDF audit. Web search outputs are not primary-body evidence and search coverage is not exhaustive.

All scripts run through the unchanged helper_guard.py with fixed 512MiB address-space and sampled process-group RSS, CPU210s, wall230s, nominal40ms. Sampling does not rule out unsampled transients. Shell wrappers set OPENBLAS_NUM_THREADS=1, OMP_NUM_THREADS=1 and PYTHONDONTWRITEBYTECODE=1. Mutable context snapshots are bound separately from scientific-freeze.json. finalmanifest.json binds delivered payloads; its external verification receipt necessarily excludes itself and the manifest. No shared counts or files were changed.
