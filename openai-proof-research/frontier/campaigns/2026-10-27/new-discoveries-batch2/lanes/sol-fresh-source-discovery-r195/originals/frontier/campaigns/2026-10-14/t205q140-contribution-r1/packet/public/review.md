# T205Q140 — independent contribution review r1

**Verdict: TECHNICAL, conditional on correctness, for the complete unchanged joint theorem.** The all-support fourth-moment estimate follows by a compatible composition of the actual Féray–Śniady and Teyssier bounds with classical cycle-index counting, retaining its cycle-number factorial. Exact class algebra, Fulman's tensor spectral transform and i-cycle CLT, and tensor/hypergroup contraction then give all the frozen conclusions. There is a useful sharp quantitative corollary here, but I do not identify a substantial new operation after those deductions. This assessment is not based on a failed factorial-free bound, an absent headline, importance, proof length, or a desired campaign grade.

Reviewer: Codex / GPT-6.1-Sol / high / default service tier, as assigned. There were **no previous independent T205Q140 contribution reviews or unresolved reviewer objections**. C1–C6 are first-round comparison questions, not inherited adverse findings. This is not mathematical acceptance, a correctness review, or a campaign-count decision. Parent alone integrates. Publication and all downstream stages remain stopped.

## Scope assessed

I assess the whole theorem at scope SHA256 `0b57f7972d43586f721a6e1aaa42cdd6fa8c80512702f933796b82e2bcd3f6ef` and proof SHA256 `fe18edab356729afe1c0cd96919bf20210ac7ba72c756a125495113d3f78e0ff`: every triangular n=m(m+1)/2, m≥2, every partition as a state, ordinary complex staircase tensor kernel in its original discrete time, and Plancherel stationary measure. At time two the density has the exact three-cycle coefficient, an orthogonal squared-L2 remainder ≤C/n² for one existential absolute C valid for every m, and the stated exact chi-square subtraction. The trivial state attains the exact TV and chi-square maxima; the sharp limits are 1/(4√(6π)) and 1/48 after multiplication by √n and n. At time one the exact maximum is 1−π_n(ρ), tending to one. No laziness, continuous-time change, diverging-time cutoff, pointwise floor, signed-square, integral, modular or general-shape appendage is used in the assessment.

## Actual primary comparison

[Fulman, convergence rates](https://dornsife.usc.edu/jason-fulman/wp-content/uploads/sites/224/2023/06/markovirrep3.pdf), final revisions 13 April 2007, Lemma 2.1 and Section 3, gives the exact spectral density/chi-square formula and the tensor-power law from the trivial representation. Its symmetric-group mixing application uses the defining representation, so its cutoff theorem is not a staircase two-step theorem. [Fulman, random character ratios](https://dornsife.usc.edu/jason-fulman/wp-content/uploads/sites/224/2023/06/steinalgrevised.pdf), submitted 2005 with referee revisions 12 May 2006, proves the tensor eigenbasis in Lemmas 3.6–3.7/Corollary 3.8 and the fixed-i, unit-variance character CLT in Theorem 3.14. I read those operative proofs, including the exchangeable-pair and two-i-cycle estimates. For i=3 its normalization is exactly √|C3| χλ(C3)/dλ.

[Benkart–Diaconis–Liebeck–Tiep](https://par.nsf.gov/servlets/purl/10221127), Theorem 1.1, Section 2.2 and Appendix I, supplies the tensor-chain/hypergroup framework and spectral calculation. Its stated ordinary theorem assumes a faithful complex character and allows a real-character reversible chain. Fulman's real-character calculation is the sufficient interface used here. Neither diagonalization statement by itself bounds the global fourth-moment tail. Their modular and quantum chains have different stationary laws or spectral issues and are not substitutes for the present kernel.

[Féray–Śniady, math/0701051v4](https://arxiv.org/abs/math/0701051v4), 21 March 2011, Theorem 1, is a uniform normalized-character estimate for every diagram and every permutation, with **transposition length** t=|σ|:

    |rλ(σ)| ≤ [A max(rows(λ)/n, columns(λ)/n, t/n)]^t.

I read its coloring/factorization estimates and Section 5.1 proof. These are paid operations. [Teyssier, 2508.06770v2](https://arxiv.org/abs/2508.06770v2), **16 September 2026**, Theorem 1.2, uniformly over each fixed C-balanced family s(λ)=λ1+λ′1−1≤C√n and every nonidentity permutation, gives for sufficiently large n

    |rλ(σ)| ≤ [B/√t]^t,

where B depends only on C. I read the operative thick-hook/skew-dimension route, restriction to support, ribbon count, Section 3.3 proof and applications in Sections 4–5. For the staircase s(ρ)=2m−1<3√n, so C=3 is fixed. The crossover with Féray–Śniady at t≈n^(2/3) is explicitly discussed in Teyssier's introduction. This external 2026 theorem is an essential literature input; it is **not** covered by the stipulation of truth for the OpenAI pin. No explicit numerical B or threshold is extracted.

The strongest older fourth-moment leads need their real hypotheses. [Rattan–Śniady, math/0610540v2](https://arxiv.org/abs/math/0610540v2), Theorem 1 and Corollary 14 with proof, gives a bounded fourth moment only for t≤a n^(4/7) for balanced diagrams. Its Problem 2 explicitly asks about tensor-product proximity to Plancherel; this is credited context, not a solved general theorem. [Moore–Russell–Śniady, quant-ph/0612089v3](https://arxiv.org/abs/quant-ph/0612089v3), Lemmas 1–2 and 6–9, proves an O(1) global fourth-moment bound for **typical** diagrams. Definition 4 requires both balance and dλ>√(n!) exp(−√n log n/2). It is not a bound for every balanced diagram. For the staircase the hook formula gives

    log(dρ/√(n!)) = −(log(2√2)−1)n + o(n),

so that typicality assumption fails eventually. Indeed the hook product is ∏_{r=0}^{m−1}(2r+1)^(m−r); its Riemann sum gives log H=n log(2m)−3n/2+o(n), which yields the displayed positive linear deficit. Furthermore, an O(1) fourth moment alone would not provide the exact C3 subtraction and O(n^−2) remainder. The actual v3 has the additional dimension condition; an earlier search excerpt omitting it is not the operative theorem.

[Śniady, math/0501112v3](https://arxiv.org/abs/math/0501112v3), Theorem 3.10 and its proof, says tensor products of sequences with character factorization have the Plancherel limit shape and fluctuations. These are fixed-observable/weak limits, not a quantitative total-variation or L2 comparison of the complete measures. [Dousse–Féray](https://www.unige.ch/~doussej/skewSYT.pdf), Theorems 1, 3–4 and Section 2 proofs, is a useful antecedent for factorial-preserving character summation and support/length windows. Its quantity is a skew-tableau/compression ratio with its own size restrictions, not this fourth-moment remainder.

For staircase-square asymptotics, [Luo–Sellke, 1511.02387v2](https://arxiv.org/abs/1511.02387v2), Theorem 1.6 and Section 4.2 proof, establishes that the *set of constituents* has Plancherel probability tending to one, using sum-flexibility, dominance and the semigroup property. That does not compare the actual dimension-weighted tensor-square law with Plancherel, or give the sharp constants. Its transitive sum-flexibility appendix was not fully read here. [Pak–Panova–Vallejo, 1304.0738v2](https://arxiv.org/abs/1304.0738v2), Lemma 1.3, Theorem 1.4 and Section 8, concerns positivity, principal-hook character tests and random-character questions, not the frozen global remainder. These distinctions do not themselves establish substantiality.

No inspected general primary theorem directly states the entire frozen theorem. That observation does not establish novelty or absence of further antecedents. The following **constructive full-scope composition**, rather than any absence claim, is the decisive reason for TECHNICAL.

## Strongest compatible reduction of the whole tail

Let k be the support size, l the number of nontrivial cycles, and t=k−l. Staircase 2-core vanishing removes every class having an even cycle. For the surviving profiles all nontrivial cycles have odd size at least three, so l≤k/3. This is the usual Murnaghan–Nakayama/beta-set operation, not merely self-conjugacy (which alone would kill odd permutations).

The exact cycle index, equivalently the exponential formula, is

    H(z)=Σ_(j odd≥3) z^j/j,
    Σ_(profiles at k,l) 1/∏_j(j^a_j a_j!) = [z^k] H(z)^l/l!.

Consequently the total size of these classes is at most 2^k n^k/l!: order the l cycles, bound the number of ordered compositions by 2^k and their reciprocal length products by one. This retains the crucial factorial, for **all** profiles without a bound on cycle lengths. The elementary Stirling estimate gives

    1/l! ≤ e^k k^(−l),

since (ek/l)^l≤e^k for l≤k. The cycle-index identity and this optimization are classical operations already available before considering the author's intermediate window.

For small support k≤√n, Féray–Śniady gives |rρ|^4≤D^k n^(−2t). Thus the full (k,l) contribution is bounded by

    D^k n^(−k+2l)/l!.

There are no nonidentity admissible profiles at k=1,2,4. Remove the unique k=3 profile exactly. The k=5 profile has l=1 and is O(n^−3). For all k≥6, −k+2l≤−k/3. Summing l (absorbing a factor at most k into D^k) and then k gives

    Σ_(6≤k≤√n) (D1 n^(−1/3))^k = O(n^−2).

Here and below constants depend only on the two fixed primary constants and the fixed staircase balance constant, never on m, k, l or a profile.

For **every** transposition length t≥1, the two actual primary estimates imply the simpler common bound

    |rρ(σ)| ≤ [D2 n^(−1/3)]^t.                 (* )

Indeed, if t≤n^(2/3), Féray–Śniady has max(√(2/n),t/n)≤√2 n^(−1/3); if t≥n^(2/3), Teyssier has t^(−1/2)≤n^(−1/3). The latter estimate is uniform for the fixed balanced family for sufficiently large n. This uses both estimates on their actual ranges, with no Moore–Russell conjecture or unsupported extension.

Now take **all** k>√n, including k of linear size and k=n. The profile factorial gives 1/l!≤e^k n^(−l/2). Applying (*) to the fourth power, the total (k,l) contribution is at most

    D3^k n^k n^(−4(k−l)/3) n^(−l/2)
      =D3^k n^(−k/3+5l/6)
      ≤D3^k n^(−k/18).

Summing at most k values of l and all k>√n therefore gives

    Σ_(k>√n) (D4 n^(−1/18))^k = O(n^−2).

For example choose n sufficiently large that D4≤n^(1/36); the remaining geometric tail starts beyond √n and is smaller than n^−2. This covers the author's intermediate and large windows together. It pays the entire all-support interface by the exact cycle-index factorial and a coarse uniform minimum of the two supplied estimates. There is no remaining bootstrap, new profile cancellation, compatibility constraint between different shapes, or new character estimate to establish. The author's sharper n^(−k/9) window bounds are a valid way to organize the same standard composition, but their extra exponent is unnecessary at the frozen strength.

Combining the two support ranges bounds Σ_(C≠1,C3)|C|rρ(C)^4 by C0/n² for sufficiently large triangular n. The remaining m≥2 form a finite set, and each finite sum exists; take the maximum of their n²-weighted values and C0. This proves the **existential all-m** constant at exactly the requested strength. No effective finite threshold, uniform explicit constant, extra finite enumeration, or asymptotic-only weakening is needed. This reduction is an analytic comparison conditional on the inputs, not an independent correctness certification of the author packet.

## Allocation of every other frozen conclusion

1. **Exact residual orthogonality and chi-square coefficient.** The class basis X_C(λ)=√|C|rλ(C) is exactly orthonormal in L2(π). Fulman's transform gives μ/π−1=Σ_(C≠1)√|C|rρ(C)²X_C. Subtracting the C3 coordinate leaves an exactly orthogonal residual. Its squared norm is precisely the nonnegative tail just bounded, not an approximate decorrelation estimate.

2. **Exact C3 cancellation.** The classical transposition class sum satisfies T2²=binom(n,2)1+3T3+2T22. The 2-core zeroes at 2 and 22 give rρ(C3)=−1/[2(n−2)], also at n=3 when T22 is empty. Squaring in the time-two transform gives a_n=√|C3|/[4(n−2)²] and a_n²=n(n−1)/[48(n−2)³]. This finite class-algebra specialization is useful but routine; no source205 positivity is needed.

3. **TV and chi-square sharp constants.** Fulman Theorem 3.14 at i=3 gives X_C3⇒Z, a standard normal. Exact second moment one makes |X_C3| uniformly integrable, hence E|X_C3|→√(2/π). Cauchy–Schwarz on the bounded residual gives |TV(μ,π)−a_n E|X_C3|/2|≤√C/(2n). Since √n a_n→1/(4√3), the TV limit is exactly 1/(4√(6π)). Orthogonality gives the chi-square limit 1/48. The coupling adds no stronger all-support demand than the estimate already paid above.

4. **Exact worst starts, every m.** For every irreducible η, tensor associativity gives δ_η Kρ^s=(δ_1 Kρ^s)Kη and πKη=π. Stochastic contraction proves the trivial state maximizes TV, for s=1 and s=2 (indeed every integer s). The spectral formula and |rη(C)|≤1 prove the same chi-square maximum. These are standard tensor/hypergroup operations on exactly the original kernel; no lazification or change of state space is involved.

5. **One-step exact value and limit.** δ_1 Kρ=δρ, so the exact maximum is 1−π(ρ). From Eπ X_C3²=1 and X_C3(ρ)²=n(n−1)/[12(n−2)], the single atom gives π(ρ)≤12(n−2)/[n(n−1)]→0. No new staircase dimension asymptotic is necessary for this conclusion. Calling this an abrupt one-to-two-step transition, without conventional cutoff, preserves the precise claim.

The joint result has more content than positivity, or a fixed-support expansion. Nevertheless, the *whole joint result* follows from the above compatible operations. The verdict does not assess only its headline constants or only the small-support fragment.

## Operative project history, credit and limits

I read the full operative R026 manuscript, full R037 manuscript, r1 candidate and r38 frozen scope, I19's complete signed target/quotient/recursion/obstruction discussion through line 240, and all I21. R026 proves the explicit integral regular summand in every cube over every commutative unital base ring, by the equality filter, refined letters, unit coefficient and splitting. R037 proves the all-label sharp floor m−1 by a cyclic multiplicity recursion, four exceptions, usable predecessors and low-capacity rigged configurations. I19/I21 preserve the physical-flip target and its explicit maps, failed ranks and growing-band limitations. Their repeated-row identification, max rule, band and source projection machinery are paid antecedents. None is a global likelihood estimate, and none is relabeled as this review's new mathematics. Their scopes remain immutable and are neither solved nor weakened by T205Q140.

I also read the pinned cyclic source's actual dominance, band quotient, matrix-path and completion proofs and classical Specht tools, plus the specified companion passages. They are stipulated true, including their proof operations; I performed no truth audit. The quantitative reduction uses no positivity premise and no hidden invocation of those support constructions. Historical separateness therefore avoids a mistaken duplication charge but supplies no automatic novelty credit.

Minimum honest positioning if this theorem is used later: describe it as a sharp staircase specialization/corollary of the two uniform character bounds and the tensor-chain/CLT framework; credit classical odd-cycle index counting with its factorial and 2-core vanishing; distinguish its exact distributional assertion from credited support, pointwise, signed and integral work. Do not advertise the intermediate window as a new nonroutine principle, a new balanced-character bound, or a new conventional cutoff theorem. A paper could still be useful as an explicit sharp application. That usefulness does not change this contribution verdict.

Read extents, exact retained versions, observation/late-binding chronology, searches and isolation updates are in [reading-limits.md](reading-limits.md). Protected bodies remain private/local under original rights. The search was bounded and cannot certify worldwide priority, current-open status, all companion duplicates or unread transitive originals. The retained primary versions, not abstracts or acquisition flags, support the comparisons above. Missing transitive reads are explicitly identified. No primary acquisition failed in this review.

**Correctness boundary:** no distinct correctness concern about T205Q140 was identified during this conditional comparison. This is not a full proof PASS: I did not conduct the separate adversarial proof gate. Artifact authentication, copied controls and bounded finite replay establish identities/reproduction only. The contribution verdict is TECHNICAL for the full unchanged theorem; no acceptance, count, formal, manuscript or release gate follows.
