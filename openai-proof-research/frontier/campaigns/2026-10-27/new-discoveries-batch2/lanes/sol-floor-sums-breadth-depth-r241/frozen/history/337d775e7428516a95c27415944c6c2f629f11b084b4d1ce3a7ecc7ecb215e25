# Bounded formal investment: partial, not a source endpoint

**Source endpoint NOT PROVED.** This packet is a deterministic finite component plus checked integer leaves. It proves neither an unconditional stochastic marginal derivative nor the refutation of arXiv Conjecture 3.2 or 3.1 in Lean. No acceptance or discovery credit. Administrative snapshots remain 9 additional / 39 total / next 40; root alone adjudicates. No manuscript, shared, git, public, browser or MathDB edits; solo, no children.

## Checked mathematics

`FiniteCore.lean` defines configurations `Fin 10 → Bool`, the exact 19-edge graph via neighbor lists, and strict neighbor-majority updates retaining the old spin on ties. Kernel-checked finite propositions establish no self-loops, symmetric adjacency and no repeated neighbors. Neighbor lists are:

```
0:3,5,8       1:2,3,6,9    2:1,3,5,6       3:0,1,2,4,5,8
4:3,6,8       5:0,2,3,7,8,9  6:1,2,4      7:5,9
8:0,3,4,5     9:1,5,7
```

`T h s = ∑ i, h (update s i)` counts all ten rings, including ineffective updates. `Q h s = T h s - 10*h s`; `generator` identifies this with the sum of all update increments. `bit` observes vertex 1. `drift_local` and `drift_abs` prove `g=Q bit` is precisely the single observed-vertex increment and `|g|≤1`.

The initial unnormalized real weight is the product of 2 for true and 3 for false over the ten vertices. `total_weight` proves its sum is `5^10`, by product-of-sums, without enumerating a huge flat term. `iterate_drift_bound` and `coefficient_bound` prove unconditionally for every natural k that

```
|T^k g(s)| ≤ 10^k,
|∑ s, weight(s) * T^k g(s)| ≤ 5^10 * 10^k.
```

`Word k` is a recursively indexed product of exactly k vertices; `word_count` proves cardinality `10^k`. `evalWord` applies its chronological marks, and `iterate_all_words` proves `T^k h(s)` is the sum of `h` over every such word. This is a deterministic combinatorial identity, not a probability-law theorem. A separate list-word composition lemma is also checked.

`IntegerLeaf.lean` transcribes the actual five integers A,B,C,D,W from the frozen candidate certificate and checks, by kernel-checked `norm_num`, both strict inequalities

```
1000000*(D*A-W*C) > 18*W*(D*B+C),
1000000*(D*A+W*C) < 19*W*D*B,
```

and `0<D*A-W*C`. These definitions are explicit integers. **There is no proved identification of A with the weighted sum of the 241 coefficients.** Their arithmetic PASS cannot be promoted to a derivative interval PASS.

## Exact remaining interfaces

1. Construct a probability space carrying independent iid Bernoulli(2/5) initial spins and ten independent rate-one Poisson clocks, independent of the spins; define the actual chronological update trajectory with no simultaneous rings and finite counts almost surely. Prove the initial configuration law equals `weight/5^10`. Product-weight normalization alone is insufficient.
2. For each ordered k-mark word, prove its unconditional probability up to t is `exp(-10*t)*t^k/k!`, by actual exponential event densities and simplex integration or a proved equivalent clock-law construction. The library's Poisson distribution, convolution and independent-increment definitions do not themselves prove this marked chronological process law. No such theorem is assumed in this packet, and no defined series is named a source probability.
3. Identify the source marginal with `exp(-10*t)/5^10 * ∑' k, t^k/k! * ∑ s, weight(s)*T^k bit(s)`. Prove local uniform convergence and termwise differentiation with derivative given by the same series replacing bit by g. The finite bound supplies domination but is not the analytic proof.
4. Kernel-check the exact coefficients k=0..240 against the literal update/weight definitions, using a sound finite checker or verified forward mass recurrence. Then prove the coefficient sum is the explicit A, the exponential partial sum is B, `C=121*80^241`, `D=19521=241*81`, and `W=5^10`. Prove the k≥241 exponential remainder bound from successive ratio ≤80/242. Prove the resulting positive divisions give `18/10^6 < m'(8) < 19/10^6`. None of these links follows from the leaf inequalities alone.
5. Deduce failure of antitonicity on nonnegative time from the positive derivative at 8. This logical wrapper has not been implemented here.
6. For Conjecture 3.1, additionally construct the iid-uniform median process, prove thresholding commutes with each odd median pool, prove the even-degree self-pool/tie-retain identity, extend to the actual clock trajectory, and prove no fixed-threshold atom. Every median stays among the ten initial uniforms, so nullity of an initial equality at 2/5 should resolve `[0,p]` versus `[0,p)` simultaneously. This reasoning is not yet kernel-certified.

These are residual obligations, not hypotheses silently supplied to a final endpoint. No final source endpoint exists. The parameters remain p=2/5, observed vertex 1, t=8; no changed rate, conditioned schedule, optimizer or numerical oracle.

## Source, chronology and holds

Actual frozen primary body: Amir–Baldasso–Beilin, arXiv:1911.08613v2, Section 2 PDF pp7–9 and Conjectures 3.1/3.2 p10. Section 2 and Proposition 2.2 were read here, as were the exact marginal/conjecture statements. Independent rate-one clocks, iid initial values, and self-inclusion for even degree are literal. Conjecture 3.1 uses `[0,alpha)`; Proposition 2.2 uses `[0,p]`. No transitivity premise is imposed on the conjectures. The distinct 3.7/3.8 assertions are outside scope.

Frozen reviews record arXiv v1 2019-11-19 and v2 2023-01-02 16:49:15 UTC (PDF cover January 3), and journal metadata SPA155 (January2023),437–458, DOI10.1016/j.spa.2022.10.015. Journal accepted/published-body equivalence remains HOLD. Current-prior, complete citing-body and public-registry coverage remain HOLD. Earlier review retrieval chronology is inherited evidence, not a new live check in this lane. No network retrieval was attempted; all denied GitHub API/raw/codeload/diff/patch, ScienceDirect and Google challenge routes and inaccessible historical intervals remain parked. No worldwide priority claim.

Selected candidate, mathematical review, source/prior review and root replay receipt are frozen in `freeze.json`; only selected immediate files and the actual primary v2 PDF/text were copied. Existing immutable reviews are reused; their nested historical source trees were not recursively duplicated. Root's frozen receipt records all 241 independently reconstructed coefficients and exact bounds passing its Python replay. That is evidence for further work, not a Lean source-law certificate.

## Replay, audit and resources

`source-only.tar.gz` is deterministic USTAR/gzip with sorted names, zero timestamps/owners and no compiled artifacts. Extract inside this assigned lane and run `bash run.sh`. The runner uses the pinned Lean hash, all nine package revisions, `-j1 -M2700 -DwarningAsError=true -DautoImplicit=false`. Root local oleans were deleted before packaging; the successful fresh source extraction starts without oleans. `fresh-replay-02/replay-receipt.json` reports the full component audit; source endpoint remains NOT_PROVED.

`Audit.log` prints full actual types, module origins, safety and transitive axiom reports for all declarations originating in the two mathematical modules, including private/generated declarations. Inherited library code is distinguished and is not counted as new. Only propext, Classical.choice and Quot.sound occur in audited dependencies. Four compiler-generated `_unsafe_rec` declarations have safety `partial` but `isUnsafe=false`; these are reported explicitly, not hidden by source-text scans. No user-written partial or unsafe definition is present. No new axiom, sorry/admit, native_decide or optimizer is used.

All helper/generation/hash/packaging/verification processes use the specified immutable helper_guard with AS/groupRSS512MiB, CPU210, wall230 and single-thread environment. Lean uses its separate fixed serial guard with groupRSS2800MiB, CPU210, wall230; no cap increases. RSS is sampled every40ms, so unsampled transients are not ruled out. An initial broad import exceeded RSS and was killed; narrower imports then passed. Failed compilation and extracted-parser logs remain preserved. See `FAILURES.md`.

Final `manifest.json` excludes itself and `verification-receipt.json`. A separate guarded verifier runs after final writes, checks all original/copy scientific hashes, all nine pins and compiler hash, source archive contents, successful replay audit and final manifest. Administrative AGENTS/ledger/prior-context snapshots are not bound to their changing live originals. No live administrative NEXT binding is used.
