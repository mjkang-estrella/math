# O234 independent contribution/eligibility review, round 2

Reviewer: independent CONTRIBUTION/ELIGIBILITY recovery reviewer (Claude Opus 5.5), 2026-10-17. Original prose by the reviewer for Myeongjin Kang (no affiliation): CC BY 4.0; original code MIT. Third-party source and primary bodies were read only from the author's private inputs and are not reproduced here beyond short operation-level paraphrase and line references.

This is a fresh review. Round 1 (Grok) ended with API 402 and produced no findings. `o234-parent/contribution-r1-failure.json` is preserved untouched, and no verdict is inherited or reversed. The proof gate is separate. I deliberately did NOT read `o234-proof-r1/` or its provisional PASS, so this assessment stays independent of it. The parent alone integrates and decides.

## Verdict

**TECHNICAL** (conditional on the full proof; not DUPLICATE, not INELIGIBLE, not BLOCKED).

Assume the proof is complete. Theorem O234 at its full frozen scope is then a correct, natural and, as far as my bounded reading shows, not previously stated extension of source 234 to bounded spectra with outliers at every temperature. Its proof, however, is a short assembly of operations that are already paid:

- source 234's own general-spectra and magnetic machinery;
- classical Schur–Ostrowski ordering;
- Gromov/Fan–Wu exponential Haar concentration;
- the standard ε-net/union-bound template that Husson–Ko use twice in the sublinear-rank setting.

The one step monotonicity cannot pay is the scalar-block rank-thickening comparison (Lemma 2). It is that template with an equal-mean symmetry the source already uses. Its quantitative content is exactly the "finite-union bookkeeping / routine robust transfer" that the campaign briefs list as insufficient. No new interface of the kind credited in R029/R030/R031/R032 is introduced.

## Exact identities

| Object | SHA256 |
|---|---|
| author output-manifest.json | 85f5d443db8ef59498f183cb91018ff067600d6ef2dd6aa9d2dcec0732f8bb3b |
| author candidate.md | 2f550b13bee014b9b40657b15c06a4fb112b4b732327ee4bd101662d47adbc87 |
| author original-scope.md | cfb52e908976e2968bda9404e615cca27ad9c9b7ea5b19b78fb2885b8d22810b |
| source 234 invariant-sk.tex | c5d4dc62abc23768531a259d284a1ced44bf717ca85900ac6a9bd492718bef3e |
| source 234 30-rotation.tex | ba2f433d02b8df4355dc1b136db756dd2c3cc07aea7c303fa818c8afa8960f29 |
| source 234 60-general.tex | bfe25afe1fd4b27b8a34d2f5ddbc6f54b8bb8d794a14d16fbe3c2506a84957b6 |
| source 234 70-magnetic.tex | 0ad5a63394d275a01d3b7edb7d99108a2ec43d1dc68cae15f034e3da8c7ac640 |
| hk2208.03642v2.txt | b9235ff99621cbb810a55d0dfc54420d0b69645e7c513d0d51c5a239038ae782 |
| fw2105.02797v3.txt | 932c397117ce02cc01e2334a0b5f98d7b8890f5f9f97f811102b7248a26ac4e6 |
| gm0406121v3.txt | ed475fbdda867b51f09d61cd5707c0cf6705e1f0b3fcef1bd374249cb4a5e872 |
| bs1507.05067v2.txt | 4ffcb4b31c7fc47847fa95c873e65063647f4751a5ee40be526cbb3cd7388618 |
| fmww2607.10102v2.txt | 896ab147861b2e7a0d50739a7f248265fdfd44d05515311bc8dca5268cdfe225 |
| history i149 snapshot | b9ce62843b360b0dbe7e762baa663836c1143ad22f269ba7444f62ec9ffc61f2 |
| history i151 snapshot | 1cd1e881c06abdfe63e1462b1a147a32610c1fad45a7e85a037e0728d988c757 |
| history family-operation-notes | a736980aa14c4251ec24fb01baec51efc0544c9a77fd30ab62dbc54e8cdfb137 |

Author verifier, run read-only with `python3 -I`:

- With the external anchor: exit 0, `IDENTITY_ONLY`, 62 payloads, 5 directories, 23 pinned blobs, 6 primary PDFs.
- Wrong-anchor control (64 zeros): exit 1, `VERIFY_REJECTED: external anchor mismatch`.

Captured byte-for-byte in `checks/`. The author packet is identity-only. `git status` shows no author-file modification by this review.

## Frozen scope reviewed (unchanged, no narrowing)

The scope is the full frozen target in `original-scope.md`:

- **Spectra:** deterministic, uniformly bounded, real diagonal, with empirical limit μ and top eigenvalue limit θ ≥ max supp μ.
- **Outliers:** arbitrary bounded lower outliers with no minimum convergence, and any finite or sublinear number of upper outliers.
- **Haar coupling:** Haar O(N) with any cross-N coupling.
- **Conclusion:** at all β ≥ 0, in expectation and almost surely, locally uniformly, the limit is F(β_*μ, βθ), i.e. the source functional with the inverse-Stieltjes branch capped at βθ.
- **Included cases:** atomic and point-mass μ, θ = b, and β = 0.

I assess only this full theorem. No high-temperature, fixed-rank, positive-density, overlap or field substitute is assessed or offered.

## Operation-level decomposition and antecedents

Each operation below is listed with the actual body that already pays it. "Read" means read in the bound private extraction at the stated lines.

1. **Upper bound for every outlier configuration** (candidate §6, (20), (27)).
   - The operations: raise the top k_N = ⌊εN⌋ eigenvalues to θ, clip the rest at b plus a vanishing scalar shift, then apply the source theorem at fixed ε>0 to the law ν_ε = (Q_μ)_*Leb|(0,1−ε) + εδ_θ.
   - Antecedents: monotonicity and `gen:scalar-shift` (60-general.tex:113–125); the zero-mass bin squeeze `gen:bin-squeeze` with "thermodynamic limit for each fixed alphabet before refinement" (60-general.tex:173–281); the stipulated `thm:main` (invariant-sk.tex:186–205).
   - The quantile-trimmed law and its weak convergence are standard one-dimensional facts. *Paid; routine.*

2. **Capped-transform continuity with an extreme t ≥ max supp** (Lemma 3).
   - This is the source proof of `gen:R-continuity` (60-general.tex:18–107) with e replaced by t. All three steps transfer verbatim: the b-bounds, the subsequence/monotonicity argument and the small-x expansion `gen:R-at-zero`.
   - The cap at an extreme eigenvalue beyond the support is exactly Guionnet–Maïda Theorem 1.6 under their Hypothesis 1.1 (gm0406121v3.txt:81–88, 357–383, where λ_max is any limit). *Paid; routine adaptation.* The author agrees.

3. **Lower-outlier deletion** (Lemma 1).
   - The operations: f_N is a symmetric convex function of the eigenvalues, so its partial derivatives are ordered like the coordinates (with ties equal). They sum to 1/2. Raising an o(N) bottom set therefore costs O(q_N/(N−q_N)).
   - Ordering of the gradient of a symmetric convex function is the classical Schur–Ostrowski criterion.
   - Source `gen:counts` (60-general.tex:127–171) already uses the same template: endpoint convexity, equal derivatives within a symmetric block via row rotation of U, and a total squared norm of N to bound the derivative mass carried by the changed coordinates.
   - Fan–Wu Assumption 1.1 and FMWW Assumption 2.1 already allow bounded lower outliers at high temperature. *Paid; routine.*

4. **Scalar-block rank-thickening** (Lemma 2). This is the only proposed new operation. Its steps:
   - (a) For a k-dimensional subspace E on which A_0 = bI, an η-net V of the unit sphere of E with |V| ≤ (1+2/η)^k gives ‖Π_E x‖² ≤ (1−η)^{-2} max_v (v·x)², and hence Z(A_k) ≤ Σ_v Z(A_0 + a′vv^T).
   - (b) Every A_0 + a′vv^T has the same spectrum, and a rotation inside E fixes A_0, so all net pressures have the same mean.
   - (c) Exponential Haar concentration (FW (5.1)) plus a union bound gives E max_v P_v ≤ m′ + O(L√((k log(1/η)+1)/N)).
   - (d) With k = εN and η = √ε, the error is O(√(ε log 1/ε)), and N → ∞ is taken before ε → 0.

   The antecedents for each step:
   - **(a)** The standard sphere net and the max-over-net linearization of a quadratic form. Husson–Ko 2208.03642v2 §5.1, Lemma 5.11 and (5.5) (hk:1596–1626), linearize a sum of top-k quadratic values over a frame net with constant loss. Husson–Ko §7.2, Lemma 7.4 (hk:2920–2935), takes an ε-net of S^{k(N)−1} of cardinality (3/ε)^{k(N)} and controls the quadratic form ⟨u,Wu⟩ over all directions of a k(N)-dimensional space.
   - **(b)** This is precisely the source `gen:counts` symmetry: rotating rows of U inside a degenerate eigenspace preserves the Haar law and the Hamiltonian (60-general.tex:150–163). Husson–Ko §5.1 uses the same invariance step: by GOE invariance each frame has the law of the canonical one (hk:1700–1712).
   - **(c)** Fan–Wu §5 (fw:2255–2290) proves the exponential concentration at every strength, with only an operator-norm bound. A union bound against an exponential tail at each of e^{O(k)} net points with k/N small is literally Husson–Ko Lemma 7.4 ("by a simple union bound", hk:2927–2932) and §5.1 (hk:1741–1747).
     - The source's magnetic proof already uses the pattern "partition sum ≤ sum over polynomially many pieces → maximum over a net → concentration for every net member" (70-magnetic.tex:389–413). The source net is fixed in size and uses fourth moments, so the exponential tail of FW is what lets the net grow to e^{O(εN)}. That substitution is the standard one.
   - **(d)** This is the source's own order-of-limits device: N first at fixed finite alphabet/fixed ε, then refinement, with no uniform derivative bounds (60-general.tex:274–280). The flattening cost b − c_{k_N} → 0 is paid by `gen:operator-comparison` and the support-edge mass property, exactly as in the source's clipping of η_N.

   What is genuinely specific to O234 is the *combination*: flatten the top block to the edge so that all net directions are equidistributed, then compare one spike with an εN-fold spike in the *quenched Ising* pressure, with error vanishing after N → ∞ and then ε → 0. That combination is correct (conditional on the proof gate), short (under one page), and every ingredient is used in its standard role. An expert in this area handed source 234, FW §5 and the observation that gen:counts fails for multiplicity 1 versus εN would reach this argument directly. It is the canonical way to linearize a low-rank quadratic term in a quenched pressure. I find no step where a known tool must be modified, or where a new estimate, construction or identity is needed. *Technical bridge.*

5. **All temperatures, almost sure, local uniformity** (§7).
   - Rescaling, the deterministic K/2 Lipschitz bound in β, Borel–Cantelli on rational β with FW exponential tails (the source's fourth-moment bound would also suffice), and rational meshes.
   - The source's `gen:ground-state` (60-general.tex:362–410) and completion proof (60-general.tex:282–301) use the same devices. *Paid; routine.*

6. **Rank-one stress model** (§9). This is the classical Curie–Weiss/Hubbard–Stratonovich computation. It is a check, not a contribution, and the author agrees.

### Where the statement-level novelty actually lives, and why it doesn't change the verdict

All the outlier-permitting antecedents are high-temperature results: BS Hypothesis 2 / Theorem 1.2 (bs:183–202, small β), FW Theorem 1.3, and FMWW Assumption 2.1 / Corollary 2.8 (fmww:330–339, 590–625, ‖X‖ < 1/2). In their regimes the outlier is *invisible*.

- If the rescaled spectrum lies in [−K,K] with 2K < 1, then H_ρ(t+) ≥ 1/(t+K) ≥ 1/(2K) > 1 ≥ x for every x ∈ [0,1].
- So the branch is never capped on [0,1], the uncapped root is the same for every admissible t, and F(ρ,t) = F(ρ, max supp ρ).

So O234's new statement-level content is exactly the low-temperature regime where the cap at βθ binds. Two things temper this:

- The *form* of the answer is already predicted at the annealed level. The annealed Ising partition function is a rank-one spherical integral (BS (1.16)–(1.18), bs:236–262). Guionnet–Maïda Theorem 1.6 gives its limit with the cap at λ_max only, so other outliers don't enter.
- The source supplies the quenched hierarchy, which is the hard part.

What O234 adds is the transfer of the cap from the annealed to the quenched setting through the routine bridge in item 4. Under the campaign rule that operation-level comparison, not absence of a literal duplicate, decides substantiality, this is TECHNICAL. In ordinary research terms it is a correct and useful extension. Here, "TECHNICAL" refers only to the campaign's contribution bar.

## Eligibility

- **Not DUPLICATE.** None of the read bodies states the O234 theorem. Source 234 explicitly assumes no asymptotic outliers (invariant-sk.tex:80–84, 104–114, 186–205). GM and HK are annealed spherical integrals. BS, FW and FMWW are high-temperature. Bounded absence is not proof of literature novelty.
- **Not INELIGIBLE under the developed-chain rule.** The only developed family-234 chain is I149 C234/S149, the explicit W1-plus-edge modulus for spectra whose two extremes converge to the support edges. It was audited PASS/TECHNICAL in I151 and family-operation-notes. Its operation, a quantitative inversion of H, is not used by O234. O234 changes the multiplicity of a spike outside the support, which C234 never considers. I151's full family-234 operation reading (family-operation-notes:3–17) records no outlier operation.
- **Nonblocking eligibility note for the parent.** The r27 assignment (expanded-target analytic-brief) says "Start a fresh undeveloped source family". Family 234 has a developed technical chain (C234) from the earlier campaign. The parent's brief treats only that chain as excluded, so I do not mark O234 ineligible. The parent should still confirm that admitting a second family-234 target is intended.

## Objections

**Required (for any contribution acceptance):** none that the author can repair inside the frozen target. The verdict is TECHNICAL on the merits of the operation. Under the campaign rules, no rewording, constant improvement or narrower rescue changes it.

**Nonblocking:**

- N1. `234-prefreeze-comparison.md` and `reading-limits.md` cite Husson–Ko §5.1 but omit §7.2, Lemma 7.4 (hk:2920–2935). That lemma is the closer template: a sphere net on a k(N)-dimensional subspace, an exponential tail at each direction, and a union bound with k/N small. Any future manuscript should credit it.
- N2. The comparison doesn't credit the source's own magnetic net/concentration step (70-magnetic.tex:389–413), or the fact that `gen:counts` already contains the in-eigenspace rotation symmetry used for equal means.
- N3. Lemma 1's derivative ordering should be attributed to the Schur–Ostrowski criterion.
- N4. The high-temperature invisibility of outliers (the computation above) would clarify for readers that the theorem's content is the capped regime. It also explains why the antecedents' outlier permissions are harmless.
- N5. Constants: FW (5.1) gives an exponent of about Nε²/(8β²‖D‖²) for their normalization; the candidate's (5) uses a looser 16L². This is harmless, and the proof gate owns it.

## Reading limits (honest and bounded)

**Read in full:**

- author `original-scope.md`, `candidate.md`, README, checkpoint, `234-prefreeze-feasibility.md`, `234-prefreeze-comparison.md`, `adversarial-checks.md`, `reading-limits.md`, `source-map.md`, and the author `verify.py`;
- the parent r1/r2 contribution briefs, contribution-r1-failure.json, contribution-r2-dispatch.json and review-entry.json;
- the review-entry-parent next-discovery brief and the expanded-target analytic brief.

**Read in part:**

- *Long briefs:* fresh-r15-brief.txt (first 6,000 characters plus keyword-located passages on substantiality criteria; 115 KB total, not read end to end) and fresh-r17-brief.txt (first 4,000 characters).
- *NEW-TEN ledger:* headings and verdict lines via grep, plus lines 500–520 and 929–937. It was not read end to end, and tasks.json was not read.
- *Source 234:* invariant-sk.tex:74–349 (model, functional, theorem, context, strategy); 60-general.tex:1–420 (continuity, operator comparison, counts, approximation, completion, random spectra, ground state); 30-rotation.tex:112–200 (concentration lemma statement and first part of proof); 70-magnetic.tex:360–470 and 740–781 (slice net and concentration, block product start, final concentration). The other source files (10-arrays, 20-field, 40-upper, 50-cavity, the rest of 70-magnetic, and 60-general.tex:420–634 on Wishart) were not read. I rely on the I151 family-operation-notes account of those files, read by me in full for family 234 (lines 3–30).
- *Primary sources:*
  - Husson–Ko: hk:1–140 and 1596–1760 (§5.1 complete), 2791–2990 (§7.2 through Lemma 7.4 and the opening of Proposition 7.7).
  - Fan–Wu: fw:2255–2345 (§5 complete).
  - Guionnet–Maïda: gm:81–107, 150–300 and 330–420 (Hypothesis 1.1, Theorems 1.3, 1.4 and 1.6 with discussion). I did not read GM §5 proofs.
  - Bhattacharya–Sen: bs:180–262 (Hypothesis 2, Theorem 1.2, the annealed spherical-integral identification).
  - FMWW: fmww:330–339 and 580–628 (Assumption 2.1, Corollary 2.8 statement). Not its proof.
- *History:* i149 snapshot lines 100–120 and 185–214, i151 snapshot lines 45–91, family-operation-notes lines 1–30 and the grep-located family-234 lines, and prior-overlap-notes (first 1,500 characters of each line).

**Not done:**

- No new web or literature search, so no worldwide novelty or priority claim.
- I did not read the published 2025 Husson–Ko version.
- Hopfield-model results with p = o(N) or small α, which use similar sphere-net reductions of low-rank quadratic terms, are a natural further comparator class. I did not read them, and they do not bear on the verdict.
- I did not read `o234-proof-r1/`, by design.
- I did not re-run `finite_diagnostics.py`. Finite diagnostics cannot affect a contribution verdict.

No checksum, verifier result or finite test is a proof or a contribution certificate.

## Seal

Membership of this review directory is fixed by `manifest.json`. `verify.py` is read-only (no network, subprocess or writes) and requires `--anchor <external SHA256 of manifest.json>`. It checks exact file and directory membership and per-file bytes/SHA256, and rejects symlinks and special files.

The only files not listed in the manifest are `manifest.json` itself and `seal-receipt.json`. The receipt is written after sealing and records the reviewer's positive and wrong-anchor control runs. The receipt is not authenticated by the anchor.

The manifest SHA256 is reported to the parent out-of-band in the final message.
