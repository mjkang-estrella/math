# T298P independent contribution review, round 2

Role: contribution and eligibility only, **conditional on correctness**. This round takes over after round 1 failed with a provider rate limit. It is not an appeal or a rating escalation. Correctness belongs to the separate proof gate. I did not open any `t298p-proof*` path or `t298p-parent/proof-r1-brief.txt`, and I did not infer the proof gate's result.

Stipulations: the pinned OpenAI theorems and their proof operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are taken as true. External primary results are applied only under their printed hypotheses. This review accepts nothing and changes no count. Only the parent can accept.

Reviewed object: the sealed author packet `fresh-structural-discovery-r104`.

- `MANIFEST.json` sha256 `b6c525288bd6a7203d13c8b8ed4b696e14a0f8c3a06cd30cb6fbe871d6dfbeb3`.
- All seven dispatched anchors and the 13223-entry tree anchor `eeecc1da…5e09b` were recomputed and match.
- Frozen scope: `scope-freeze.md` sha256 `8e9b3f5f…589e`, unchanged.

Full frozen target, unchanged: there exist exactly two bounded self-adjoint Z1, Z2 in a von Neumann algebra with faithful normal tracial state such that

  −∞ < χ(Z1,Z2) < χ*(Z1,Z2) < ∞.

Here χ is the original operator-norm-cutoff, limsup-over-matrix-sizes microstates entropy with unnormalized Hilbert–Schmidt Lebesgue volume.

## Verdict

**SUBSTANTIAL, conditional on correctness, for the full unchanged target.** Four REQUIRED attribution and comparison corrections are unresolved in the frozen packet (§4). None of them changes the theorem, the proof or the classification. Each must be resolved in any acceptance record or manuscript.

This is my own assessment. I re-derived the round-1 draft's operation-level findings from the primary bodies and adopt most of them. I state below where I refine or add to them.

- **Not DUPLICATE.** None of the following contains a finite strict χ/χ* gap for two variables, or an unconditional finite-part matrix-amplification identity that would yield one:
  - the actual source and companion bodies I read;
  - the three closest primary bodies;
  - the pinned two-generator preprint;
  - the bounded campaign history and literature screen.
  
  Source298 states that its construction "does not address equality for every smaller prescribed number of variables" (`01-introduction.tex`, after `thm:main`). That sentence shows only that the source does not already contain the result. It is not evidence of substance.
- **Not INELIGIBLE.** The claimed result is the full frozen statement, with exactly two variables, both entropies finite, original χ and the ordinary limsup. It also claims the stronger transfer (1). Neither is relative, ultrafilter-only, many-variable, −∞-entropy, based on factor isomorphism, or conditional on matrix units. Entropy depends only on the joint law, so W*-generation is not required.
- **Not BLOCKED.** I read the actual operations that could pay the bridge (reading limits in `reading-limits.md`). Contribution is assessable conditional on correctness.
- **Not TECHNICAL.** I tried each available reduction to paid operations (§2). Each fails at a named operation. The structural reason is §2.1: at the target pair, both paid relative quantities equal −∞. On the χ side this holds along every free ultrafilter, where the paid §5 equality lives; on the χ* side it holds exactly. Both conditioning-removal excesses are therefore +∞. The paid relative identities, combined with the classical one-sided inequalities, therefore cannot by themselves produce the finite target gap. The transfer needs three operations that no read body supplies:
  - **U1.** An unconditional, orbit-cheap free Fisher bound (candidate (3)).
  - **U2.** An unconditional normal-tube volume upper bound, valid for every output size, with the same constant C_D as the lower bound, at the ordinary limsup (upper half of (2)).
  - **U3.** The coupling of U1 and U2 through the exact free normal/orbital noise split and the relative analytic straightening. On both sides this makes the gauge orbit cost only O(ε) in the increments.

I do not infer novelty from the missing two-variable statement, the length of the proof or the audit effort.

### Conditions of this classification (not objections to the frozen bytes)

The classification assumes that the separate proof gate passes the unchanged argument, in particular:

- **(a)** inequality (3) holds as an unconditional bound. No relative-to-M_k score is discarded into it, and no upper Fisher continuity is used.
- **(b)** the upper half of (2) holds for every output size N at the ordinary limsup, with the same C_D as the lower half.
- **(c)** the noisy-endpoint bound χ(H_ε) ≥ χ(U) − O(ε) holds via Shlyakhtenko Theorems 2.19 and 4.1 under their printed hypotheses.

If (a) or (b) is repaired by a different mechanism, the classification must be redone. If either is replaced by a relative, ultrafilter, or multiples-of-k-only statement, the frozen target is not met, and that outcome would be INELIGIBLE, not TECHNICAL.

## 1. Operation ledger

| Candidate step | Closest paid operation (actually read) | Status |
|---|---|---|
| Base pair D with scalar commutant; tangent rank k²−1; normal dimension k²+1 | Finite linear algebra. Independently reproduced exactly over Q for path and star trees, k=2..6 (K1) | Routine |
| Finite χ of E_ε(X) (local chart, Jacobian, GUE norm tail, source subsequence) | Source298 `eq:gue-norm-tail` and selected-ensemble pattern; Voiculescu chart volume arguments | Technical |
| Orbit × fiber volume factorization; constant c = 3/4 + ½log2π; unitary-group volume formula | NSS math/9809081v1 Lemma 2.6 (polar measure factorization with C_k = Vol U(k)), Lemma 2.8 (the same limit in the same Re Tr metric; Marinov), Lemmas 2.9/2.10 (orbit upper/lower pattern); classical Vol U(l) formula (K3 reproduces the constant) | Paid constant. C_D bookkeeping is routine (K2: log d coefficient 0, log k coefficient 1) |
| Lower half of (2): bundle over source microstates; source subsequences kept as kd | NSS Lemma 2.10 pattern; Shlyakhtenko §5 second claim (measure-preserving packing of entry microstates into matrix microstates) | Global tube injectivity with uniform radius is technical |
| **U2.** Upper half of (2) for every N: exact band traces 1/k; tree-polar truncation and common-root intersection; second root truncation; inverse back to source microstates; projection η-nets and complement-volume cost θlog(C/θ)+θlog(C/η); ordinary limsup | NSS Lemma 2.9 is exact only because polar decomposition covers all of M_k. Shlyakhtenko §5 first claim compresses to a corner p ≤ e11 of **supplied** matrix-unit conditioning microstates, is an equality only along ultrafilters, and has a one-sided ordinary-limsup form whose proof is "left to the reader" | **Unpaid.** Matrix units must be recovered from the pair's own microstates. The bound is unconditional, holds for every N, and carries the same constant as the lower bound |
| **U1.** Φ*(Z) ≤ Φ*(U)/(ε²k⁴) + Cε⁻¹(1+Φ*(U)) via coarse normal derivations plus inner derivations, Neumann series and projection | NSS math/9809080v1 Prop. 4.1: Φ*({g_ij}:B) = d³Φ*(G:M_d(B)), relative to M_d(B), plus the projection Φ*(G) ≤ Φ*(G:M_d(ℂ)) | **Unpaid.** The paid route is non-integrable at t=0 for this encoding (§2.1, K4). Inner derivations replace the relative orbital cost (k²−1)/u by O(1) adjoint norms |
| Exact free normal/orbital noise decomposition at t = ε²k²u | Orthogonal invariance of free semicircular families; the entry normalization "2k² semicirculars divided by k" | Routine identity. Its role in U3 (the heat path stays inside the encoded form) is part of the coupling |
| Noisy straightening H_ε = U + εR_ε; χ(H) ≥ χ(H\|T) = χ(U) − O(ε) | Shlyakhtenko Prop. 2.8 (with Voiculescu χ(X:Y) ≤ χ(X)); Thm. 2.19 (its proof gives the fiber ratio for every large size, so the ordinary limsup is kept); Thm. 4.1 (statement only: proof omitted in v1) | Paid operations. The contraction construction of the inverse series is technical |
| **U3.** Same C_D at both endpoints; gap ≥ k⁻²[g − gap(X+√U₀S)] − O(ε) | none | **Unpaid coupling** |
| Strictness: gap(0) ≥ Δχ − Δχ*; large-noise source gap → 0; finiteness | Source298 two-noise-scale template and `eq:chistar`/`eq:freeflow`; Shlyakhtenko Prop. 4.2 (Gaussian lower bound; embeddability hypothesis; printed "n log" is n/2 by its own proof); covariance bound for χ*; χ ≤ χ* (Biane–Capitaine–Guionnet; Jekel–Pi, as cited in source298) | Routine |

## 2. Attempted reductions to paid operations

### 2.1 Structural obstruction: the paid relative theory is degenerate at the target pair

Both conditioning-removal excesses are nonnegative in general:

- I_micro = χ(Z) − χ(Z|M_k) ≥ 0, by Shlyakhtenko Prop. 2.12.
- I_star = χ*(Z) − χ*(Z:M_k) ≥ 0, by the projection inequality Φ*(Z) ≤ Φ*(Z:M_k) recalled with NSS Prop. 4.1.

The relative quantities are paid: via Shlyakhtenko Thm 5.1 (ultrafilter equality) and NSS Prop. 4.1 (exact Fisher identity). Write the unconditional gap as

  gap(Z) = [χ*(Z:M_k) − χ(Z|M_k)] + I_star − I_micro.

At the actual target pair Z_ε = D + εVX, the 2k² real entry coordinates lie in a (k²+1)-parameter affine family, so they satisfy k²−1 independent real-linear relations. Hence:

- **Microstates side.** The entry tuple has χ = −∞ (linear relations), so for every free ultrafilter Shlyakhtenko Thm 5.1 gives χ^ω(Z_ε|M_k) = −∞. The ordinary-limsup form of §5 is one-sided, and it bounds the relative entropy only from below by the entry entropy. It therefore supplies nothing here.
- **Fisher side.** Along the heat flow the relative Fisher information is exactly [Φ*(U(u)) + (k²−1)/u]/(ε²k⁴). This follows from NSS 4.1, converted to real coordinates orthonormal for the normalized trace, and free additivity for U free from T. As a check, the free scalar semicircular pair gives 2 = 2k⁴/k⁴. With dt = ε²k²du, its orbital part is ((k²−1)/k²)·t⁻¹. That is non-integrable at t=0, so χ*(Z_ε:M_k) = −∞.

At the target pair the paid identity is therefore −∞ = −∞ (for χ, along every ultrafilter; the ordinary-limsup relative χ is not computed by any read body). Both excesses are +∞, or undetermined in the ordinary-limsup χ case, and the target needs exactly their finite difference to O(ε). An alternative would be to start at a noisy pair u₀ > 0. Conditional on the candidate's own formula (2), the microstates excess there is

  I_micro = −((k²−1)/(2k²))·log(ε²u₀) + O(1).

The paid relative Fisher increment carries the same coefficient, ((k²−1)/(2k²))·log(U₀/u₀) (K4). Both diverge as ε → 0 or u₀ → 0, so the paid route needs these two divergent orbital terms to cancel to O(ε). No read body computes either excess. The candidate replaces this cancellation of divergent relative terms with U1 and U2, which are direct unconditional estimates. This is the precise unpaid operation. K4 checks only the coefficients, and only conditionally on the candidate formulas.

### 2.2 Other attempted reductions

**(a) Pure packing with free fillers (Shlyakhtenko §5 and NSS 3.1/4.1).** This gives the relative gap k⁻²·gap(entries), with only an ultrafilter conclusion on the χ side. NSS Theorem 3.1 uses χ(Z|B) ≤ χ(Z) one-sidedly. Its relative-to-unconditional equality is used only when Z is ∗-free from 1⊗M_d. That is a strong constraint on the joint entry law (R-cyclicity, in another Nica–Shlyakhtenko–Speicher paper that I did not read at body level). Nothing makes an arbitrary source tuple satisfy it, and the target pair is not free from M_k. Fails at I_star − I_micro.

**(b) Conditioning on matrix units recovered inside W*(Z).** The spectral-band and tree-polar matrix units f_ij lie in W*(Z), and conditioning on them is legitimate. However, the off-diagonal f-entries of Z1 then vanish identically. NSS 4.1 then gives an infinite relative Fisher information, and §5 gives χ = −∞ on the small side of its one-sided inequality. Fails, for the same degenerate reason as §2.1.

**(c) Free Haar rotation.** If w is a free Haar unitary, wZw* is free from M_k and has the law of Z. Then χ(Z) = χ(wZw*|M_k), but its entries are not the source tuple. This is a tautology. Fails.

**(d) Generator and isomorphism routes.**
- Companion287 (`cor:entropy-dimensions`, `amplification.tex`) transports tuples coordinatewise, preserving their length and joint law.
- The pinned *Relative generation and the generator problem for finite factors* (Sept 23 2026, `thm:main`) gives two self-adjoint W*-generators for every separable II₁ factor. It uses the classical 2×2 matrix encoding (Douglas–Pearcy/Wogen; DSSW Prop. 1.1). That is exactly the "classical generator trick".
- Its own `cor:entropy-generators` proves that δ and δ₀ change under replacement of generators: the pair has dimension ≤ 2 < n.

W*-generation therefore says nothing about the pair's entropy values, and factor isomorphism is not entropy invariance. I authenticated these bodies independently (git-blob and tree match) before relying on them. Fails.

**(e) Transplanting the source block witness with one or two signals.** encoding-attempt.md §3 shows the copied terminal event becomes typical: an eigenspace partition of D1 retains energy → v > r/16. At contribution level this is a sound obstruction to that specific copied witness. Fails for the source mechanism.

**(f) Dimension-level and orbital literature.** Jung math/0410594 Lemma 3.1, Shlyakhtenko 2201.09503, Connes–Shlyakhtenko inner-derivation δ*, and the orbital free entropy of Hiai–Miyamoto–Ueda and Ueda were seen only by abstract or snippet. There is a structural reason they cannot pay the finite part:
- Exact matrix units are projections with χ = −∞, so any finite-χ statement must replace them by a perturbed generic pair, as the candidate does.
- Dimension statements are insensitive to the O(d²) volume constants that decide the gap.
- Orbital free entropy would at most re-express U2. U1 would remain unpaid unless a general equality between mutual free information and orbital free entropy were available; to my bounded knowledge that equality is known only in special cases.

Not read as bodies; disclosed in the reading limits.

## 3. Contribution at operation level

The source enters as a black box: its finite-gap tuple (g ≥ 1/2), finite Fisher information after smoothing, embeddability, boundedness and n = 2⁶⁴+1. The new engine is an unconditional reduction from k²+1 variables to 2 that preserves the gap up to the factor k⁻². It works for these reasons:

- The base pair has scalar commutant, so the gauge orbit has full dimension k²−1 and the normal fiber has dimension k²+1.
- On the microstates side, the orbit contributes the same constant C_D at both noise endpoints. This needs U2: matrix units recovered from arbitrary microstates of every size, with vanishing rank loss.
- On the Fisher side, inner derivations make the orbit directions cost an O(1) score norm instead of the relative (k²−1)/u. This is U1.
- The exact free normal/orbital split keeps the heat path inside the encoded form, and the relative analytic straightening absorbs the orbital noise into the gauge. This is U3.

Every constituent is classical, as the author acknowledges. Their combination supplies the two unconditional finite-part estimates that the paid relative theory provably cannot deliver at this pair (§2.1). Classical work leaves only the one-sided inequalities χ(Z|M_k) ≤ χ(Z) and Φ*(Z) ≤ Φ*(Z:M_k).

## 4. REQUIRED objections (attribution and comparison; unresolved in frozen r104)

None of these changes the frozen theorem, the proof or the classification.

1. **Credit the orbit-volume components and narrow the novelty claim to U1/U2/U3.** comparison.md lists "a global associated normal bundle gives matching chi volume constants" inside the new operation. The following are paid and must be credited:
   - the polar/orbit × fiber measure factorization and the orbit constant 3/4 + ½log2π, from NSS math/9809081v1 Lemmas 2.6 and 2.8 (same Re Tr metric) with the upper/lower orbit patterns of Lemmas 2.9 and 2.10;
   - the classical unitary-group volume formula.
   
   Global tube injectivity with a uniform radius is technical support. The microstates novelty must be stated as U2 (unconditional, every N, intrinsic matrix-unit recovery, rank-loss accounting, ordinary limsup), together with the coupling U3.
2. **Credit the Shlyakhtenko §5 corner/compression/packing pattern, and state its limits exactly.** The pattern is a corner p ≤ e11 with [e11,p]=0, the compression map T, and measure-preserving packing. The record must state:
   - §5 conditions on supplied matrix-unit microstates;
   - its equality holds only along ultrafilters;
   - its ordinary-limsup statement is one-sided, with proof "left to the reader";
   - the second displayed claim has a direction typo (the proof shows the reverse of the printed inequality).
   
   Also record the §2.1 observation: at the target pair, both relative quantities are −∞.
3. **Cite explicitly the paid results now invoked generically.** These are:
   - Shlyakhtenko Prop. 4.2, for the Gaussian lower bound in candidate §5 and matched-volume E. State its embeddability hypothesis and that the printed "n log 2πet" is (n/2)log 2πet by its own proof.
   - The covariance (semicircular maximum) bound for χ*.
   - χ ≤ χ* (Biane–Capitaine–Guionnet; Jekel–Pi).
   - Shlyakhtenko Prop. 2.8 with χ(X:Y) ≤ χ(X), for χ(H) ≥ χ(H|T).
   - The source298 heat-flow identity and two-noise-scale strictness template (`eq:chistar`, `eq:freeflow`, introduction).
   
   The strictness step of candidate §5 belongs to that template and is not part of the new operation.
4. **Address the pinned two-generator preprint.** *Relative generation and the generator problem for finite factors* (`thm:main`, `cor:entropy-generators`) is the same-corpus two-generator theorem. It uses the classical 2×2 matrix encoding, and the packet's comparison omits it. The record must state that it pays W*-generation only, and that its own corollary shows the entropy dimensions depend on the generators. Otherwise "source298 plus the pinned two-generator theorem" would appear to give the target, and it does not.

## 5. Optional

1. Add §2.1 (both relative quantities −∞ at the target pair; the divergent orbital coefficient ((k²−1)/(2k²))·log) to the comparison. It is the cleanest operation-level reason that the result is not a transfer.
2. If the argument is general, state the transfer theorem for every bounded, embeddable (k²+1)-tuple with finite χ and finite Φ* (k ≥ 2), then specialize to source298. This changes presentation only; the frozen scope is unchanged.
3. Present the free normal/orbital rotation, the 1/k entry normalization and the finite-algebra bookkeeping as classical.
4. Shlyakhtenko Thm 4.1 has its proof omitted in arXiv v1 ("almost identical to … [4]"). Cite a version containing the argument, or flag that only the statement and its printed hypotheses are used. Whether those hypotheses are met is the proof gate's question.
5. In any manuscript, screen and cite at body level the dimension and orbital analogues: Jung math/0410594; Shlyakhtenko 2201.09503; Hiai–Miyamoto–Ueda math/0702745; Ueda 1210.6421 and 1610.04118; arXiv 1306.5372 (*Remarks on free mutual information and orbital free entropy*); Connes–Shlyakhtenko. I saw these only at abstract or snippet level.
6. Keep the explicit statement that ε is existential and non-effective, and that g/k² ≈ 2⁻⁶⁵ is not a quantitative claim.

## 6. Disposition of the round-1 draft findings

- **Adopted after independent re-derivation from the primary bodies:**
  - the SUBSTANTIAL classification and the U1/U2/U3 decomposition;
  - reductions (a)–(g) of the draft, renumbered here as §2.2(a)–(f) and §2.1;
  - required items 1–4, sharpened: item 2 now records the §5 direction typo and the "left to the reader" ordinary-limsup proof, and item 3 credits the strictness template.
- **Added:**
  - §2.1, the degeneracy of the relative theory at the target pair (−∞ = −∞), with the exact matching log coefficients (K4);
  - the DSSW 2×2 encoding as the precise "classical generator trick";
  - the structural reason that dimension-level results cannot pay finite parts;
  - the INELIGIBLE, rather than TECHNICAL, consequence if (a) or (b) is replaced by a weaker statement.
- **Not adopted:** nothing material was rejected. I did not rerun the round-1 C1–C5 scripts. My K1–K4 checks are independent and separately written.

## 7. Evidence and limits

- `contribution-checks.py` and its output `contribution-checks.json` cover K1–K4. All checks pass, and two runs were byte-identical. These are finite attribution and normalization diagnostics. They prove no entropy or Fisher statement.
- `checks.json` records:
  - the anchor recomputation;
  - the author verifier, read before execution, which passed;
  - six copied author-verifier controls with reasons checked;
  - authentication of the generator-preprint blobs;
  - confirmation that the round-1 bytes are unchanged;
  - the state of the author-side attribution packet.
- `verify.py` is the read-only anchored verifier for this directory. `controls.py` reproduces the copied controls under /var/tmp.
- `reading-limits.md` gives the exact reading extent.
- No worldwide priority claim is made.
