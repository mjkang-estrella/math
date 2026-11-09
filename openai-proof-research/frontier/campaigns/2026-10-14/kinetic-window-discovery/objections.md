# Disposition of prior I340 objections and carried-forward gaps

2026-10-14. Sources: `frontier/experiments/i340_kinetic_path_fluctuations/{analysis.md,reading-and-failures.md}`
and `frontier/iterations/i340-*.md`. These are read-only and preserved unchanged. Section numbers
refer to `analysis.md` in this directory.

## A. Prior proved partials (carried forward, not counted as new)

| Prior item | Use here |
|---|---|
| Continuous Gaussian coordinate modification (prior §2, parent) | identifies the limit in §7 step 1; re-checked, unchanged |
| Uniform exact-centring transfer ‖X−X̂‖_∞→0 (prior §3, parent; H `lem:center-transfer`) | §7 step 3; unchanged |
| Uniform deterministic-time moments (prior §4) | not needed; Prop. B contains the δ=t case |
| Indefinite integrals converge in C (prior §5) | superseded, not needed |
| Fourth increments ≤C[(δ+rᵋ)²+μ⁻¹(δ+rᵋ)] (prior §6) | **superseded** by Prop. B: C(δ²+δ/μ)+Cμ²ε^P |
| Transport/current identity (prior §7) | not needed: the proof bounds X̂ increments directly |

## B. Prior open gaps, each carried forward explicitly

| Gap as recorded on 2026-10-13 | Status now |
|---|---|
| Requested D([0,T],ℝ^m), J1 limit | **Proved, subject to an independent gate** (Theorem K) |
| Window-localised connected estimate for redundant marked contacts, preserving the μ root gain, fresh-label factorials, restarts and summability | **Supplied** by Lemma A (§3). Root gain μ^{1−h}ε^p, fresh-label counting and the base Cτ√L are unchanged. The only cost is the factor e(1+a)/τ, plus one 1/ε paid by a link's ε when p≥1. |
| Microscopic close-collision or equivalent closure at the same cutoff | **Supplied** at α=μ⁻⁷ᐟ³ by Prop. C, an equivalent closure via EZ_W³. It is not a close-pair estimate. It relies on R1. |
| Unquantified rᵋ amplified by μ^{28/9} in GRR | **Eliminated.** The remaining additive error is Cμ²ε^P, and μ²ε^Pα^{−4/3}→0 for P>92/9; P=12 is used. |
| Stopping-time / Aldous estimate | **Still unproved, and not needed.** Neither this nor a mixed adjacent-increment bound is claimed. |
| Fresh independent proof gate | **Not done** for this work. Recommended before counting. |

## C. Prior objections, one by one

1. **"Redundant contacts have determined times. The coarea integral is an intersection indicator
   of mass ≤1, with no independent dt."** Correct, and it is not contradicted. Lemma A never gives
   a redundant atom its own coordinate. It uses the free direction 𝟙 (all merger times together,
   with link vectors sheared), along which every contact time has derivative exactly 1 (F2).
   Averaging over that direction converts {t_r∈W} into |W|/Λ (A.3).
2. **"A new compatible chart or cut must preserve μ^{1−h}, the fresh-label factorials, all restarts
   and summability."** The flow T_λ is a unit-Jacobian translation of H's own chart. Nothing is cut,
   and no activity, root normalisation or factorial is changed. Restarts and slab assignments enter
   only through the domain Δ_G, which is swept to Δ_G^Λ. Its volume is at most e times H's, and the
   pair-sum induction is unchanged (§3.5).
3. **"Spanning-tree exchange making the marked contact a free coordinate."** Not used. That
   exchange would require the scattering derivative ∂ω/∂X~1/ε.
4. **"Global signed negligible cycle measure is not a no-cycle event for the whole gas."** Not used.
   Lemma A bounds every bounded-complexity connected diagram, tree or cyclic, directly. No cycle is
   claimed absent.
5. **"The collision current is not a martingale."** No martingale is used. The proof bounds
   increments of X̂ through cumulants.
6. **"Small jumps do not imply tightness."** Agreed. Prop. C needs the quantitative count bound
   max_jZ_{W_j}=o_P(√μ), proved from the third moment, plus GRR above scale α. Jump size alone is
   not used.
7. **"Independently resampling each slab destroys the correlated interface law."** Not used.
   Everything is on the one pasted process.
8. **"DHM/H primitive-pair bound needs a simultaneous velocity restriction and is not an arbitrary
   close-collision bound."** Not used.
9. **"A fixed observation count is not a growing grid."** Respected. Prop. B uses one two-pulse
   expansion for each pair (s,t). Prop. C uses one single-flag expansion for each cell. The union
   over cells uses constants uniform in the cell (§2, R3), never one expansion with O(1/α) pulses.
10. **"BGSS 2008.10403v2 short-time proof already known; 2201.04514v1 stationary patching does not
    apply."** Credited and not reused. Our window factor is not BGSS's clustering-time localisation
    (their §8.2 point 3, read). Our microscopic step is not their two-collision estimate (their
    Lemma 6.2.5, read). Only the GRR strategy is shared.
11. **"Cannot diagonalise the cutoff without its microscopic estimate."** The estimate is proved at
    the same α=μ⁻⁷ᐟ³. The admissible range is μ^{-a} with a∈[1,3) (`checks/exponents.py`).
12. **"Mixed adjacent increments / maximal / Aldous only if genuinely proved."** Not claimed. A
    two-window analogue of Lemma A is **not** available from one flow when the later of the two
    windowed atoms is redundant. That is why the route goes through Prop. B plus Prop. C.

## D. Smallest remaining unpaid operation

Within the stipulated-source contract none is known. The proof is complete modulo R1–R5 in
`analysis.md` §9. The single non-literal extension of H is R1: the collision-flag records. If R1
were rejected, the smallest unpaid operation would be a bound E Z_W³ ≤ C(μ|W|+μ^{−M}), uniform in
cells of length 4μ⁻⁷ᐟ³, for the number Z_W of particles with an accepted collision in W, on the
pasted process. Lemma A already pays the window factor for any record that detects a C-atom of a
designated line in W. Only the expressibility of that record in H's marked hierarchy would remain.
