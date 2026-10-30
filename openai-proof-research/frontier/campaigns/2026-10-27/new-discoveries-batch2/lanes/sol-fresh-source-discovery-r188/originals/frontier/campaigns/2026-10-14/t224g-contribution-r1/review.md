# T224G independent contribution review r1

Role: contribution/eligibility only, **conditional on correctness**. The separate proof gate owns correctness. I did not read its outputs, the parallel reviewer's result or any T224G parent disposition. Pinned OpenAI theorems and their proof operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated. This verdict counts nothing alone. Only the parent can accept.

## Verdict

**TECHNICAL** for the full unchanged target (scope-status.json `ab52a8e5…e2e4`). The target is a conditional-on-initial-uncolored-geometry, full-plane `D([0,T],H_C)` J1 limit for every finite T at the r_e/2 unit-pivotal clock.

- **Not DUPLICATE.** The bounded search found no proof of this theorem, either externally or in campaign history. I26 named the target, and I149 proved only the frozen-geometry analogue.
- **Not INELIGIBLE.** The target was neither weakened nor replaced.
- **Not BLOCKED.** Contribution can be assessed conditional on correctness.
- **Not SUBSTANTIAL.** Every quantitative engine that the bridge needs is a stipulated source operation, and each source operation is used for the purpose it was built for. The new material is an exact four-case algebraic identity, standard Poisson and J1 compactness bookkeeping, and careful quantifier checking. I could not identify an unpaid analytic estimate.

The decisive point is analytic. The only place where geometric birth/death differs from colour refresh at leading order is the fair-insertion drift. The unsigned bound (e/h)^{5/4} is not small after the 1/a_e normalisation, so that drift needs a better-than-inverse-square signed cancellation. Source A states this cancellation as its own purpose and proves it (A00 lines 113–121; Corollary `tr:insertion`, A05 820–909). A06 already uses it to differentiate in Poisson intensity, which is a static birth. The candidate supplies the identity showing that the drift is exactly that message with an exterior-measurable coefficient. It does not supply a new estimate.

## Explicit operation-level reduction (quantifiers preserved)

Notation: V = *From critical crossings…*, A = *A Pivotal Amplitude…*, GPS = arXiv:1305.5526v4.

| Candidate step | Reduction to paid operation(s) | What is genuinely added |
|---|---|---|
| R1 Lifetime decomposition (persistent/initial-death/birth; replica marking with shared initial points) | Independent marked Poisson particles; thinning; Mecke/factorial-moment expansion as in V05 eq. `site-expansion` | Bookkeeping. Base mesh change e'=e·exp(aT/2) absorbed by A Thm 1.1 ratio |
| R2 Simultaneous presence-subset support / forest majorant | V05 190–383 verbatim. V's kernel already *inserts nuclei*, and V05 ~229–232 already says "Even if its witness uses different times, the bits on the probe are critical and constant in time". V05 ~263–266: "Forced nuclei all lie outside these buffers". V05 cutoff Γ_e is "increasing under addition". Changed cell is localised inside the probe's inner boundary by V02 localization | Checking that absence of a selected nucleus is also shielded by base screens, i.e. monotonicity of occupancy screens under addition. That is a one-line check of a property the source states |
| R3 Local two-time table: birth/death = one refresh kernel + fair-insertion marginal (C+D/2)E(v−u) | Four-case enumeration (I verified (1)–(3) of single-jump-replacement.md by hand). Drift bounded by A Cor. `tr:insertion`, C(e/h)^{2+ν}, against seam/exterior data, as its contract allows. Normalised margin e^{3/4+ν}h^{−2−ν} | The identity itself and the observation that its coefficient is exterior-measurable. Neither is a new estimate |
| R4 Fixed-k telescoping; six-wall failure; inactive protection; common-geometry correction; H1H2−I split | V07 eq. `all-disk-replacement` (successive single-site replacement with other sites retained). V06 ~500: "Necessary probes at x_i, i≥2 … contribute at most C P_e". Six-arm bound and bank construction from V02 `color-arms`. Protection event and E[p_e(η)²]≤C A(l,R)² from V06 545–600. A02 cap lemma (planar-pairing extension). Location UI from V05 385–458. Common calibration from V07 1–158 | Re-running these patterns with one geometric slot. The double-active shared-site term uses the same second-moment arm bound in place of V's q_e repeated-label factor. That is an adaptation, not a new bound |
| R5 Path-valued TV series and finite-quad J1 tightness | V05 bound is uniform over arbitrary centred weights and depends on them only through ∏‖w‖_TV, so a path-valued signed measure inherits it. Compactness of ≤2k-jump paths with bounded jump-time densities is textbook (Billingsley/Ethier–Kurtz). Campaign I149 §4.3 already ran the same tightness → deterministic-time continuity → FDD identification chain (technical) | Using mark-density domination in place of I149's reversible-clock lemma, needed because geometry changes |
| R6 H_C topology | GPS Prop 3.9(i) (I confirmed the uniform statement in private gps.txt 1140–1195), Def 3.3, full-plane metric (9.7), Thm 2.7 boundary nullity, J1 metric Prop 4.1 | Finite-range selector argument. Routine |
| R7 Quenched upgrade | One/two-replica first and second moments, as in V07 and I149 §4.3 (Markov on compact complement, bounded-Lipschitz net) | None new |
| R8 Clock | Deterministic time change of the GPS law. BPY 2407.13502v1 Prop 3.15 pays factor 2 | None |

Composing R1–R8 reproduces exactly the full original statement: every T, full plane, H_C, J1, conditional law given initial uncolored geometry, in probability. No step weakens a quantifier. The reduction is the candidate's own proof with each operation attributed.

## REQUIRED objections (numbered)

1. **Undisclosed campaign antecedents (I26, I149).** comparison-and-dependencies.md and geometric-dynamics-interface.md list excluded histories but omit two items.
   - `frontier/iterations/i26-probability-discovery-resumed.md` §2.A (2026-10-09) formulated essentially this target: birth–death Voronoi dynamics, conditional on initial uncolored geometry, finite-vector J1, at a_e=c_geo·r_e. It named the missing bridge as "a signed local replacement theorem for this geometric generator" plus path tightness.
   - `i149-spectral-stochastic-universality-discovery.md` §§2–4 (2026-10-10) proved the frozen-tessellation colour-refresh quenched path law "C224" at crossing-coordinate scope. It classified that result TECHNICAL and parked only the geometric/spatial-marking route (G149).

   The candidate fills I26's named gap and lifts C224's topology to H_C. Neither antecedent is a duplicate, but both must be disclosed in any record or manuscript. Their technical classifications are directly relevant: the path/quenched half of this candidate repeats I149's chain.
2. **The "time-list-independent strengthening" is already in the source.** path-series-tightness.md §1 presents time-list independence as a strengthening. V05's own proof states that the witness may use different times while the probe bits are constant in time, and its bound depends on weights only through TV. Present this as an observation, not as a contribution.
3. **The central "new" step is a paid tool applied to its design purpose.** Recognising that A Cor. `tr:insertion` controls the birth/death-versus-refresh drift is the key insight, and I26 had missed it. A's introduction already describes fair Poisson insertion integrability in location as the role of this corollary. Applicability insight plus a four-case identity does not meet the campaign's "substantial new operation" bar.
4. **Fixed-k replacement and replica protection are V06/V07 patterns.** Retaining the other k−1 arm factors, six-wall removal and inactive protection are explicitly present in V. The common-geometry correction C_active(R_inactive−I) and the H1H2−I split are exact algebra plus V06's second-moment arm bound.
5. **No literature-priority claim.** External search was bounded (three web queries; see reading-limits.md). It found no primary scaling-limit theorem for geometric Voronoi dynamics. BPY Thm 1.4 and Vanneuville cover noise scale and frozen dynamics. Ahlberg–Baldasso arXiv:1708.03054 (relocation dynamics, noise sensitivity) was seen as a snippet only. The theorem is therefore plausibly new as a statement. That novelty is conditional on the 2026 stipulated sources and does not convert a technical bridge into a substantial one. Any external write-up must say so.
6. **Correctness not assessed here.** TECHNICAL is conditional on correctness. Several interfaces could be wrong without changing this classification: simultaneous subset shielding, exterior-measurability of the drift coefficient under the other sites' time-varying exterior data, six-wall handling inside boundary strips (given the four-nucleus counterexample), and the mark-density J1 argument. If any interface needs a genuinely new estimate to repair, contribution must be re-reviewed. A repair could raise the classification.

## Optional items

- O1. The hidden-rate counterexample and the four-nucleus boundary example are nice cautionary content for an exposition. They are not contribution.
- O2. An exposition could usefully state the general principle: geometric Poisson insertion = colour refresh + symmetric insertion message. It explains why OU geometric dynamics and colour refresh share the same scaling limit, which matches BPY's factor-2 heuristic at path level.
- O3. The author's reading-limits correctly flag unread A05 transfer proof and GPS cited bodies. These are stipulated, not a contribution issue.

## Family 224 eligibility note

Family 224 already holds critical (Cardy), amplitude and quenched near-critical results, plus campaign technical extensions (I26 screen, I149 C224). This candidate is the geometric-dynamics continuation of that line. It is eligible as a target, but its operations sit inside the family's toolset. The classification is technical, not substantial.
