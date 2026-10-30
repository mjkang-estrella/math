# Independent adversarial full proof gate, round 2: revised kinetic-window candidate

Date: 2026-10-14. Reviewer role: fresh proof sub-agent; no subagents, git, staging, or shared edits.

**Verdict: PASS for the full original I340 target**, relative to the stipulated truth of H at
`openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` and to the credited I340 continuity and transfer
lemmas, which I re-derived (§8). I found no mathematical gap that blocks the theorem as stated. Section 9
lists editorial and provenance corrections that do not block. These should be fixed before a manuscript gate.

This verdict covers proof validity only. It is not acceptance, a campaign count, a novelty or priority
certificate, a manuscript gate, a public submission, or a Lean claim. Earlier PASS/REPAIR/SUBSTANTIAL
verdicts were read for context only and were not used as proof.

## 0. Object under review and input binding

| Object | SHA-256 | Bytes / lines | Status here |
|---|---|---|---|
| `kinetic-repair-r1/candidate.md` (frozen revised candidate) | `c509dc89097d870aae16e4888b6e4481c45813ff92349436cbe15d99ed3b028c` | 47,522 / 881 | read in full, line by line |
| `kinetic-repair-r1/outputs.json` (manifest) | `9e820c6fe13e06fa1585ce164ecb98f43bcd1d55e0b03fc97e6d8fc5eb572f13` | 2,509 | read in full; all 16 listed hashes recomputed and matched |
| `kinetic-window-factory/candidate.md` (original Factory candidate) | `7c71805a0029bf5badcdbed37355775741e7aeb2513a3fba0a9a64b1f8fd2208` | 28,868 | read: header, §§1–2 (old W), and every changed hunk through the diff |
| `kinetic-repair-r1/candidate.diff` | `dc99d6ba64fb5e34834e7237d3387588c8f7cdea70ada4d14daa988663030045` | 54,798 | applied to a copy of the original and reproduces the revised bytes exactly |
| `kinetic-proof-r1/review.md` | `9333aca083f4d8428be9a45f71baf2f3a065da6443c59e99046bbe6ce1f2f2ab` | 21,817 | read in full |
| `kinetic-contribution-r1/review.md` | `f1ccd7fecb8e72b899f32730027b80e7fa198493f911e2cea92d19cdd26f033a` | 21,383 | verdict, statement, and objections 1–5 read; the primary-literature body was skimmed only |

On a sandbox copy, `consolidate.py` regenerates `c509dc89…` from the read-only original. The repair's
`checks/repair_checks.py` and `checks/adversarial_checks.py` were rerun on copies; both outputs are
byte-identical to the recorded JSON. Read extents, H authentication, and the concurrent deletion of the
shared `fetched-H` cache are recorded in `provenance.json` (§10).

## 1. The target is the original one, not a narrowed theorem

I compared candidate §0 with H01 `ass:kinetic` and `eq:grand-canonical` (lines 75–104) and with I340
`analysis.md` §1. Everything is preserved:

- the domain is R³×R³, the dynamics are deterministic elastic hard spheres, the diameter is ε, and μ=ε⁻²;
- the initial law is the exact grand-canonical exclusion/product-activity law, including N=0;
- f₀ is a smooth probability density with ‖f₀‖_{Bol,2β}+‖∇ₓf₀‖_{Bol,2β}<∞;
- there is a nonnegative classical Boltzmann solution with sup e^{2β|v|²}f bounded on the whole supplied [0,T];
- the observable is μ^{-1/2}(Σφ(zᵢ(t)) − EΣφ(zᵢ(t))), unsmoothed and exactly centered at every t, for every
  finite list of real C_c^∞ tests;
- the conclusion is J₁ convergence in D([0,T],R^m) to the continuous version of the Gaussian field of H
  `thm:main`, together with C-tightness.

The candidate introduces no equilibrium, torus, shortened interval, time smoothing, independent restart,
or narrowed test class. The extra uniform-topology weak-convergence claim has been removed. Uniform
convergence is stated only on a J₁ Skorokhod representation with a continuous limit (lines 59–62, 821–824).

## 2. Lemma W, attacked at each interface

W is the only genuinely new analytic input. I reconstructed it independently from H06
`lem:sharp-merger-coordinates` (lines 150–231), `eq:sharp-scaling`, `lem:sharp-factorials`, and
`lem:sharp-summability` (lines 257–436), plus H03 `def:dhm-history`.

### 2.1 Physical chart first: (W0) and Claim 1

H's chart gives three things:

- coordinates (v, X, y, (t_g, ω_g));
- the merger Jacobian ε²[(Δv)·ω]₊;
- the redundant-contact identity ∫δ(|r|−ε)[−u·r/ε]₊ dt = 1{incoming crossing in I}.

So a redundant contact contributes only an indicator. The candidate takes this Jacobian on the physical
chart only. It then dominates the physical integrand by F^{ext,Q}.

**Check of Claim 1.** For physical points I verified that the extended construction reproduces the
physical history, by induction on slots.

- **Mergers.** H's contact equation fixes the same group translation.
- **Redundant contacts.** The physical common segment interval starts at the later of the two current
  segment starts. That start is a preceding event or a birth/interface time, so the interval lies inside the
  candidate's forward ray, whose lower bound is the later preceding incident event, or −∞. A straight
  relative flight has at most one entering intersection with the sphere on the whole real line. The
  physical incoming root is therefore the ray's unique entering root.
- **Global order.** Physical event times are strictly increasing, so Q=1.

Every omitted factor (lifetimes, slabs on redundant times, acceptance, compatibility leftovers) is a
[0,1] weight. My control 2 tests this against actual event-driven 3D hard-sphere histories, including real
recollisions and an optional initial-link coordinate. Rebuilding from the extracted coordinates reproduced
every event time, normal, position, and velocity to 1e-9.

Minor presentation point: (W0) does not display the fresh-label coefficient ∏1/jᵢ!. §2.5 restores it
unchanged, so nothing is lost (§9 E1).

### 2.2 Prefix construction and the chronology repair

The round-1 defect was an extension without chronology: the 7/15 > 9/20 counterchart. The revised
construction has three rules.

- Translate the entire moved group at each merger. This preserves all earlier internal contacts and every y.
- Compute each redundant time as the entering root on the forward ray.
- Abort unless each new slot time is strictly greater than the previous global slot time (Q).

Every test depends only on the processed prefix and the next prescribed coordinates. After an abort, no
future trajectory is used. Successful branches are therefore genuine chronological, piecewise-affine
all-time paths. The counterchart is rejected at the last slot; I reproduced this from the rerun receipt.

**Adversarial finding (handled, not a gap).** An O-type redundant update leaves the pair's relative flight
unchanged. A following redundant slot on the same pair then recomputes exactly the same entering time.
This is a structural tie, not a null set in the extended coordinates. The candidate's "at or after" ray
bound passes it, but its strict Q test aborts it. Weight zero is correct: H06 lines 517–523 and H04
`lem:one-root-bridge` note that a fixed segment pair has at most one incoming contact, so the physical chart
carries no such branch. Exact ties are also shift invariant. My first float run exposed this tie as a
rounding artefact, and treating ties with a tolerance confirmed invariance. The candidate's sentence
"simultaneous … null sets have H's original convention" is slightly inaccurate for this case, but the strict
inequality already gives the right answer (§9 E2).

### 2.3 Shear covariance and measure preservation (Claims 2–3)

**Covariance.** Φ_θ maps (v,X,y,t,ω) to (v, X−θv_rep, y−θ(v_q−v_p), t+θ, ω). The construction never
references any fixed time: births, interfaces, and slabs enter only F's input factors and 𝒟. Its rules are
straight flight, the relative contact equation, elastic reflection, the forward-ray rule (lower bound an
event time or −∞), and the comparison with the previous global time. All of these commute with time
translation. The pre-first affine origins transform as A_p ↦ A_p − θv_p, which gives exactly the displayed
X and y shear. The candidate correctly avoids the false shortcut x_p(−θ) = A_p − θv_p for already-scattered
paths. Uniqueness of the forest solve then identifies the history of Φ_θξ with the time translate. It also
gives equality of the abort slot and its reason.

**Measure preservation.** Φ_θ is a shear with identity diagonal blocks and inverse Φ_{−θ}, so it preserves
Lebesgue × surface measure on the whole parameter space. No new Jacobian is claimed on nonphysical points.

**Exact control.** My control 1 implements the construction in 3D from the candidate text, independently
of the repair scripts. Over 4000 random charts (m ≤ 5, random forests, mergers, and redundant C/O slots;
773 successful branches with 217 redundant events; 3227 aborts of all four kinds), shears with
θ ∈ {−2.3, −0.4, 0.37, 1.9} gave:

- identical success/abort status, abort slot, and abort reason;
- event times shifted by exactly θ, with unchanged normals;
- segments equal to the time translates;
- conserved all-m-line energy E₀.

### 2.4 Averaging with Q retained, and the time volume

The identity I = Θ⁻¹∫₀^Θ∫F(Φ_θη)1{t_{a*}(η)+θ ∈ J} dη dθ needs only measure preservation and covariance of
t_{a*}.

**Pointwise bound.** Under the shear, the input factors take the form g(X+d_p, v_p), with d_p independent
of X. Fluxes, R, and Q are invariant. The link factor becomes 1{|y−θu| ≤ Rε}.

**X-integration.** One spatial L¹ norm and the remaining spatial suprema give B(v) ≤ C^m e^{−b₀E₀}, whatever
the displacements. On nonphysical branches the Gaussian argument is the independent coordinate v_p, as the
text states.

**θ-integration.** The single common θ lets each link indicator be replaced by membership in a containing
cylinder: |Cyl| ≤ πR²ε²Θ|u| + (4/3)πR³ε³. The θ-integral then gives |J|·1{t ∈ 𝒟−[0,Θ]1}.

**Minkowski volume.** For S = {s<t₁<…<t_a<s+τ}, the enlarged set is {ordered, span<τ, t₁>s−Θ, t_a<s+τ}.
At fixed gaps the admissible t₁-length is τ−u+Θ. Hence |S−[0,Θ]1| = τ^a/a! + Θτ^{a−1}/(a−1)!, which is a
factor 1+a at Θ=τ. Product containment gives at most (1+n)^L. My control 3 brackets the formula between
exact-rational lower and upper lattice sums for (a,Θ) = (1,1), (2,1), (2,1/2), (3,1).

### 2.5 Flux tree with Q retained, energy, factorials, scale, summability

**Flux tree.** At fixed (v,y,t,ω), all incoming velocities at a merger node are prefix data and are
identical for every candidate next pair. Redundant reflections between nodes are prefix functions. A
failure gives weight zero, so the child sum is at most Σ_{p<q}[(v_p−v_q)·ω]₊.

**Energy.** On extended branches all m lines exist at all times. C-updates conserve pair energy and O-updates
change nothing, so any subset of slab-i lines has energy at most E₀ = Σ|v_p|². That gives the bound
n_i^{3/2}√P on the bin E₀ ≤ P. This is H's argument (`eq:sharp-pair-flux`–`eq:sharp-pair-products`) with
RQ retained. RQ ≤ 1 is used only afterwards, in the time volume. The order of operations is correct. My
control 4 checks the pair-flux inequality on random data.

**Counting.** The fresh-label denominators and the C/O graph exploration are fixed before the change of
variables. The shear and the indicator enlargement introduce no new labelling, partition, or permutation.
Choosing the marked slot costs n+O_K(1). Redundant labels, crossing roots, and initial forests remain the
fixed polynomials of `lem:sharp-factorials`.

**Scale.** In a connected diagram, μ^{m−h}ε^{2(m−1−p)}·ε^{2p} = μ^{1−h}. Only the extra ε of H's ε^{3p} link
volume is lost. The cylinders' (τ|u|+ε)^p ≤ C_K(1+E₀)^{p/2} costs no power of μ.

**Gaussian budget and L.** b₀ = β/4 is fixed before K and the moment order. B₀ = sup_i‖g_i‖_{Bol,b₀} is
independent of L because, for ε ≤ ε₀(L), `prop:one-root` gives ‖g_i − f_{iτ}‖_{Bol,β_i} ≤ ε^{θ_i} ≤ 1 with
β_i ≥ 9β/20 > b₀, and H03 `lem:kinetic-envelopes` bounds f_t uniformly in Bol,β. I checked this point
specifically because an L-dependent B₀ would make the choice of L circular. After absorbing
(1+E₀)^{p/2} ≤ C_K e^{b₀E₀/4}, the energy-bin sum has a base depending only on b₀ (control 4 shows a log-base
of about 1.25 at b=0.3 over a ≤ 119). The normals contribute 4π per merger, Stirling contributes e², and
the C/O flags contribute 2. None of these depends on L or K. L is then chosen once so that CT/√L < 1,
which H05 `prop:cutoff` (every fixed L ≥ L₀) and H04 `thm:marked-expansion` permit. The Minkowski factor
(1+n)^L and the factor 1/τ are front polynomials or constants.

**Stirling.** n^{3a/2}/(a!n!) ≤ e^{2n}(1+n)^d n^{−n/2} with d = n−a; control 4 verifies it exactly in
log-gamma form for n < 160 and d ≤ 6. Combined with Σn_i log n_i ≥ n log(n/L), this gives (W2) and summability.

**Conclusion on W.** W holds uniformly in ε, J, and record or pulse times. It covers no-merger histories,
histories with initial links, and redundant C-atoms. It uses no cycle rate and no microscopic input.

## 3. Proposition I (increment cumulants)

**Pointwise majorant.** The only test is H's own scalar mark with two pulses (−φ at s, +φ at t). In the
absolute majorant, each autonomous C-cluster is refined by its complete accepted C-history (H04
`lem:one-root-bridge`, `lem:stopped-variation`), so the designated line's velocity changes only at displayed
C-atoms. H04 `lem:marked-regrouping` ("every record-bearing line continues to time zero") ensures no
designated segment is hidden in a resummed g. On the actual support the test is a function of the prescribed
history, and the majorant D_φδ + 2B·N_{(s,t]}(ℓ) is a positive function on the enlarged domain. The
majorant |y| ≤ D_φδ + 2B·N_{(s,t]}(ℓ) is therefore valid diagram by diagram.

**Cumulant formula.** It is H07 `eq:limit-factorial-ordinary` verbatim (lines 381–386), with block factor μ^{|π|}.

**Remainders and uniformity.** I checked against H04 `thm:marked-expansion`(ii)–(iii),
`eq:stopped-coarse-estimate`, `lem:diagram-labels`, and H06 lines 246–255:

- record values never enter acceptance or compatibility;
- pulse-to-segment placement costs a fixed polynomial, or a cutoff power in the coarse regime;
- the TV operator sees only the supremum of the test.

Hence one positive majorant covers all (s,t) ∈ [0,T]². The order of choices is correct:
A > P+2j+2, then K with C_{h,2}ε^{−C_*h−C_2+c_*K/2} ≤ ε^A, then M > P+2j+2 and D > 2K+M. After multiplication
by μ^h with h ≤ j, the tails are O(ε^{M−2}) and the coarse part is O(ε^{A−2j}). The variation term e^{−cΛ_L}
is super-polynomially small. No Gaussian weight is claimed for a generic remainder.

**Moments.** (κ₄ + 3κ₂²)/μ² ≤ C(δ/μ + δ²) + C_Pε^P. For E|S| ≤ μ∫|y| dc₁, note that c₁ = F₁ ≥ 0.

## 4. Lemma E′ (decorated final-partial-slab kernel), against the actual H text

I checked the following points individually.

1. **Exact one-slab identity.** H04 `eq:autonomous-observation` (lines 55–61) holds for any test H of the
   root histories Ψ|_S. The flag r_p = 1{velocity jumps in (a,b]} is a function of root p's final-slab
   history, and on every nonzero summand the full and juxtaposed autonomous root histories coincide. The
   Janossy/rooted-forest proof of `lem:one-slab-expansion` (lines 230–259) uses the output only through a
   delta pushforward. Spectators cancel pointwise and μ^j/j! survives, so the decorated identity holds as
   an identity of measures on (z, r).
2. **No flag hidden in an unmarked g.** Under the regrouping rule (lines 446–450), a top block with a single
   root, disjoint from H₋, would be resummed into g_i. The candidate instead keeps a decorated singleton
   g_i^{dec} = L_{i,1}^{dec}(g_{i−1}). This is legitimate because its output depends only on that block. For
   h ≥ 2, connectivity excludes such singletons from c_h. For h = 1, the decorated singleton's low-complexity
   molecules are slab-i diagrams with Bol-bounded g_{i−1} births, to which W applies. Its high-complexity
   part uses the coarse class with the top-root deficit ε^{−C_*h} of H03 `lem:dhm-dummies`(i), absorbed by
   K. Earlier slabs stay unmarked, and no record or line is added per collision.
3. **Component inversion.** Each flag is a root-history function of its own component, so
   `lem:diagram-labels` (fresh-label multinomial, lines 537–556) gives the decorated exponential formula, and
   finite inversion keeps exactly the connected decorated diagrams. Restricting to r = 1 is multiplicative,
   giving a genuine thinned point-process hierarchy.
4. **TV without lifting an endpoint estimate.** In Δ_i = R_i + L_iΔ_{i−1}, the decorated stopped kernel
   satisfies |R^{dec}(H)| ≤ ‖H‖_∞·𝓔_iF_{i−1}(1) by positivity and mass preservation of each history-level
   pushforward. The decorated L_i is again a kernel pushforward, so `eq:crude-operator` applies unchanged.
   Δ_{i−1} is the ordinary unmarked error. `lem:stopped-variation` is uniform for a partial final slab.
   The actual normalized decorated mass is at most μ^{−s}E(N)_s ≤ 1 (H02 `eq:initial-N-moments`).
5. **Jump flag ≤ count.** On refined molecules, r_p ≤ N_{(a,b]}(p); O-atoms change no velocity. W is applied
   after artificial dummy links are removed, as H04 `thm:marked-expansion`(iii) requires. All majorants are
   uniform in a, b, and the endpoint, and there are at most L slab indices.

E′ is therefore a valid consequence of H's finite kernels. It is not a reading of the additive-pulse theorem
and not an endpoint test. This closes contribution-review objection 4 at the proof level.

## 5. Proposition M (microscopic modulus at α = μ^{−3/2})

- **Pathwise bound.** Every pair with t−s ≤ 2α lies in [kα, (k+3)α] for k = ⌊s/α⌋. With right-continuous
  velocities, a particle with no jump in (kα, t] moves freely, and a jump costs 2B. Pieces split at at most
  one interface once 3α < τ. Half-open intervals assign endpoint collisions correctly.
- **Third moment.** Count³ = Count^{(3)} + 3Count^{(2)} + Count, with factorial moment–cumulant products.
  Each block is at most Cμα + C_Pε^P, and μα = μ^{−1/2} ≤ 1, so E Count³ ≤ C(μα + μ³ε^P). All diagonals are
  kept.
- **Union bound.** (T/α)·C(μα + μ³ε^P)/(η³μ^{3/2}) = Cη^{−3}(μ^{−1/2} + μ³ε^P), which tends to 0 for P > 6.
- **Free flight.** μ^{−1/2}·3αD_φN = 3D_φμ^{−1}(N/μ) → 0 in probability.
- **Centering.** Proposition I gives μ^{1/2}·2α·C + ε^P = O(μ^{−1}).

The excluded second-moment bound is correctly T/η², which does not vanish (§7 of the candidate).

## 6. Lemma C (chaining), §6 (assembly), and limit identification

**Lemma C.** With θ = 1/8 the three dyadic sums are as follows:

- C·Σ2^{−k/2}, made small by choosing k₀;
- μ^{−1}·(T/α)^{1/2} = Cμ^{−1/4};
- R·(T/α)^{3/2} ≤ CRα^{−2} = Cε^{P−6}.

The finest grid spacing lies in [α, 2α). Chaining plus 2w(Y, 2α) controls w(Y, T2^{−k₀−1}). With tight Y₀,
this is the C-tightness criterion of Jacod–Shiryaev VI.3.26. A vector of C-tight coordinates is C-tight.

**Transfer.** sup_t|S_t − Ŝ_t| ≤ 2‖φ‖_∞N·1_{E^ε}, H05 `prop:cutoff` (lines 14–29, η = 1/20), and H02
`eq:initial-N-moments` give exponent −1 + (21/20)(21/22) = 1/440. The J₁ distance is at most the sup
distance, and the modulus inequality transfers C-tightness. No fourth-moment bound for the true flow on
E^ε is used.

**Identification.** J₁ convergence to a continuous limit gives FDD convergence at every time. H01
`thm:main` (lines 143–167) gives joint FDD for C_c^∞ tests. FDDs determine a law on C, so the limit is
unique. Measurability: J₁ Borel sets are generated by coordinate evaluations, paths are càdlàg, and
expectations are càdlàg by dominated convergence with EN < ∞.

## 7. Required-repair checklist from round 1, re-verified on the new bytes

| Round-1 item | Location in the revised text | Independently re-verified |
|---|---|---|
| Chronology Q prefix-measurable, retained through averaging and the flux tree, dropped only for the time volume | §2.2 items 1–3; (W1-Q); §2.5 | yes, §§2.2–2.5 above and controls 1–2 |
| Affine pre-first origins, not x(−θ); input velocity may differ from the birth-time velocity on nonphysical branches | lines 211–221, 270–277, 332–334 | yes |
| Recursive whole-group translations preserve old contacts and y | line 233 | yes, control 1 |
| All m lines conserve E₀ | lines 259–268, 423–429 | yes, control 1 |
| Gaussian reserve before K/order; L chosen once; no literal "base unchanged" | §1.1; lines 456–467 | yes, including the L-independence of B₀ |
| Simultaneous cylinders and the μ^{1−h} scale | lines 362–376, 447–455 | yes |
| E′ decorated kernel, inversion, TV before pushforward, root losses, W after removing artificial links | §4.1 | yes, §4 above |
| Pulse uniformity with explicit A/K/M/D before μ^h | lines 551–578 | yes |
| Count³ diagonals; P > 6; interfaces; free flight; centering | §4.2 | yes |
| Uniform-topology overclaim removed | §0, §6 step 3 | yes |
| Second-moment arithmetic corrected to T/η² | line 851 | yes |
| Duplicate E′ removed | exactly one Lemma E′ (three textual mentions, one statement) | yes |

## 8. Credited paid inputs, re-derived rather than trusted

- **I340 §2 continuity.** The weak identity, Kolmogorov continuity of W(φ) via Gaussian fourth moments, and
  the Bochner/Tonelli indefinite integral are standard. The finite intersection of probability-one events
  preserves the covariance. Theorem F does not strictly need a pre-existing version: C-tightness plus
  FDD already yields a continuous process with ζ's FDD.
- **I340 §3 transfer.** Re-derived in §6 above.
- **Source theorems.** H `thm:main`, `prop:cutoff`, `prop:initial`, `thm:dhm-package`, and
  `thm:marked-expansion` are stipulated true per the user's instruction. Only the new deductions built on
  their stated interfaces and proofs were checked.

## 9. Remaining non-blocking corrections (editorial and provenance only)

None of these items changes a hypothesis, quantifier, exponent, or conclusion.

- **E1.** Display the fresh-label coefficient ∏1/jᵢ! (or state that C_K excludes it) in (W0); §2.5 already
  reinstates it.
- **E2.** In §2.2, state that a repeated root after an O-redundant update is a structural tie. Strict Q
  aborts it with weight zero, consistent with the physical chart, rather than handling it as a null set.
- **E3.** Resolve symbol clashes: B (‖φ‖_∞ versus partition blocks); b (endpoint versus block size); P
  (error power versus energy bin); η (coupling exponent 1/20 versus probability threshold); θ (shift versus
  chaining exponent 1/8).
- **E4.** §4.2 writes the error as C_Pμ^bε^P, which is weaker than (E′)'s C_Pε^P. It is harmless but
  should be aligned.
- **E5.** Make explicit in §1.1 that B₀'s L-independence holds for ε ≤ ε₀(L). This is what prevents the
  choice of L from being circular.
- **E6 (provenance, not mathematics).** The shared `kinetic-window-discovery/fetched-H/` cache that the
  repair's `sources.md`, `source-H-authentication.json`, and `validate.py` bind to was deleted by a
  concurrent process at about 21:12 during this review. As written, `validate.py` will no longer rerun.
  The bytes remain authenticated: before the deletion I matched all eleven files to the pinned
  `sources/preprints-tree.json` blob SHA-1s. Byte-identical copies from the pinned corpus also match the
  repair's recorded SHA-256 values (see `provenance.json`). The parent should rebind the paths.
- **E7.** The Factory-provenance byte-count erratum is confirmed: the actual file is 10,138 bytes with
  SHA-256 `a4c644fa…7fc7`, while the contribution `input-hashes.json` records 7,587. The ledger-path typo
  is noted as already documented. Neither is mathematical.

## 10. What was not done

- No upstream truth audit.
- No novelty or priority search. BGSS, DHM, and other primary papers were not reopened.
- No manuscript gate, Lean development, acceptance, or count.
- H06 lines 700–946 (traces and limit trees) and H05 beyond `prop:cutoff` were not re-read; Theorem F does
  not use them.
- `chronological-mergers.tex` and the later unintegrated discovery/checks files were not used as premises.
- The supporting controls in `checks/` are finite exact or float tests of the specific definitions. They
  are not a proof certificate.
