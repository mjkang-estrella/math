# ANS263 — independent contribution / eligibility review, round 1

Reviewer: Claude Opus 5.5 (fresh independent contribution/eligibility sub-agent). Original prose CC BY 4.0, original code MIT. No nested agents, staging, commits, uploads or shared-ledger edits. Only this directory was written. Third-party source and primary bodies are cited by label and line ranges and are not reproduced here.

Candidate: `frontier/campaigns/2026-10-14/fresh-analytic-discovery-r32`, external manifest SHA256 `0e1af1b06709a0585a8724e3a15e59e228a65f4c88ee363ef88e7aa482c73cf2`, working proof `eef51e8d…7a48`, scope `03dd0d2e…fcf5fc` (both rehashed at review time; see `input-binding.json`).

## Verdict

**TECHNICAL.** For this gate only, I assume the working proof is correct.

* **Eligible:** yes. The scope record is honest. It was recorded post-exploration and is not backdated. The target is the unchanged full target in the brief. No stronger frozen family-263 target was swapped out.
* **Duplicate:** no. Within my bounded reading, none of F, E, R, Lieb–Simon 1977 or Solovej 2003 states the full approximate-state, every-sequence joint outer-density/radius law for the correlated two-spin Schrödinger atom.
* **Blocked:** no. Correctness is assumed for this gate, and no missing source interface needed to *classify* the work was found.
* **Not substantial.** Every analytic estimate in steps (1)–(14) is an estimate already proved in F/E/R, or textbook IMS. Each is evaluated at retuned parameters. The integrated mechanism has four parts:
  * an adaptive probability threshold;
  * an adaptive master width;
  * a coarser spatial net that keeps the union bound independent of the dimension;
  * a Cauchy–Schwarz geometric barrier sum with the condition α>6/7.

  These are threshold/union-bound bookkeeping and parameter tuning, done to transfer E's comparison and barrier proof from eigenstates to approximate states. This is a robust transfer under the campaign's stated bar ("Routine transfers … do not count").

This verdict concerns contribution only. It says nothing for or against the mathematical correctness of the candidate. I did not read `ans263-proof-r1` or any proof-gate verdict.

## 1. Integrity controls performed (non-mathematical)

* I read the author `verify.py` and `exponent_checks.py` completely before running them. The verifier is read-only: it hashes files, recomputes git blobs, runs `pdftotext` to stdout, and runs the exponent checker. It requires `--anchor` and rejects a mismatched anchor before reading any dependent input.
* `python3 -B verify.py --anchor 0e1af1b0…cf2` returned **PASS_INTEGRITY_ONLY** (79 payload files, 17 directories, 55 pinned preprint blobs, 1 doc blob, 2 primary PDF bindings, scope unchanged, arithmetic replay PASS_NONPROOF). Output is in `checks/author-positive.out`.
* Wrong anchor `000…0` returned `FAIL: external anchor mismatch` with exit status 1. Output is in `checks/author-wrong-anchor.out`.
* I ran these without `-O`. The author packet was not modified. Its `private/` subtree is untracked in git, which is expected.
* Reviewer arithmetic: `checks/budget_alternatives.py` and its output (§4.5). It is exact rational arithmetic and not a proof.

## 2. Exact target compared

The comparison target is exactly the one in `263-scope.md` and the brief:
* every sequence m_l<Z_l with m_l→∞ and Z_l/m_l→∞;
* every normalized form-domain state in ∧^{Z_l}L²(R³;C²) with q[Ψ_l]−E_{Z_l}(Z_l)=o(m_l^{7/3});
* for each fixed a>0, convergence of the expected exterior mass m^{-1}∫_{|x|>a m^{-1/3}}ρ to (81π²/2)a^{-3}, and the radius consequence.

It has no eigenstate, gap, symmetry, rate-coupling or sequential substitute. It is an expected-density statement.

Relative to the strongest source statement, the target strengthens R in two ways:
* **(J) Joint scale.** R proves the asymptotic along "admissible" sequences s→0, Z≥Z_bar(s), Zs³→∞, where Z_bar(s) is an *unquantified* threshold (R §3 `scales:admissible`, R §6 "No rate of growth for Z_bar(s) is asserted"). It then deduces the iterated limits (R Thm 1.1). The candidate requires only Z/m→∞.
* **(A) Approximate states.** R, E and F's comparison/propagation all take *eigenstates* (sector ground states). The candidate takes arbitrary form-domain states with excess o(m^{7/3}).

## 3. Actual source contracts used in the comparison

These are the passages I read; exact limits are in `reading-and-limits.md`.

* **F (foundation).**
  * Lemma 5.1 (conditional versions and towers).
  * **Lemma 5.2** (`lem:obs-tilt`). The score-gradient bound `eq:obs-score-gradient`, |∇p_A| ≤ Cℓ^{-1}p_A log^{5/2}(e/p_A), holds for *every* Borel event A, using only the likelihood. The proof uses the eigenstate property only at the final step, through the multiplier identity.
  * **Lemma 5.3** (`lem:obs-transfer`). Its hypotheses and its conclusion `eq:obs-transfer` are stated in free parameters τ, β, ε_a. The paragraph after it explains that the fixed choices ε_a=a^{.01}, β=a^{.2}, τ≥ca^w are what *the applications* plug in.
  * Lemma 12.1 (`a:lem:tail-harmonic`) and **Lemma 12.2** (`a:lem:tail-deficit-upper`). Both hold for every normalized δ-state with n≤3Z and arbitrary δ. They give a spherical-average bound on the inner deficit.
  * §15 interfaces: arbitrary-offset versus fixed-power refined corollary; eigenstate event cost; the Z_*(D_0,s) fixed-offset comparison.
  * §11 statement (Z_*(D_0,s)).
* **E (energies).**
  * §2: `lem:local-field-input` and `lem:screening-inputs`, "No minimizing property is required in either estimate". Also `lem:priced-rough`, where the spherical average of B_{s/8} plus the trivial-data field bound at arbitrary offset gives Z−n ≤ C(s^{-3}+√(D_0 s)).
  * §3 (complete): event tilt (`lem:event-tilt`, the only eigenstate use), simultaneous inverse comparison, count event, cap, patch comparison with explicit `eq:patch-error-budget` in δ′, density recovery, two-posterior potential matching, spatial/height nets with mesh r² and r^{-3} points.
  * §4 (complete): initialization, open-cover maxima, conditional forgetting, and the total-error Cauchy–Schwarz sum using the pointwise L² density bound with r^{25} bad probability.
  * §5 (complete): slow diagonal, compactness by spherical means, barrier transfer, dilation rigidity.
  * The regime throughout is s→0, Zs³→∞ at arbitrary relative rate, with growing offset D_0≤Cs^{-7}.
* **R (radii).** I read §1–§6 completely. They cover:
  * the ground-state scope with Z≥Z_bar(s);
  * comparison failure Cr_j^{25} and barrier error s^{32}+s^γ imported from F §10–§11;
  * the slow diagonal (§3);
  * neutral compactness, barrier transfer and nonradial rigidity (§4);
  * expected annular mass via conditional Jensen and L² annular counts, packet sandwich, dyadic tightness at fixed D_0, and quantile bracketing (§5).

## 4. Operation-by-operation comparison

| Candidate step | Source operation it reuses | What actually changes | Classification |
|---|---|---|---|
| (1) Event cost D/p + Cℓ^{-2}log⁵(e/p) | F Lemma 5.2 score bound, applied to A and to A^c (the bound is event-agnostic). Tail integration is verbatim from F Lemma 5.2. IMS localization with f²+g²=1 is textbook. | Lower bound q[gψ] ≥ E_Z‖gψ‖² replaces the eigenstate multiplier identity. | Elementary. The parent's own note says so. |
| Threshold p ≥ u^A + r^{40}, tilted offset θ | E `lem:event-tilt` / count event: "condition if probability > r^{40}" | The threshold is u^A instead of a power of r, because the cost is now linear in 1/p. | Bookkeeping |
| (5)–(9) count event, cap, patch, density, negative field, potential matching | E §3 verbatim. E `eq:patch-error-budget` is already explicit in δ′. F `eq:obs-transfer` is already explicit in ε_a, τ, β. | δ′=D_A, ε_a≍θ^{1/2}, and τ≍T instead of a^w. Each candidate formula (7)–(9) is the source formula after substitution. | Parameter tuning |
| (2) Adaptive width T=max(r^w,(Dr^7)^b) | E master width t_x=c_1D·min(D,s)^w, with τ∈[a^w,s^w]. The source only needs τ→0 and τ≫(error)^{small}. | τ is enlarged so that the slowly vanishing θ still beats every negative power of τ. | Parameter tuning |
| Spatial net mesh rT^5, O(T^{-15}) points | E §3 net (mesh r², O(r^{-3}) points) with the same harmonic-gradient variation argument `eq:net-field-variation`. | The net count no longer depends on r, so the union bound survives failure probabilities u^A. | Union-bound bookkeeping |
| (3) α=A−15b>6/7 | Exponent arithmetic | — | Arithmetic |
| (11) Initialization with T^{-9} net and Z weight | E §4 initialization verbatim (global density bound, Hölder, net). | λ^{1−7α_0/3}→0 needs α_0>3/7. | Arithmetic |
| (12) Integrated annular L² mass × P(bad)^{1/2} | R §5 `tail:annular`: conditional Jensen of an annular count with L² count bound. E §4 total-error Cauchy–Schwarz. | Integrated instead of pointwise. **Not needed:** see §4.5. | Convenience |
| (13) Geometric sum, expected mass preserved by forgetting | E §4 "Total error", R §2 persistence remark | — | Routine |
| Slow diagonal and profile | R §3–§4 and E §5. The only edit is replacing s³ by B_s in K*P_s ≤ 2B_s/\|x\|. | — | Paid |
| (14) N_out(2r) ≤ C(r^{-3}+√(Dr)) | **E `lem:priced-rough`** and **F Lemma 12.2**. Both take the spherical average of the inner-screened field (Newton) and bound it by the arbitrary-offset conditional field. At n=Z this is (14) up to fixed radius ratios. | The radius and offset bookkeeping change. | Paid (duplicate operation) |
| Removing Z_bar(s), the joint scale (J) | E §3–§5 regime "Zs³→∞" at arbitrary rate and uniform thresholds, at price zero | — | Paid |
| Annular mass, packet sandwich, quantile bracketing | R §5 | Tightness by (14) instead of the dyadic sum with fixed D_0 | Paid |

### 4.1 Where approximate states actually differ from eigenstates

The only eigenstate input in E §3–§4 is `lem:event-tilt`, and through it the logarithmic cost in 1/p. Every other estimate is stated for arbitrary normalized δ-states. Examples:
* the screening and local-field bounds;
* the global L^{5/3} density bound;
* the core-slice lower bound e_X ≥ P(λ) (or E_Z at price zero);
* the insertion trial;
* the patch identity and its error budget;
* Coulomb duality;
* the two-posterior identity.

E and F state this explicitly (E §2 proof of `lem:screening-inputs`; F §15 "Arbitrary energy offsets").

So the full difference between the source proof and the candidate proof comes from one replaced inequality: log(e/p) becomes D/p + log(e/p). That replacement is elementary.

### 4.2 Is the downstream propagation a new mechanism?

This is the key question. With cost D/p, events of probability below u^A can no longer be conditioned on. Bad events can then only be shown to have probability about u^A, where u=Dr^7. That is not a power of r, and it may tend to zero arbitrarily slowly. Three source steps used polynomially small failure probabilities:

1. **The net union bound** (E: r^{-3} points × r^{42}). The candidate's response is the obvious one: make the net count independent of r by widening the packets.
   * The Lipschitz constants of μ_j and H_j scale like r^{-7}T^{-4} and r^{-4}·(rT)^{-1}·…, so mesh rT^5 gives relative variation O(T).
   * The count is then T^{-15} ≤ u^{-15b}, and this is charged to α.

   This is the standard "dimension-free net via adapted smoothing" trade-off. The source already leaves the width as a free parameter between a^w and s^w. F's transfer lemma and E's patch budget are already written in the free variables that need tuning.
2. **The barrier error sum** (E: Σ r^{-3-3w}r^{25/2}). The candidate replaces this with Σ r^{-3}u^{α/2} = D^{α/2}Σ r^{7α/2−3}. The sum is geometric and dominated by the top scale r~s, where s³·s^{-3}e^{α/2}→0. The requirement 7α/2>3 is a one-line exponent condition.
3. **The initialization** (E: n·P(G_0^c) ≤ Z r_0^{35}). Here s³Z·u_0^{α_0} = ε^{7α_0}e^{α_0}λ^{1−7α_0/3}, which needs α_0>3/7. This is arithmetic.

None of these steps introduces a new type of estimate, a new trial state, a new comparison principle, a new conditioning device or a new structural identity. They re-balance existing estimates. Retuning one long chain consistently is real work, and the author records it carefully and checks it adversarially. But under this campaign's bar it is the kind of robust transfer that previous TECHNICAL dispositions describe:
* OA057: the integrated construction was paid by source operations;
* O234: "standard net/concentration transfer";
* the fullCS review: "summable-weight threshold balls … reuse credited … operations".

### 4.3 Joint scale (J) is paid by E

E already runs the same observation, comparison, barrier and limit chain along s→0, Zs³→∞ at an *arbitrary* relative rate, with uniform thresholds and no Z_bar(s). R's Z_bar(s) comes only from importing F's fixed-offset Propositions 10.1/11.2 (F §15: "first fixes a finite D_0 … then takes s sufficiently small … It is not a uniform comparison"). Running E's chain at price zero for neutral ground states (bounded D) is a direct specialization: the price enters only as a constant subtraction. R §1 itself notes that the intermediate-scale compactness strategy is shared with E §5. So the joint-scale ground-state law is a routine E→R transfer, and (J) adds no contribution beyond (A).

### 4.4 The neutral tail (14) is a source operation

E `lem:priced-rough` computes the spherical mean of B_{s/8} on |x|=s as (Z−#{|x_i|<s/8})/s. It bounds this mean through the trivial-data conditional field at arbitrary offset. F Lemma 12.2 does the same for every δ-state with n≤3Z. With n=Z these give exactly the candidate's N_out ≲ r^{-3}+√(Dr), up to fixed radius ratios.

The candidate's identity "r·avg H = ∫_{|x|>r}(1−r/|x|)ρ" is the same Newton spherical average. R §4 (`prof:mean`) also uses it for compactness. Using it in place of R §5's dyadic tail sum, once D grows, is a correct choice, but it is an already-proved source operation.

Solovej 2003 (introduction, extracted lines 264–270) remarks that in the outermost region energy cannot control the density, so the variational equation must be used. That remark does not make (14) new here. F's correlated screening already controls the outer deficit for arbitrary δ-states at a √δ cost, and the candidate stays at the m^{-1/3} scale, where the o(m^{7/3}) excess is small compared with the local energy scale.

### 4.5 The integrated-annulus device is not necessary (reviewer check)

`checks/budget_alternatives.py` uses exact rationals. Suppose one instead uses E's pointwise route, ‖μ_j(y)‖₂ ≤ C(rT)^{-3}r^{-3}, with its packet-volume loss T^{-3} ≤ u^{-3b}. Then:
* the u-power is α/2−3b = 9879/20000;
* the r-exponent is 7(α/2−3b)−3 = 9153/20000 > 0;
* the r-branch is 3399979/200000 > 0.

So the source's own pointwise Cauchy–Schwarz also closes. The integrated device is a convenience, which the author already words as "unnecessarily".

The binding condition is α>6/7, with margin 1839/14000. A wrong control with A=0.85 fails (exponent −121/4000). A first-draft control at A=0.86 was *wrongly* expected to fail: it gives α=.8585>6/7. That error is retained as a note in the script.

### 4.6 Primary predecessors and formulations

* **Lieb–Simon 1977 §III.1–III.3** (extracted lines 1650–1700 and 1830–1900, OCR imperfect). This defines "approximate ground states" by excess o(Z^{7/3}) and proves bulk-scale density convergence via Rayleigh–Ritz plus concavity/differentiability of perturbed energies. It explicitly motivates the notion as covering degeneracy and "excited states where … not many electrons are excited". So the approximate-minimizer *formulation* is classical. The candidate's version is its natural transposition to the outer scale m^{-1/3} with excess o(m^{7/3}), the energy scale of that region (compare E's I_m≈a_TF m^{7/3}). The classical concavity route would need a perturbed-energy asymptotic at scale m^{-1/3}, which none of the sources supplies. The candidate does not use that route, so there is no duplicate. But a natural transposition of a classical robustness formulation does not count as a contribution by itself.
* **Solovej 2003** (extracted lines 190–285). Theorem 1.5 covers HF minimizers and lim inf/lim sup in Z. Its outer-region method uses the HF variational equation. This review relies only on the introductory remarks. The author's bounded reading of §§4–8 is recorded in their packet, and I did not re-read those sections.
* I located no primary result stating the candidate's full correlated approximate-state joint law. My search was bounded, so this is not a worldwide priority certificate.

## 5. Eligibility and history

* The scope was recorded after exploration and after the first draft, and this is disclosed (`263-scope.md`, `263-scope-freeze.json`). The only post-freeze edit is notational (e→exp(1)). The brief says the parent verified that this edit is invertible. No stronger previously frozen target was replaced.
* History screen (my own, bounded): grep over `frontier/` for outer radius, generalized ionization, Sommerfeld and Coulomb topics, excluding `ans263-proof-r1`, `private/` and the r32 packet. Hits fell into five groups:
  * catalogue copies (`CONTENTS.md`, catalogue surveys);
  * CM275/R032 (continuum Coulomb QMA membership, a different problem);
  * the I217–I223 Coulomb *transport cost* chain (different, classified TECHNICAL);
  * the r32 packet;
  * the ans263-parent briefs.

  I found no earlier developed family-263 approximate-state or radius chain. The author's `263-history-screen.json` agrees. Absence of hits is not exhaustive clearance.
* The target is not trivially implied by R or E and is not a relabeled old finding. It is eligible as a candidate. It fails only the substantiality bar.

## 6. Objections

### Required (for any retained record or downstream use of this candidate)

1. **R1 — Contribution gate not passed.** Classification is TECHNICAL. Neither count nor nominate the candidate as a substantial result on the basis of (1)–(14). Wording cannot repair this. A narrower slice of the same proof would not help either, because each isolated piece is more routine than the whole. Preserving the original target does not change the classification: the full target remains a technical robust transfer.
2. **R2 — Attribution of the neutral tail.** The packet's "Limits" paragraph lists "(14)" inside "The new part". The neutral spherical tail bound must be credited as the operation of E `lem:priced-rough` and F Lemma 12.2 / Lemma 12.1, specialized to n=Z, together with R §4's Newton identity. It must not be presented as a new interface.
3. **R3 — Attribution of the joint scale.** Removing R's Z_bar(s) for ground states must be credited to E's joint-regime comparison, barrier and limit operations (E §3–§5) at price zero. Any wording that presents the *joint* law itself as a contribution must be removed. The README's "joint outer-electron density/radius law" headline is acceptable as a description of the statement only.
4. **R4 — Credit the parametrized source lemmas.** Formulas (6) and (9) are literal substitutions into E `eq:patch-error-budget` (δ′=D_A) and F `eq:obs-transfer` (ε_a≍θ^{1/2}, τ≍T). Any retained exposition must cite them as such, not as altered estimates proved anew. The packet currently says "Here are the altered estimates in E §3 proving (3)".

### Optional

5. **O1.** §4 says the integrated L² mass device is "the important new budget". Per §4.5, the source pointwise route also closes with these exponents. Describe it as a convenience.
6. **O2.** Cite Lieb–Simon's approximate-ground-state definition and its "few excited electrons" motivation as the formulation antecedent. Note explicitly that the concavity route is unavailable here only because of a missing perturbed-energy asymptotic at the outer scale.
7. **O3.** Solovej's outermost-region remark (variational equation needed) is relevant context for why the scope stays at the energy-controlled m^{-1/3} scale. Recording it would pre-empt a reader's over-reading of the tail argument.
8. **O4.** Possible directions that might carry a genuinely new mechanism are not evaluated here. Examples: an empirical outer-count concentration law; a quantitative rate; the threshold regime q−E_Z ≍ m^{7/3} with an identified non-neutral-profile alternative. Listing them asserts neither feasibility nor novelty.

## 7. Approaches considered and rejected (preserved)

* **For SUBSTANTIAL.** The cost structure changes qualitatively, from log(1/p) to 1/p. This destroys the source's polynomially small failure probabilities, and all three downstream uses (net, barrier, initialization) have to be re-engineered. I rejected this argument because each re-engineering is a free-parameter retuning of an existing estimate, with no new estimate type (§4.2). The width freedom is already present in E's width and F's transfer lemma. The integrated device is not even necessary (§4.5).
* **For DUPLICATE.** R plus E already give the ground-state joint law (§4.3). Approximate states are a classical formulation (Lieb–Simon). I rejected DUPLICATE because no source or primary I read states the approximate-state outer-scale law. The E→R joint transfer and the approximate-state transfer, while routine, are still unwritten operations.
* **For INELIGIBLE.** The scope was frozen post-exploration. I rejected INELIGIBLE because the chronology is disclosed honestly and the target is unchanged from the brief.
* **For BLOCKED.** Correctness is assumed for this gate, and no source interface needed for classification is missing.
* **Calibration error.** The first wrong control (A=0.86) was miscomputed and corrected to A=0.85 (§4.5).

## 8. Limits

* This is a contribution and eligibility judgment only. It gives no proof verdict, no acceptance or count, no formal claim and no manuscript claim.
* Source truths are stipulated, not audited.
* My reading is bounded (`reading-and-limits.md`). In particular:
  * F §4 (screening), F §10 (atomic comparison), the remainder of F §11, E §6 and R's bibliography were not read.
  * Primary reading was limited to the cited extracted line ranges.
  * No external literature search was performed in this review. Primary coverage relies on the retained PDFs and the author's disclosed searches.
* There is no worldwide priority certificate.
