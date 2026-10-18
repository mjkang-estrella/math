# ANS263 independent full-scope proof review, round 1

Reviewer: independent PROOF sub-agent (Claude Opus 5.5), fresh context, 2026-10-17. Original prose CC BY 4.0, code MIT. No nested agents, staging, commits, uploads, or shared-ledger edits. Only `frontier/campaigns/2026-10-14/ans263-proof-r1/` was written. Third-party bodies were read in the author's private copies and are not reproduced here beyond short label/formula references.

Reviewed author inputs (immutable, anchored):

- `fresh-analytic-discovery-r32/manifest.json` SHA256 `0e1af1b06709a0585a8724e3a15e59e228a65f4c88ee363ef88e7aa482c73cf2`
- `263-working-proof.md` SHA256 `eef51e8d50cfaf29c971e346cc4f2957f40dfe033bda3de3d2543586879c7a48`
- `263-scope.md` SHA256 `03dd0d2eb2987fbc87bf130b7fe1978caa1755e7eb0286f616fc6ccfe13cf5fc`

## Verdict

**PROOF GATE: PASS, conditional on the stipulated pinned source theorems. No required objections.**

Relative to the actual stated contracts of the three family-263 companions at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, the working proof establishes the full unchanged target in `263-scope.md`:

> For every sequence m_l<Z_l with m_l→∞ and Z_l/m_l→∞, and every normalized form-domain state Ψ_l of ∧^{Z_l}L²(R³;C²) with q_{Z,Z}[Ψ_l]−E_{Z_l}(Z_l)=o(m_l^{7/3}), for every fixed a>0, m_l^{-1}∫_{|x|>a m_l^{-1/3}}ρ_l → (81π²/2)a^{-3}, and m_l^{1/3}R_{m_l}(Ψ_l) → (81π²/2)^{1/3}.

I re-derived every new deduction at full scope myself. That covers the form-domain IMS event cost, the price-zero lower baselines, the adaptive width and all §3 error margins, the cap, the spatial and initial nets, the integrated bad-band budget and its scaled sum, the R §4 transfer, annular uniform integrability, the neutral exterior tail, and the radius quantifiers. Nothing relies on an eigenstate identity, gap, spatial symmetry, prescribed rate, coupling of the rates, sequential limit, or bounded offset. Fermionic antisymmetry is preserved at every multiplier and slice.

The verdict covers mathematical validity only. It is not a substantial-contribution, novelty, formalization, manuscript, or acceptance verdict, and it does not count anything. Integrity and arithmetic checks are not proof.

## Required objections

None.

## Optional objections (precision and presentation; none affects validity)

1. **§3 (4)/(6), absorbing the patch errors into θ.** θ=C(u^{1−A}+r^{.02}) bounds more than the tilt. In (6) it must also absorb E's fixed patch errors, whose ratios to a^{-7} are a^{.1} (from √β), a^{2.8}, a^{.6} and a^{1.6}. This works because a≍r<1 gives a^{.1}≤Cr^{.02}. The text should say so explicitly. As written, θ looks like it only covers the tilted offset.
2. **§1 (1), both IMS summands.** Say explicitly that ∫(|∇√a|²+|∇√(1−a)|²)|Ψ|² is what gets bounded, and how in each regime. For a≤1/2, |∇√(1−a)|²≤|∇a|²/2 is dominated by the a-score bound. For a≥1/2, |∇√a|²≤|∇a|²/2 is dominated by the (1−a)-score bound. The complement score bound is F's `eq:obs-score-gradient` applied to A^c∈F_j. Also, √a is already Lipschitz by F's own argument, because √u·log^{5/2}(e/u) is bounded. No further approximation is needed for the IMS identity.
3. **§1, which E.** The baseline is E_Z:=inf_n E_Z(n)≤E_Z(Z), with E_0=0. Its use for gΨ (same sector), for every core slice (any n≤Z, vacuum included, e_X=0≥E), and for every inserted trial (any integer sector) should be stated in one place. The scope's δ is measured from E_Z(Z), and D=δ+C+1 converts it via E's `eq:neutral-offset`, valid for Z≥Z_0.
4. **§3, band-dependence of constants.** The comparison band runs up to 8Mr_j, with M=q² in §5, so beyond s. That replaces u=Dr_j^7 by C_M·u at band points (D a_y^7 ≤ (8M/L)^7 u). This only enlarges constants that depend on fixed parameters. The coefficient of √(u/p) in the cap may depend on M, but the cap constant C_cap may not, and doesn't. Stating this would make the universality of C_cap visible.
5. **§3, field-envelope cut condition.** Record that E's cut verifies D_z²/(a_z m_z)≤Ca^{1.6} using only m_z≥a_z^{-3}. It is therefore independent of the tilted offset, and F's `a:prop:screen-local` applies with offset D_A.
6. **§4 (12), mass and support conventions.** (a) Every packet has y-mass exactly one, which gives ∫μ_j=Z exactly. "Approximate mass 1+O(T(s))" in §2 refers to the center integral ∫K_z(y)dz. The proof should keep the two apart, since R's neutrality identity needs the exact one. (b) At j=0 the gain annulus [r_0,2r_0) also receives clamped packets with centers in |x|<r_0. The "comparable annulus" should be stated as [(1−c_1)r_0, 3r_0], which is still covered by `eq:annular-count`.
7. **§5, diagonal dependence.** Say explicitly that the deterministic slow diagonal q_l depends on the given sequence, through e_l, s_l, λ_l and the q-dependent thresholds, in the same way as R §3's stage choice. That is permitted because the theorem is proved one sequence at a time. "Imposes no rate" is correct but terse.
8. **Arithmetic coverage.** The author's `exponent_checks.py` doesn't cover the tilt powers in (4), the patch-error absorption (objection 1), or ℓ_j/t→0. This review's `checks/independent_arith.py` covers them. Both remain arithmetic diagnostics only.

## Independent re-derivations (summary of what was checked, not a restatement of the author's text)

Notation: u=Dr^7, s=m^{-1/3}, e=Ds^7→0, λ=Zs³→∞, T(r)=max(r^w,u^b), τ=t/a≍T.

**(1) Event cost for a form-domain state.** Let f=√a and g=√(1−a). IMS for −Δ/2 gives q[fΨ]=q[Ψ]−q[gΨ]+(1/8)∫|∇a|²/(a(1−a))|Ψ|². Then q[gΨ]≥E‖gΨ‖² and q[Ψ]≤E+D give p·q[Ψ_A]≤pE+D+loc, whatever the sign of E. In each regime the integrand is ≤Cℓ^{-2}·a·log^5(e/a), or ≤Cℓ^{-2}a when a≥1/2. Under Q=a|Ψ|²/p, Q(log(p/a)>t)≤e^{-t}, so E[a log^5(e/a)]≤Cp log^5(e/p) because the fifth moment of an exponentially dominated variable is bounded. Result: q[Ψ_A]≤E+D/p+Cℓ^{-2}log^5(e/p), uniform in n, arrays, Z and D. F's score bound is a property of the likelihood alone (F §5 l.171–205), and its only eigenstate use is at l.222, which this argument replaces. Confirmed.

**(2) Adaptive width.** d·T(d) has logarithmic slopes 1+w and 1+7b. Hence Lip(t)≤Cc_1T(s)→0, the minimum is c_1r_0T(r_0)>0, and the scale chain is b=a^{1.2} ≪ ℓ=r^{1.01} ≪ t=aT ≪ a, using T≥r^w for ℓ/t≤r^{.01−w} and T≤T(s)→0. The widths are deterministic for each system, so F's conditional versions, towers and Poisson identity hold unchanged. Confirmed.

**(3) Comparison at price zero.** On events with p≥u^A+r^{40}: D_A a^7≤C_M(u^{1−A}+r^{4.98}log^5) (4). The count event C_j holds with tilted count O(r^{-3}), giving μ_j≤Cr^{-6}T^{-3} and |∇μ_j|≤Cr^{-7}T^{-4}. In E's `eq:patch-error-budget` at λ=0, with δ'=D_A and P(0)=E, all lower baselines hold. The budget is ≤Ca^{-7}θ. Markov on G={D(σ−ρ)≤a^{-7}θ^{1/2}} plus F's Coulomb duality gives a relative error θ^{1/4}τ^{-5/2}. The sandwich gives r^{.01}T^{-4} and r^{.2}T^{-4}. The negative field gives θτ^{-3}+τ. The potential matching via F `lem:obs-transfer` gives τ^{1/5}, β^{1/5}, √β, θ^{1/2}τ^{-1/2}, τ² and (τ+√3β)^{1/5}. Each term vanishes uniformly in j after pairing θ's u-branch with T≥u^b and its r-branch with T≥r^w. Cap: the tail p≤Cu/(1+t)²+exp(−cr^{-.996}(1+t)^{2/5}) is correct (one of the two terms must exceed (1+t)/2), and subharmonic ball means give failure probability C(u+r^{40}) with universal C_cap. Net: mesh crT^5 gives density variation O(T) and field variation C(T²+T^5v_-). I derived this independently from the local potential (≤Cr^{-4}T^{-3}) and the positive-harmonic gradient estimate. With T^{-15} points the failure is ≤C(u^{A−15b}+r^{40−15w}). The high/low net transfer goes through exactly as in E, including arbitrarily negative v. Confirmed: α=1977/2000.

**(4) Initialization and budget.** Tilted offset at r_0: D_A r_0^7→0≤ε^7=Z^{7/3}r_0^7, so F's global density bound gives E[P_0|A]≤Cε^{6/5}Z/r_0. Also ‖∇P_0‖≤CZt_min^{-2}, and a net of spacing r_0T³ has T^{-9} points, giving α_0=A−9b. E∫p_0≤Z·P(G_0^c). Scaling: s³Zu_0^{α_0}=ε^{7α_0}e^{α_0}λ^{1−7α_0/3} and s³Zr_0^{η_0}=ε^{η_0}s^{η_0}λ^{1−η_0/3}. Both tend to 0 for arbitrary independent e→0 and λ→∞, since both λ-exponents are negative. Bad band: M_j≤E[N_ann|F_j] by unit y-mass, ‖N_ann‖_2≤Cr^{-3}(1+√u)≤Cr^{-3}, and Cauchy–Schwarz with the common F_j-event gives (12). The sum over r_j≤s is geometric with ratio 2^{-.45975}, so it gives s³·Σ≤C(e^{α/2}+s^{η/2}). Conditional averaging preserves E∫p, so E∫p_j is nondecreasing in j. E §4's open-cover maxima, branch checks, Jensen forgetting and initial branch don't involve the price, apart from H'→H. Confirmed.

**(5) Profile.** Inverting the comparison gives |σ−k(F_+)^{3/2}|≤q^{-8}|x|^{-6} on [a_s,q_s], exactly as in R §3. In R §4 the error mass enters only at R `prof:lower` l.200, as K*p_l≤2(∫p_l)/|x|, so replacing s³ by √B_s→0 is legitimate. Compactness, transfer and rigidity use exact neutrality ∫σ=λ, which holds here by unit y-mass. They also use the cap and the band, and both are supplied. Corollary `prof:uniform` gives uniformity over all retained data without measurable selection. Confirmed.

**(6) Expected masses, tail, radius.** ‖s³∫_{sA}μ_j‖_2≤C(1+√e) gives uniform integrability. R `tail:packets` holds with relative width O(T(s)), and the clamped packets lie within r_0(1+c_1)=o(s). Neutral Newton identity: r·avg_{S²}H(r·)=∫_{|x|>r}(1−r/|x|)ρ≥N_out(2r)/2. H(y)≤E J_y≤(E J_y)_+≤Cm_y/a_y by F `a:prop:screen-local` with trivial data, which holds for every δ-state. Hence N_out(2r)≤C(r^{-3}+√(Dr)) for r≤L, and s³N_out(2Rs)≤CR^{-3}+C√e R^{1/2}. Taking l→∞ first and then R→∞ gives tightness. The integral (4π/3)kA_*^{3/2}=81π²/2 checks exactly. N_out is continuous and nonincreasing, so the quantile bracketing with a_±→(81π²/2)^{1/3} proves the radius limit. Confirmed.

## Adversarial attempts and failed lines of attack (preserved)

- **Mixture counterexample.** I tried Ψ=√(1−η)Ψ_0+√ηΦ, with Φ of excess Δ carrying many outer electrons and ηΔ=o(m^{7/3}). The contribution to N_out(as) is ≤η·C(m+√(Δs))≤Cηm+C√(ηΔs)=o(m). This is consistent with (14). No counterexample.
- **Partial ionization.** Removing k=ε_l m electrons costs ≈(ε_l m)^{7/3}=o(m^{7/3}) but shifts N_out by o(m). Removing order m electrons costs order m^{7/3}, which the hypothesis excludes. No counterexample, and the o(m^{7/3}) hypothesis is the natural sharp form. I didn't try to prove sharpness.
- **D entering the patch budget unscaled.** At price zero the full unshifted offset D_A enters E's budget. In E it doesn't, because there only the shifted offset enters. This is the real reason the proof needs e→0 and the u^A threshold. I checked that u≤C_M e→0 on every band used (r≤s, band ≤8Ms), so this is handled. Not a gap.
- **Loss of the price beyond s.** E uses λ=s^{-4} for its exterior cutoff and to make H' negative beyond s. The author never runs the comparison past bands of size O_q(s), and replaces the exterior cutoff with the neutral tail (14). That tail needs no price and no eigen-equation. Not a gap.
- **Hidden eigenstate use.** I searched E §2–§4, F §3–§5 and R §2–§5 for eigen-equation or multiplier use. Found: E `eq:ground-multiplier` (event tilt and `lem:exterior-cutoff`), F `lem:obs-tilt` l.222, and E `lem:priced-rough` (minimizing sector). The proposal uses none of them. The localization identity (F `lem:loc-identity`, ψ∈Q_n), the screening contracts (F §4 l.11, "No eigenstate assumption"), the global density bound and the insertion lemma are all form-domain statements.
- **Lower baseline in variable sectors.** I checked that every comparison used only "energy ≥ inf over all sectors". This covers the vacuum slice (E_0=0) and the inserted trials, which have random integer particle number.
- **Union-bound loss.** If the source mesh r² were kept, the loss would be r^{-3}, against which u^A gives no power of r. The adaptive mesh rT^5 is what makes the union bound close. Verified.

## Exact reading limits

Read in full by this reviewer, in the author's private pinned copies (blob ids re-verified against the complete tree):

- E: `02-pricing.tex` (all 348 lines), `03-comparison.tex` (all 756), `04-barriers.tex` (all 352), `05-limit.tex` lines 1–60.
- R: `02-inputs.tex`, `03-scales.tex`, `04-profile.tex`, `05-tails.tex`, `06-interface.tex` (all), `01-introduction.tex` lines 1–80.
- F: `05-observations.tex` (all 438), `03-localization.tex` lines 145–300 (global density, localization identity), `04-screening.tex` lines 1–35 and 650–869 (local second moments, `a:prop:screen-local`, fixed-power corollary, oscillation, annular counts). Plus a grep of statement labels in F `02-foundations.tex`/`03-localization.tex`/`04-screening.tex`.
- Author packet: `263-working-proof.md`, `263-scope.md`, `263-scope-freeze.json`, `README.md`, `checkpoint.md`, `reading-and-limits.md`, `263-comparison-and-support.md`, `verify.py`, `exponent_checks.py`, `exponent-checks.json` (all in full).
- Parent: `ans263-parent/proof-review-brief.txt` (identical to the task brief) and `proof-dispatch.json` (task metadata).

Not read, so no claims rest on them: F §4 lines 36–649 (proofs of `screen-positive-field` and `screen-patch`), the F/E/R foundation proofs behind the cited labels (stipulated true), F §2 and its sector/multiplier proofs, F §§6–15 and the remainder of F §3, E §1, E §5 beyond line 60, E §6, R §1 beyond line 80, the Lean doc, both primary PDFs (Solovej 2003 and Lieb–Simon 1977), the parent's `author-side-reading.json` and event-lemma note (left unread to keep this review independent), and all campaign history. I did no novelty, priority, or literature assessment. That is the separate contribution gate.

## Checks shipped

- `checks/independent_arith.py`, plus its output `checks/independent-arith.json`. Exact rational margins for every exponent I re-derived, the TF constant 81π²/2, the Newton 1/2 factor, and four failing mutation controls. It refuses `-O`.
- `checks/author-packet-controls.md`: author verifier inspection and controls.
- `verify.py` + `manifest.json` (this directory): read-only exact-inventory verifier requiring the external manifest SHA256.

## Status

No acceptance, count, Lean, manuscript or publication claim. The parent alone decides acceptance and edits shared ledgers. The separate substantial-contribution gate is pending and outside this review.
