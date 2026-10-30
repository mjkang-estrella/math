# Kinetic-window contribution review, round 1

2026-10-14. Independent primary-literature contribution review of the frozen Factory candidate for the original I340 target. This file does not certify the proof, does not accept the candidate, and does not increment a count. Upstream theorem truth at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` is stipulated.

## Verdict

**SUBSTANTIAL, conditional on validity.**

The full-scope statement (F) below is a single frontier theorem. It is not identified with H `thm:main`, with Bodineau–Gallagher–Saint-Raymond–Simonella arXiv:2008.10403v2 Theorem 2, with arXiv:2201.04514v1 Theorem 1.3, or with Deng–Hani–Ma arXiv:2408.07818v3. The new content is the bridge in "Unpaid bridge": one collective time translation of a connected history, averaged so that a determined redundant contact still contributes a factor `|J|` at the sharp scale `μ^{1-h}`. Cumulant algebra, Markov union bounds, dyadic chaining, Gaussian continuity, and exact-centering transfer stay credited or routine once that factor is available.

Validity is open. The written argument for that bridge drops chronology and has not yet absorbed the shift-invariant event-order indicator required to keep the physical trajectories and the flux-tree bound. That repair is not frozen in this package. If the repair fails to return the same `μ^{1-h}|J|` gain on redundant contacts, (F) returns to I340's unpaid status. No diluted target is offered as a substitute.

## Statement under review

Primary text: `frontier/campaigns/2026-10-14/kinetic-window-factory/candidate.md`, SHA-256 `7c71805a0029bf5badcdbed37355775741e7aeb2513a3fba0a9a64b1f8fd2208`, 28868 bytes. On-disk bytes match the hash named in the review assignment and in the candidate's `provenance.json`.

Phase space is `R^3_x × R^3_v`, diameter `ε`, `μ = ε^{-2}`. The initial law is H `eq:grand-canonical`, including `N = 0`. H `ass:kinetic` holds: smooth probability `f_0` with finite `Bol,2β` norms of `f_0` and `∇_x f_0`, and a nonnegative classical Boltzmann solution with

    sup_{t≤T} sup_{x,v} e^{2β|v|^2} f_t < ∞

on the entire supplied interval `[0,T]`. The dynamics are deterministic elastic hard spheres. For real `φ ∈ C_c^∞(R^6)`,

    X^ε_t(φ) = μ^{-1/2} (Σ_i φ(z_i(t)) − E Σ_i φ(z_i(t))),

with exact microscopic centering at every `t`.

**(F).** For every finite list `φ_1,…,φ_m ∈ C_c^∞(R^6; R)`,

    (X^ε(φ_1), …, X^ε(φ_m)) ⇒ (ζ(φ_1), …, ζ(φ_m))

in `D([0,T], R^m)` with the `J_1` topology, where `ζ` is the continuous version of the centered Gaussian field of H `thm:main`. The sequence is C-tight.

The candidate also asserts uniform-topology convergence. That extra sentence is an objection below. Removing it leaves the `J_1` and C-tightness target unchanged.

## What a duplicate or a technical reduction had to preserve

A technical or duplicate verdict would require an explicit deduction of (F) from older theorems such that all of the following survive:

- whole space, grand-canonical exclusion, and exact microscopic centering;
- the entire supplied regular interval, with the given Gaussian `f_0` and classical solution, away from equilibrium;
- unsmoothed càdlàg paths, tested by arbitrary finite lists of real `C_c^∞` functions, in `J_1`, with C-tightness;
- a window factor on every marked C-atom of H's retained diagrams, including a redundant contact whose time is a function of earlier merger data.

Each source below drops at least one of these. The closest machines are recorded first.

### 1. BGSS short-time process theorem

Bodineau, Gallagher, Saint-Raymond, and Simonella, arXiv:2008.10403v2 (25 August 2022), HTML <https://arxiv.org/html/2008.10403v2>, and the local text extract `frontier/sources/i20_pde_kinetic_discovery/literature/bgss_v2.txt` (header `arXiv:2008.10403v2 [math.AP] 25 Aug 2022`). The published article is Annals of Mathematics 198 (2023), 1047–1201. Locators below are the v2 PDF section numbers in that extract. The HTML numbering used by I340 (25.2–25.4, Proposition 25.3, Lemmas 25.5–25.6) is the same material as PDF §§6.2.2–6.2.4 and Lemmas 6.2.5–6.2.6.

Theorem 2, page 6 of the extract: for grand-canonical hard spheres on the torus `T^d`, `d ≥ 2`, with `μ_ε = ε^{-(d-1)}` and initial density obeying the Gaussian bound (1.1.5), there exists `T ∼ C_0^{-1} β_0^{(d+1)/2}` such that the fluctuation field converges in law on `[0,T]` to the Gaussian process solving the fluctuating Boltzmann equation. The field (1.3.1) is centered by the exact microscopic first marginal. The abstract states that the results hold away from equilibrium and only for short times.

Tightness is Proposition 6.2.3 in `D([0,T_0], H^{-k})`: the modulus (6.2.4) and the norm bound (6.2.5). The proof uses the modified Garsia–Rodemich–Rumsey inequality, Proposition 6.2.4, with a microscopic cutoff `α_ε = μ_ε^{-7/3}`, the fourth-moment bound Lemma 6.2.6,

    E|ζ^ε_t(h) − ζ^ε_s(h)|^4 ≤ C ‖h‖_∞² (‖∇h‖_∞² + ‖h‖_∞²) (|t−s|² + |t−s|/μ_ε),

and Lemma 6.2.5, which shows that the probability of two collisions inside some window of length `2α_ε` tends to zero. Lemma 6.2.6 quotes point 3 of Theorem 10.

Theorem 10, point 3, pages 93–94: if the observable is bounded by a Lipschitz factor times the oscillation of one pseudo-particle on an interval of length `δ`, the scaled cumulant carries a factor `δ`. The proof of that factor is the last paragraph of §8.2, pages 107–108. It has three cases.

- No collision and no recollision of that pseudo-particle on `[t−δ, t]`: free flight gives `sup |z_i(t)−z_i(t')| ≤ δ|v_i|`.
- A collision on that interval: the creation time in the Duhamel formula is a free integration variable, and localizing it produces `δ`, with a combinatorial factor `m`.
- A recollision on that interval: the clustering time `Θ^{clust}` is a free integration variable in their parametrization, and localizing it to `[t−δ, t]` produces `δ`, with a combinatorial factor `n`.

Section 8.1 builds those clustering times by a spatial rigid motion of one sub-forest relative to another (`x̂_k`), so that a clustering recollision occurs. That coordinate is a free time of an inter-tree clustering event.

H's retained chart is different. `lem:sharp-merger-coordinates` in `06-sharp-asymptotics.tex`, lines 150–211, gives `(t,ω)` only for a dynamic merger. The same lemma states that a specified redundant contact has no free continuous parameter and no extra Jacobian: on a straight relative segment the incoming intersection time is determined, and the branch weight is the indicator that the intersection exists. I340's analysis, §6, records that restricting this determined time to a window does not replace the slab length `τ` by `δ`. BGSS point 3 does not supply that replacement inside H's chart.

The fourth-moment shape, the modified Garsia–Rodemich–Rumsey inequality, and the use of a microscopic cutoff are old arguments. They are credited in the candidate's Lemma C and in I340. They do not yield (F).

The introduction of v2, page 13, says the results could be established in whole space at the cost of geometric complications, and that equilibrium global-in-time convergence was then expected. The later equilibrium paper is the next item. Neither sentence is a proof of (F).

### 2. BGSS equilibrium process theorem

arXiv:2201.04514v1 (12 January 2022), HTML <https://arxiv.org/html/2201.04514v1>. Published as Annals of Probability 52 (2024), 217–295. Read the abstract, §§1.1–1.3, Theorems 1.1–1.3, and (1.19). The long-time moment iteration after Remark 1.3 was not read.

Theorem 1.1 recalls short-time equilibrium tightness in `D([0,T*], H^{-k})` on the torus. Section 1.3 and (1.19) extend the modulus to an arbitrary interval `[0,Θ]` by splitting into blocks of length `T*` and using invariance of the equilibrium measure: the long-interval probability is at most `(2Θ/T*)` times the short-interval probability. Theorem 1.3 then concludes convergence in law for all times, for hard spheres at equilibrium in a periodic box of dimension at least 3, to the stationary fluctuating Boltzmann equation. The initial law (1.4) is the grand-canonical equilibrium Maxwellian.

The invariant-measure union has no counterpart for the arbitrary nonequilibrium `f_0` in H `ass:kinetic`. Theorem 1.3 does not yield (F).

### 3. Deng–Hani–Ma

arXiv:2408.07818v3 (18 July 2025), abstract <https://arxiv.org/abs/2408.07818v3>, HTML <https://arxiv.org/html/2408.07818v3>, and the local extract `frontier/sources/i20_pde_kinetic_discovery/literature/dhm_v3.txt` (header `arXiv:2408.07818v3 [math.AP] 18 Jul 2025`). Read the abstract, Theorem 1's statement as located in the extract, and §1.4.3 in full. The 200-page derivation was not re-audited. H's imported package is stipulated.

Theorem 1 is the law of large numbers: the hard-sphere correlation functions track the Boltzmann solution on the full interval of existence of a regular solution. Section 1.4.3, "Fluctuations and large deviations," defines the scaled observable (1.28) and states that central-limit results exist for short times in their reference [8] and for long times at a global Maxwellian in [9, 11]. The next paragraph says that, with Theorem 1, those results are expected to extend off equilibrium on long intervals, using the layered description (1.20) and (1.22). That paragraph is a stated direction. It contains no process theorem and no contact-window estimate.

### 4. Pinned H and its catalogue companions

H, `preprints/Hard-sphere-fluctuations-on-the-regular-Boltzmann-lifespan-September-23-2026/build/sections/01-introduction.tex`, local copy SHA-256 `f64b5294…c2a8`. Lines 22–47 place BGSS process theorems on the periodic gas and state that H extends the time interval away from equilibrium for finite-dimensional laws. Lines 45–47 say the paper does not assert a path-space tightness theorem. `thm:main`, lines 143–168, is joint convergence of finitely many times and tests. The proof outline, lines 189–232, obtains the scale `μ^{1-h}`, one `ε²` per merger, an extra `ε` on initial links, disappearance of a first redundant contact on each finite tree, and the cutoff `P(discrepancy) = O(ε^{1+η})`. None of these is a shrinking-window bound on a determined redundant time.

`06-sharp-asymptotics.tex`, `lem:sharp-merger-coordinates`, is the coordinate obstruction quoted above. `lem:sharp-summability` integrates the absolute spatial translation with a displacement-independent birth bound. That spatial integral is an input to the candidate's averaging step. It is not the time-shift average.

`04-cluster-expansion.tex`, `lem:autonomous-partition`, equation `autonomous-observation`, lines 46–62: if `H` tests the root histories, the autonomous partition reproduces `H` on the full history. `lem:one-slab-expansion`, lines 217–258, gives the factorial identity and the total-variation domination `|R_s(H)| ≤ (E_s F)(|H|)` for every bounded measurable `H`, and states the same identity with prescribed records on root labels. Later, lines 415–418, a record is the sum of test values at pulses. The root-history sentence supports the candidate's reading that a bounded history observable is inside the one-slab identity. It does not by itself export the sharp diagram decomposition of §06, which is written for the pulse-record expansion, onto the jump indicator used in Lemma E′. That export remains a proof-gate reading. It is not a second novelty claim.

Catalogue item 364 in `sources/CONTENTS.md` pairs H with the stable-radial-potential law of large numbers. That companion derives `L^1` convergence of factorial marginals for a different force law. Catalogue item 363 is nonuniqueness for the Boltzmann equation. Quantum hard-sphere condensation titles in the same catalogue are different models. H's own introduction is the fluctuation statement in this pin. A line search of `CONTENTS.md` for process-convergence wording returned no kinetic path theorem.

### 5. Neighboring covariance and stochastic equations

Le Bihan, arXiv:2408.03597v2 (8 January 2026), local extract `lebihan.txt`. The abstract and Theorems 1 and 3, as located in that extract, prove convergence of the covariance of equilibrium fluctuations for truncated power-law potentials toward the linearized Boltzmann or Landau equation. The model is an equilibrium Gibbs state with a long-range potential. The extract was used for this identification. Its proof was not read. It does not yield (F).

Wu, arXiv:2609.06482v1 and arXiv:2610.08247v1, were opened at their abstracts and at selected theorem headings of the first PDF through the public arXiv text. They construct a Poissonian stochastic Boltzmann equation and a large-deviation rate on regular paths of that equation. The microscopic object is a stochastic collision process. These abstracts were used to exclude a deterministic hard-sphere path theorem from those titles. Their proofs were not read as contracts for (F).

The survey arXiv:2201.10149 and the physical-trajectory cluster paper arXiv:2205.04110 recover the short-time BGSS theory. The equilibrium hydrodynamic limit arXiv:2210.11812 starts from the equilibrium kinetic fluctuation theorem. They were identified from abstracts and from passages already quoted in the BGSS and DHM bibliographies. They were not re-read in full in this round. None states (F).

## Unpaid bridge

The following step is the part of the argument that the sources above do not contain. The substantiality verdict attaches to it, conditionally on the repair in objection 1.

**Collective time-shift averaging (Lemma W).** Fix a retained connected diagram in H's chronological chart. Translate every event of that connected history by the same `θ`, and average `θ ∈ [0,τ]`. The candidate's map is

    Φ_θ(v, X, y, t, ω) = (v, X − θ v_rep, (y_l − θ u_l)_l, t + θ 1, ω).

On formal histories the marked time, merger or redundant, increases by `θ`, and `(X,y,t)` is translated at fixed velocities, so the chart measure is preserved. Birth evaluations stay integrable by H's displacement-independent `L^1`/`L^∞` bound. Each initial-link ball is enlarged to a cylinder of radius `O(ε)` and length `O(τ|u_l|)`, which removes the link's extra `ε` and keeps the tree scale `μ^{1-h}` after a polynomial velocity weight is absorbed in the Gaussian. Each slab simplex `S` of side `τ` satisfies

    vol(S − [0,τ] 1) = (τ^a / a!) (1 + a),

so the time volume grows by a polynomial in the diagram size. H's fresh-label factorials and the summable majorant are then applied to this enlarged integrand. The output is

    Σ_D ∫ N_J(ℓ) d|D| ≤ C μ^{1-h} |J|,

uniformly in the pulse times, with `N_J` counting C-atoms in `J`, redundant contacts included.

BGSS §8.2 localizes a free creation time or a free clustering time. Lemma W manufactures the missing unit-speed coordinate by moving the whole history. That is the step I340 left unpaid. The cylinder and the Minkowski factor are the bookkeeping that makes the manufactured coordinate compatible with H's scaling. They are part of this one bridge.

Once that bound is granted, the rest of the candidate is a transfer into old tightness machinery.

- Proposition I inserts the window into H's two-pulse scalar mark and the factorial-to-ordinary cumulant identity, and concludes `|κ_j(S)| ≤ C μ δ + C_P ε^P` and the fourth-moment bound `C(δ² + δ/μ) + C_P ε^P`. The shape matches BGSS Lemma 6.2.6. The arbitrary power `ε^P` is what removes I340's qualitative `r_ε` under Garsia–Rodemich–Rumsey amplification. The algebra is routine from Lemma W and H's expansion.
- Proposition M and Lemma E′ turn the same window into a third-moment bound on the number of particles whose velocity jumps in an interval of length `O(μ^{-3/2})`, then use a union bound. The moment comparison is standard. Its only kinetic input beyond Lemma W is the root-history reading E′.
- Lemma C is dyadic chaining from the fourth-moment bound down to that microscopic scale, with Hölder exponent `θ = 1/8`. The criterion it invokes is Jacod–Shiryaev, Proposition VI.3.26, and Billingsley 1999, Theorem 7.3. This is the role already played by BGSS Proposition 6.2.4. The candidate's cutoff `μ^{-3/2}` and third-moment count are fitted to Lemma W. They are not a second discovery.
- The continuous version of `ζ` and the uniform transfer `‖X^ε − X̂^ε‖_∞ → 0` in probability, with `p = 22` and rate `ε^{1/440}`, are I340's parent lemmas. Identification of every C-tight subsequential limit by H `thm:main` is the usual finite-dimensional argument on `C([0,T])`.

## Objections

These objections are conditions on validity and on wording. They are not a proposal to replace (F) by a shorter-time, periodic, equilibrium, smoothed, or finite-dimensional statement.

1. **The core repair is not in the frozen text.** Lemma W enlarges the integrand to formal extended histories, drops lifetime, segment, and chronology constraints, and reruns H's flux-tree bound on that enlargement. The active proof review requires a shift-invariant global event-order indicator `Q` so that the shifted formal history remains the translate of the physical trajectory and the energy and flux-tree bounds still apply. `Q` is removed only after those bounds. That repair is not written in `candidate.md`. Until it is frozen and checked, Lemma W is a proposed bridge, and (F) is conditional. A repair that changes the measure, or that loses the root normalization `μ^{1-h}`, fails this gate.

2. **Uniform topology on nonseparable `D`.** The last sentence of (F) in the candidate says the convergence also holds for the uniform topology. `D([0,T], R^m)` with the uniform metric is nonseparable, and an unqualified weak-convergence statement in that metric should be removed or restricted to the continuous support of the limit. C-tightness in the Skorokhod `J_1` topology, with a continuous Gaussian limit, is the original target and is untouched by that qualification. Billingsley's theorem that `J_1` convergence to an almost surely continuous limit implies uniform convergence of paths may be stated as a consequence on that support. It is not a second theorem.

3. **Second-moment union arithmetic in the exclusion note.** `exclusions-and-failures.md`, item 11, says that at `α = μ^{-3/2}` a second-moment Markov bound produces `(T/α) μ α / (η² μ) = T μ^{1/2}/η²`, which diverges. The displayed product equals `T/η²`. That quantity stays a constant and does not tend to 0, so the second-moment union still fails to prove the microscopic modulus. Proposition M uses the third moment and gives a factor `μ^{-1/2}` after the same cancellation. The misstatement is confined to the exclusion note. It does not repair, and it does not break, the third-moment arithmetic in Proposition M.

4. **Lemma E′ remains a reading past the pulse-record package.** Equation `autonomous-observation` is stated for an arbitrary test of root histories, and the one-slab remainder is dominated for every bounded measurable test. The sharp cumulant decomposition used to price that test is written for pulse records and for the scalar mark `eq:limit-mark-update`. Exporting remainders (a)–(c) and the diagramwise bound `r ≤ N_J` to a final-slab jump indicator is exactly the flagged reading. The parent note that this reading is supportable is consistent with the autonomous-partition sentence. It is not a completed check of §06. If E′ is rejected and Lemma W stands, the candidate's own fallback is correct: Proposition I and the fourth-moment bound remain, and the missing piece is a microscopic modulus. That fallback is not (F).

5. **Pulse-time uniformity of the marked-expansion remainders** is inherited from I340 §6 and is not re-proved in the candidate (review point R2). It is part of the conditional proof, not an independent novelty gap.

## What this verdict does not award

- Finite-dimensional convergence, sharp cumulants, the cutoff, and exact centering on the regular lifespan are H.
- Short-time nonequilibrium process convergence on the torus, the fourth-moment increment, the modified Garsia–Rodemich–Rumsey inequality, and the free creation-time or clustering-time factor `δ` are BGSS, arXiv:2008.10403v2, Theorem 2, Proposition 6.2.3, Lemma 6.2.6, and Theorem 10 point 3.
- All-time equilibrium process convergence on the torus, patched by invariance, is BGSS, arXiv:2201.04514v1, Theorem 1.3 and (1.19).
- The long-time hard-sphere law of large numbers, and the description of fluctuations as a further direction, are Deng–Hani–Ma, arXiv:2408.07818v3, Theorem 1 and §1.4.3.
- Gaussian path continuity and the uniform exact-centering transfer are the I340 parent lemmas.
- The numerical shift checks in `checks/` are illustrations. They are not evidence for (F).
- No priority certificate is claimed. The search bounds are in `sources.md`.

## Acceptance

The candidate remains unaccepted. Counting (F) waits on a frozen repair of Lemma W that preserves the full-scope gain, on a proof gate for that repair and for E′, on the uniform-topology qualification, and on parent integration. A failure of the repair leaves the I340 window estimate and microscopic modulus unpaid.
