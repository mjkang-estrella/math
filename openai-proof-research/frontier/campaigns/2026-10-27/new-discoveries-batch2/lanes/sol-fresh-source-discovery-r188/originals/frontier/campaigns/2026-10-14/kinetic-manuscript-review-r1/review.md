# Independent manuscript gate — kinetic manuscript, round 1

**Verdict: PASS** for the full original theorem and its standalone presentation, relative to the stipulated truth of H at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. I found no mathematical gap. There are seven non-blocking corrections, listed in §7: attribution, standalone readability and notation. None of them reopens a proof claim or narrows the theorem.

This verdict covers the proof and the presentation only. It does not decide acceptance, novelty, priority or the campaign count, and it is not a Lean certificate. Earlier verdicts (proof-r1, proof-r2, contribution-r1, formal-review-r1) were read as context only and were not used as premises.

## 1. Scope reviewed

The object under review is the frozen package `kinetic-manuscript/`:

| File | Bytes | SHA256 |
|---|---|---|
| `main.tex` | 61392 | `969c35d11d8242c35117b77233d2612761ac56bc231f7365acd2172ad6f08d29` |
| `output/pdf/main.pdf` (19 pages) | 186051 | `c7f2c4533c58d15157445b4b19044c2c1b324ce7972ea106ea158e4601412565` |
| `outputs.json` (46 records) | 7046 | `cac9c988d0b4c839d47353a0ef54d1becf751b9fac89ea4978baf9b701329f66` |
| `references.tex` | 1898 | `3797dd451cf0f48db9bde382ae8ef363360d10257569af0105ab257e2e0d8e09` |

All three hashes the parent bound match. `input-authentication.json` in this directory lists the path, length and SHA256 of all 50 inputs I read or ran. I also checked the package's own manifests independently of its verifier: all 54 `inputs.json` records and all 46 `outputs.json` records match the bytes on disk. The brief's hashes also match: repaired candidate `c509dc89…`, proof-r2 `45e149cf…`, formal source `f4a419f9…`, formal manifest `e8596741…`, formal review `b46032b1…`, formal-review manifest `9fbb3323…`. The Factory `provenance.json` is 10138 bytes with SHA256 `a4c644fa…`, which confirms E7.

**Target check.** The theorem is the original target with nothing narrowed:

- the gas is the actual unsmoothed deterministic elastic hard-sphere gas on R³ₓ×R³ᵥ, with μ=ε⁻²;
- the initial law is the grand-canonical excluded-product law, including N=0 (`eq:law`, main.tex:100–105);
- the hypothesis is exactly H's `ass:kinetic`, compared word for word with H01:75–90;
- the time interval is the whole supplied [0,T], with exact microscopic centering (`eq:field`, :112–118);
- the conclusion holds for every finite list of real C_c^∞ tests;
- the conclusion is J1 convergence in D([0,T],R^d) plus C-tightness, with the limit being the continuous version of H's Gaussian field. The covariance `eq:covariance` was compared with H02 `eq:target-covariance`, and the drift and noise with H01 `eq:drift` and `eq:noise-form`.

The paper adds no equilibrium, torus, shortened interval, restart, smoothing or integrated observable. It explicitly declines any uniform-topology weak-convergence claim (:162–163 and :1196–1199).

## 2. Read extents

- **Manuscript, read in full.** `main.tex` lines 1–1260, `references.tex`, `README.md`, `provenance.md`, `editorial-response.md`, `publication-metadata.json`, `qa/visual-qa.json`, `qa/portability-check.json`, all three `checks/*.py` with their JSON receipts, `build.py`, `verify.py`, `verify_sources.py`, and the license files. `source-map.*` was used only through the verifier's label/line checks.
- **H, the pinned sources, authenticated by length, SHA256 and git-blob SHA1:**
  - H01: full (1–242).
  - H02: 30–95 (`prop:initial`) and 290–544 (`lem:target-moments`, `lem:target-propagator`, `prop:gaussian-target`).
  - H03: 1–75 and 195–397 (exponents, restarted rule, `lem:kinetic-envelopes`, `thm:dhm-package`, `lem:dhm-dummies`).
  - H04: full (1–781).
  - H05: 1–70 (`prop:cutoff`).
  - H06: 1–450 (conventions, `thm:sharp-cumulants`, forest counts, `lem:sharp-merger-coordinates`, scaling, `lem:sharp-factorials`, `lem:sharp-summability`).
  - H07: 30–45 and 351–409 (`eq:limit-factorial-ordinary`).
  - H08: full (1–69).
  - I grepped all ten files for any convention about collision instants (see N1).
- **Prior rounds, read in part.** proof-r1 review §1 and §5 (verdict and required repairs); formal-review-r1 review: verdict, independent checks and semantic findings; proof-r2 review: section structure only. Repaired candidate, contribution review and Factory files: hashes authenticated, not reread. The manuscript replaces them as the reviewed text.
- **Lean.** `kinetic-formal-v1/KineticSupport.lean`, read in full.

## 3. Load-bearing mathematics, checked against the actual text

**(1) Model, conventions and measurability.** The Bol norm, the collision rule v'=v−(w·ω)ω and v*'=v*+(w·ω)ω, B=[w·ω]₊, the drift, the noise ½∫B f f ΔφΔψ, and the initial covariance ∫f₀φψ with no subtraction all agree with H. Each fixed ε gives finite N almost surely with E N<∞; bounded-test sums are càdlàg; and dominated convergence gives càdlàg means (:1185–1189). This makes the centered vector a random element of the J1 space. The one inaccuracy is the attribution of the right-continuity convention to H (N1). It does not affect any fixed-time input, because a contact at a prescribed time is a null event.

**(2) Imported interfaces.** Each item was compared with the actual source statement.

| Manuscript | Source statement | Match |
|---|---|---|
| Auxiliary pasted dynamics, caps, restart only of prehistory | H03:12–45 | ✓ |
| `eq:N` | H02 `prop:initial`(i) | ✓ |
| `eq:ordinary` | H07:381–397, finite formal identity | ✓ |
| `eq:autonomous` | H04 `eq:autonomous-observation`, which is stated for every test of root **histories** | ✓ |
| `eq:kernel`, `eq:operator`, `eq:fresh` | H04:172–200 and :218–278 | ✓ |
| One-slab identity with R≤ℰF | H04 `lem:one-slab-expansion` | ✓ |
| TV error C_h e^{−cΛ_L}, coarse tail C ε^{−C_*h−C_m+c_*K/2}, fresh-label factorials | H04 `thm:marked-expansion`(ii)–(iii) and `eq:bounded-crossing-factorials` | ✓ |
| Dummy cost ε^{−q/81}, top-root deficit ε^{−C_*h} | H03 `lem:dhm-dummies` | ✓ |
| Links, forest counts, Jacobian, redundant identity, activity μ^{m−h} | H06:85–255 | ✓ |
| `eq:source-summability` | H06 `lem:sharp-summability` | ✓ |
| `eq:coupling` | H05 `prop:cutoff`, Γ≥Γ₀, L≥L₀, η=1/20 | ✓ |

The decorated output is **not** licensed by import alone. The paper proves it in Lemma 6.1, as follows:

- H04's one-slab proof acts only on the indicators κ, χ and a;
- spectators cancel through `eq:autonomous-partition` pointwise before integration, independently of the output map;
- `eq:autonomous-observation` already holds for history tests.

Replacing δ_{Ψ_𝒞|_S} by the decorated delta `eq:decorated-delta` therefore gives an identity of measures on the decorated space. The proof says exactly this (:895–907), and I verified it against H04:218–278.

**(3) Physical chart first, then the extension.**
- `eq:W0` (:482–486) is H06's change of variables on the physical chart, with the discrete weight 𝔞_G=𝔟_G∏1/j_i! displayed (E1).
- The extension (§4.2) uses:
  - pre-first affine origins A_p;
  - whole-group translations at mergers;
  - a determined entering root on the forward ray from the later preceding incident time;
  - a strict global prefix order Q.
- Lemma 4.2 is correct. Each relative straight flight has a unique entering root, and the physical root lies in the forward ray, so on the physical chart the computed root equals the physical one, Q=1, and F_G≤F_G^{ext,Q}.
- E2 is correct and explicit (:529–537). After an O-update, the next slot on the same pair returns the same root, and strict Q rejects it. This is a structural tie, not a null set.
- All-line energy `eq:all-energy` follows by induction over C/O updates. The birth input keeps its independent pre-first velocity argument, and the paper states this explicitly (:547–553).

**(4) Shear, averaging and summation.**

*Shear.*
- In Φ_θ `eq:shear`, A_p ↦ A_p−θv_p gives X↦X−θv_rep and y_l↦y_l−θ(v_q−v_p). The signs are right.
- The contact equation at t_g+θ is the old equation at t_g. The forward-ray root and Q comparisons shift together. For fixed v the map is a pure translation, so Lebesgue measure is preserved.
- Covariance does not use the false identity x_p(−θ)=A_p−θv_p.

*Averaging.*
- `eq:average` is valid by Tonelli.
- The X-integral bound 𝔅(v)≤C^m e^{−β_*E_0} holds uniformly in the displacements (L¹ for one input, L^∞ for the rest, Bol envelope B_0).
- The cylinder bound |Cyl|≤πR²ε²Θ|u|+(4π/3)R³ε³ is the exact volume of a segment plus a ball, and it keeps the ε³ term.
- There is one simultaneous shift and no shift per link.
- Q, R and the fluxes are shift-invariant and are kept in `eq:W1`.

*Simplex and flux.*
- I checked `eq:simplex` independently, both exactly and by Monte Carlo (§5).
- `eq:time-volume` follows with Θ=τ.
- The prefix flux sum is pointwise in (v,y,t,ω) and uses all-line energy to give ≤n_i^{3/2}√P. Q is dropped only afterwards.

*Counting and normalization.*
- The coefficients come from H06 `lem:sharp-factorials`; there is no new permutation factor.
- The marked slot costs n+O_K(1) choices.
- The scale is μ^{m−h}ε^{2(m−1−p)}ε^{2p}=μ^{1−h}.

*Energy budget and L.*
- The reserve is: (1+E_0)^{p/2}≤C e^{β_*E_0/4}, then e^{−3β_*E_0/4}≤e^{−β_*E_0/4}e^{−β_*P/4} on [P/2,P], then the energy sum C^{a+1}(1+a)^{a/2}.
- The Stirling step in `eq:before-stirling`, its inequality, and the bound (n/L)^n were checked. The final bound is `eq:W2`.
- L is not circular (E5). H03 gives β_i≥9β/20>β/4 and ‖g_i−f_{iτ}‖_{Bol,β_i}≤ε^{θ_i}, so B_0=1+sup_t‖f_t‖_{Bol,β} for ε≤ε_0(L). The atom base is therefore independent of L, K and the moment order. The extra factor (1+n)^{L+1} is polynomial and is summed after L is fixed.

**(5) Decorated final-slab flag (Lemma 6.1).**
- Output replacement is done in both the retained and the stopped kernels.
- The decorated singleton g^{dec}_{i,b} is kept separate from the ordinary g_i.
- Component factorization `eq:decorated-partition` gives finite inversion onto connected decorated diagrams.
- The variation recursion has an ordinary lower error. The positive stopped kernel has unchanged mass, so there is no TV lifting from endpoint measures.
- Root and dummy costs are absorbed by K.
- There is no line per collision. The flag is a final-output function.
- The bound r_p≤N_{(a,b]}(p) holds literally after refining by the complete accepted C history.
- Thinning to r=1 gives the factorial hierarchy of the jumping particles.

**(6) Moving pulses (Prop 5.1).**
- The record bound is |y|≤2M_φ, uniformly in s,t, and the positive kernels see only the supremum.
- The order of choices is explicit: A>q+2j+2, then K, then M>q+2j+2, then D>2K+M. The bounds μ^hε^A≤ε^{A−2j} and μ^h·ε^Mμ^{1−h}=ε^{M−2} were checked.
- No Gaussian weight is attached to any TV error.
- The fourth moment is E|ΔX̂|⁴=μ⁻²(κ₄+3κ₂²)≤C(δ²+δ/μ)+C_qε^q, and E|S|≤μc_1(|y|).

**(7) Microscopic modulus (Prop 7.1).**
- With α=μ^{−3/2}, at most two slab pieces, and half-open intervals with right-continuous paths, the pathwise bound `eq:micro-path` holds.
- `eq:count-diagonals` keeps every falling-factorial term.
- Every term is ≤C(μα+ε^q), using x=μα≤1.
- The union bound is (T/α)(μα+ε^q)/(η³μ^{3/2}) = η⁻³T(μ^{−1/2}+ε^q). This first form uses the actual remainder (E4). The weaker μ³ε^q form with q>6 is explicitly marked as a weakening, and the brief permits it.
- The free-flight term is 3D_φμ⁻¹(N/μ)→0. The centering term is ≤Cμ⁻¹+o(1).

**(8) Chaining and the endgame.**
- The dyadic chaining with ϑ=1/8 gives the three terms 2^{−k/2}, μ⁻¹(T/α)^{1/2}=μ^{−1/4} and R_ε(T/α)^{3/2}≤R_εα⁻², and R_εα⁻²=ε^{q−6}→0.
- C-tightness then follows from Jacod–Shiryaev VI.3.26; see the minor point N7.
- Gaussian continuity is a credited deduction and is sound.
- Exact-centering transfer uses p=22: −1+(21/20)(21/22)=1/440.
- The sup-norm transfer bounds the J1 distance.
- The limit is identified through C-tightness, H01 joint fdd convergence and continuous evaluation. The uniform statement is made only on a Skorokhod representation.

## 4. Earlier corrections and repairs, checked in the actual text

| Item | Status |
|---|---|
| E1: 𝔞_G=𝔟_G∏1/j_i! visible before `eq:W0` (:475–486) | ✓ |
| E2: structural O-tie rejected by strict Q, not called a null set (:529–537) | ✓ |
| E3: required symbol pairs separated: M_φ vs blocks V; d vs b (:1029); q vs P; η_0 vs η (:1172); θ vs ϑ (:1092) | ✓ (other overloads remain: N4) |
| E4: actual decorated remainder aligned, weakening explicit (:1024–1029, :1051–1059) | ✓ |
| E5: B_0 independent of L for ε≤ε_0(L); L chosen once before K (:411–415, :433–439) | ✓ |
| E6: the ten H files match the pin, by length, SHA256 and blob SHA1; the missing figure is unused | ✓ |
| E7: provenance is 10138 bytes, `a4c644fa…` | ✓ |
| proof-r1 repairs: chronology Q; uniform-topology claim removed; T/η² arithmetic (:1060–1061); fixed Gaussian budget; decorated kernel and component factorization | ✓ all present |

## 5. Supporting computations

**Package scripts.** All three were run on a disposable copy (`/tmp/kmr1-SVRW`), never on the frozen directory.
- `repair_checks` (14), `adversarial_checks` and `editorial_checks` (8) all pass, and their receipts are byte-identical to the frozen ones.
- `verify.py --project-root …` reports 160/160 structural checks, and its `validation.json` is byte-identical to the frozen one.
- `verify_sources.py` passes all 10 sources.
- What they actually test matches what they advertise: exact rational one-dimensional collinear charts, the counterchart 1/5, 2/5, 7/15>9/20, initial-link shear, the O-tie, the Count cubic polynomial, and exponent arithmetic. They are not a geometric or probabilistic certificate, and the paper does not claim they are (:1231–1236).

**Rebuild.** Tectonic was run on the copy. The PDF bytes differ only in metadata. The extracted text is identical, and all 19 renders are byte-identical to the frozen `qa/page-*.png`. So the frozen PDF is a faithful rendering of the frozen TeX.

**My own controls.** `independent_controls.py` and `.json` contain 12 checks; all pass.
- **3-D extended-chart controls:** the 3-D extended prefix chart with genuine normals: 40 random charts containing a determined redundant root, covering C/O mixes on pairs (0,1) and (1,2). In 160 sheared copies, success, times and all paths are translated in time, including an initial-link shear. All-line energy is conserved. 100 O-merger→redundant same-pair ties were all rejected by strict Q, including under shear.
- **Volume, Stirling and arithmetic checks:**
  - the exact simplex-enlargement formula for a≤8, plus a Monte Carlo check;
  - the Stirling step for n<160;
  - the base of the energy sum;
  - the scale, transfer and union exponents.
- My first run failed because of a sign error in **my own** merger translation. I fixed it, added an explicit contact-equation assertion, and reran. That failure did not involve the manuscript.

These are finite and numerical controls only.

**Formal coverage.** `KineticSupport.lean` contains exactly nine theorems:
- collision momentum and collision energy (the energy theorem assumes ⟨n,n⟩=1);
- four affine shift identities;
- a general pair-replacement result and the concrete simultaneous elastic all-line energy;
- `exponent_budget`.

The descriptions at main.tex:1238–1249 and in the README match this source exactly, including the explicit exclusions: entering-root covariance, Q, the Jacobian, history existence, the window and kernel bounds, and the path limit. I did not recompile it. The independent formal audit reports a fresh compilation (Lean 4.34.1) and four rejected mutations; I relied on its hashes only and treated it as support, not as a premise.

**PDF.** I rendered my own copies of all 19 pages at 80 dpi and inspected them on contact sheets, plus pages 1, 8, 10, 16 and 19 at full size. There is no clipping, overlap or broken equation, and the references render correctly. The TeX log has no warnings or bad boxes.

## 6. Proof coverage statement

The new deductions are Lemmas 4.1–4.4, Proposition 5.1, Lemma 6.1, Proposition 7.1, Lemma 8.1, and the proof of Theorem 1.2. I independently re-derived all of them on paper against the cited H statements, and they are valid. Everything imported is stipulated H truth, used exactly as stated, with one exception: the decorated-output extension, which the paper proves rather than imports, and which I verified against H04's proof structure.

The following support is finite only:
- the package controls;
- my controls;
- the Lean checks, which cover nine algebraic identities.

Nothing in the analytic or probabilistic argument is formalized, and neither this review nor the paper claims otherwise.

## 7. Non-blocking corrections (recommended before any public release)

- **N1 — attribution.** main.tex:107–108 says "right-continuous velocity convention of \cite{H}". H's pinned sources state only the almost-everywhere flow from DHM Prop 1.2 (H01:105–109). No convention for velocities at collision instants appears in H01–H08; H07:38 concerns record updates only. Suggested fix: "We adopt right-continuous velocities. At any fixed time a contact occurs with probability zero, so H's fixed-time statements do not depend on this choice."
- **N2 — standalone readability.** The shorthand H01–H08 is used from :212 onward but never defined. H statements are cited only by TeX labels in typewriter type. Suggested fix: add one sentence at :178–182 saying that "H0k" means Section k of [H] and that labels are those of the pinned source.
- **N3 — standalone readability.**
  - "project record I340" at :1125 and :1218 is opaque to an outside reader.
  - :1222–1229 report internal review verdicts (PASS, SUBSTANTIAL).
  - Suggested fix: describe I340 or drop it, and move the review-process statements to the package documentation for a public version.
- **N4 — notation.**
  - In §7, p is the particle index (:1013) and then the factorial-moment order "(Count(I))_p, p=1,2,3" (:1033–1036).
  - d is the number of tests in Theorem 1.2 (:150) and the block size in §7 (:1022). It is also used for d_p, d_i and d_K.
  - Bare M is the tail target (:380, :847), alongside M_i and M_φ.
  - Suggested fix: rename the moment order and block size, for example to k.
- **N5 — constant subscripts.** In `eq:factorials` (:312–313) the constant should also depend on the record bound, as in H04's C_{K,h,m,L}. The surrounding text fixes the list, so this is harmless.
- **N6 — wording.** :221–222 says "At pulses it has updates … at fixed pulses". The phrase is duplicated, and "fixed" conflicts with the moving pulses of §5. Suggested fix: "at prescribed pulse times".
- **N7 — C-tightness criterion.** Lemma 8.1, :1117–1120: Jacod–Shiryaev VI.3.26 (i) asks for tightness of sup_t|Y_t|. Suggested fix: add that sup|Y| ≤ |Y_0| + (T/u+1)·w(Y,u) gives this from initial tightness.

## 8. What was not done

- I did not audit H's truth; it is stipulated.
- I did not reopen BGSS or DHM, and I made no novelty or priority assessment.
- I did not compile Lean.
- I did not use subagents.
- I edited no frozen files, caches or shared indexes.
- Everything I wrote is in `kinetic-manuscript-review-r1/`, plus a disposable copy at `/tmp/kmr1-SVRW`.
