# I345 repaired argument: independent adversarial proof review, round 2

2026-10-14. Reviewer: Claude Opus 5.5, fresh review sub-agent. I started no child agents, made no git operations or index edits, and published nothing. Writes are confined to this directory.
Scope: **proof gate only.** This is not a novelty, contribution or count decision. The concurrently drafted manuscript files are excluded (main.tex, the new section files, and `viscous-appendix-typeset.tex`). The exception is the frozen `viscous-appendix.tex`, which I reviewed against I236.

## Verdict

**PASS for the repaired full research argument.** The pinned OpenAI theorems at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated, and the external classical results listed in §6 are used as citations. I found **no mathematical gap** and no unpaid operation. Every round-1 repair R1–R7 is resolved at the level of the argument. The carried I344 objection remains resolved, with no regression. The reading items U1–U3 are now closed at operation level, and U4 stays a classical citation.

The repaired argument is not one document. It is the union of four byte-bound texts:

- I345 `analysis.md` (f88c4ad3…), frozen;
- the parent repair addendum (d3ff16a1…), which overrides analysis §§1, 2.2 and 9 where they conflict;
- the compact-p lemma `p-gradient-uniformity/lemma.md` (06452273…), which replaces analysis §2.2;
- the frozen appendix `viscous-appendix.tex` (1685cc94…), which serves as the written I236 proof that §6 depends on.

The PASS is for this union. It is **not** a manuscript PASS. The presentation and bookkeeping items in §5 must be carried into the manuscript, and the manuscript needs its own gate.

The claim is exactly as stated in the original and is not narrowed. For each integer n≥2 there are α_n∈(0,1/3] and C_n<∞ such that, for **every finite p≥3**, every bounded weak solution u∈W^{1,p}_loc(B_1) of div(|Du|^{p−2}Du)=0 has its continuous representative in C^{1,α_n}(B_{1/2}), with

    ||Du||_{L∞(B_1/2)} + [Du]_{α_n;B_1/2} <= C_n osc_{B_1} u.

No sign, noncriticality, level-set or boundary hypothesis is imposed, and the constants do not depend on p. Nothing is claimed for 2<p<3 (R7).

## 1. Repair items R1–R7 and reading items U1–U4

| Item | Round-1 requirement | Round-2 disposition |
|---|---|---|
| **R1** | Compact-p Uhlenbeck uniformity: citation or written check | **Resolved.** lemma.md was audited operation by operation against the full Uhlenbeck text (§2 below). Its common constants, iteration normalization, critical-point branch and Caccioppoli/Moser route are all paid. Five non-gap presentation items: P7, P8. |
| **R2** | Quantified uniform Savin family | **Resolved.** Savin Prop. 4.1 is a sequence argument over varying F_k with one bound K, and r₀=r₀(δ,K,universal), which I read on the printed pages. The family satisfies H1, H2, H3′ and H4 with common constants. I make an explicit common radius ρ=min(1/8,b₀²/30), with λ=b₀²/6 and Λ=3N (§3.1). |
| **R3** | Correct the I236 dependency statement | **Resolved.** The addendum replaces "independently revalidated" with I236 §§1–6 plus the I239 PASS. The frozen appendix preserves every paid analytic step of I236 (§4). I did not re-assume I236 true: I re-derived each changed-PDE operation. |
| **R4** | Strengthened bad-scale selection as a lemma | **Resolved.** The addendum lemma is correct, including the case b(s_i)>0 and the separation s_i/λ_i^k→0 (§3.2). |
| **R5** | Quantified coarse-cylinder lemma | **Resolved.** The hypotheses, the ellipsoid geometry, the proportional Savin bound and the Taylor step check out. A is attached to the coarse slope, and (8.2)–(8.4) precede its application (§3.3). |
| **R6** | Immutable hashes | **Resolved for review.** The parent `input-hashes.json` (5c226da3…, at HEAD caf19c07) binds the d3ff16a1… addendum, the lemma and the I345 analysis. This review binds every examined input in [input-hashes.json](input-hashes.json). Two bookkeeping caveats remain: analysis.md is still **untracked** in git (P2), and the typeset appendix copy differs from the reviewed bytes (P3). |
| **R7** | Keep p≥3 | **Resolved.** The addendum disclaims 2<p<3. The lemma also needs s=(p−2)/2≥1/2, so that its Hölder exponent satisfies a≤s. |
| **U1** | Uhlenbeck pp. 5–8 not read | **Closed.** I read Sections 1–6 of the primary text in full. I inspected the rendered pp. 221, 232, 233, 234, 235 and 238, and verified the uniformity-critical operations myself. Moser's theorems themselves remain citations (§6). |
| **U2** | I239 audit not repeated | **Closed at operation level.** I independently re-derived each analytic operation of I236 §§2–6 while comparing it with the appendix (§4), and checked the identities with exact arithmetic. The pinned-source geometric lemmas remain stipulated. |
| **U3** | Savin pp. 5–13 not read | **Reduced.** Read: pp. 557–560 (hypotheses, Thm 1.1, Cor 1.2, Thm 1.3), pp. 569–570 (Cor 3.2, Cor 3.3) and pp. 571–573 (Prop. 4.1 proof). Not read: the Harnack proofs on pp. 561–568. Their statements declare universal constants, and that is all the uniformity needs. |
| **U4** | Weak/viscosity equivalence for Δ_p | **Unchanged: classical citation.** I checked only the operator-level fact that (P) and Δ_p give identical inequalities at every test jet, including Dφ=0 (p>2). |

**I344 carried objection: no regression.** Analysis §8.1 is unchanged by the repairs. I re-derived it again:

- common ball: |P−Q|≤2κ√λ/√Λ;
- common axial point at t=c₀κ^{−1/2}: |(P−Q)·N_P|=O(κ^{3/2}λ);
- quadratic angle term: ||P|−|Q||=O(κ²λ);
- equal-η dyadic chain over ≤2log₂ν+1 steps, with norms in [1/2,L+1].

Together these give (8.3), O(κ²λ+η(1+log ν)), and (8.4), |A′−A|/A≤Cε[κ²+κ(1+log ν)]/ν→0 once 4γ_i<1. R5 explicitly forbids swapping A and A′ before (8.2)–(8.4), so the repair keeps the required order.

## 2. R1: the compact-p lemma audited against Uhlenbeck

Uhlenbeck states that her constants depend on "K and p", where her p is our s=(p−2)/2: see (4.9) on p. 233 and (5.4) on p. 238. A uniformity argument over s∈[1/2,S] is therefore genuinely needed, and the lemma supplies one. I did **not** accept "bounded p implies bounded constants". I checked each of the points where a threshold or normalization is chosen.

1. **Structural constants (lemma (7)–(9)).** (1.3), (1.3)′ and (1.4) were read on the rendered p. 221. With ρ=Q^s and C=0, the left side of (1.3) is (1+2s)Q^s. For (1.4), divide by (x+y)^s. On [0,1], t^s is s-Hölder with constant 1 when s≤1 and S-Lipschitz when s≥1. Since a≤1/2≤s and |X−Y|≤1, this gives the constant S·max{1,S}, so K* is common. a=min{1/2,1/(m−2)} meets Uhlenbeck's a≤2/(n−2) (p. 230). Sampled check C1(8): the worst ratio is exactly 1, attained at y=0, s=S=1/2, so the constant is sharp.
2. **Sections 1–3.** In the scalar case the operator L_ω has coefficients I+2s ŵ⊗ŵ, with eigenvalues in [1,1+2s]⊂[1,P−1]. The constants of Moser (2.1)–(2.3) depend only on this and on fixed β. The lemma's identity |D√H_s|≤(S+1)Q^{s/2}|Dω| is correct: √H_s is a constant ≤1 times |ω|^{s+1}. Hence (10) follows with C₂(m,P). (3.1) and (3.3) contain no internal threshold choices. Their constants are finite products of K*, (S+1) and fixed Sobolev/cutoff factors (P8).
3. **Perturbation step (lemma §3).** This is the substantive point, and the lemma does not use the opaque c(p) of printed (4.6).
   - G is exactly the flux Taylor remainder divided by ρ(|w|²), matching the printed definition on p. 232.
   - DA_s is uniformly Lipschitz on the unit ball for q=2s≥1, because D²A_s=O(|v|^{q−1}) away from 0 and a segment meets 0 at most once. With |w|²≥1/4, this gives (11).
   - The inverse comparison (12) follows from DF_s(x)≥|x|^s I by integrating over the quarter of the segment nearest the larger endpoint: (F(v)−F(w))·(v−w)≥2^{−s−2}R^s|v−w|².
   - (4.8) holds with constant 4(P−1)², from the eigenvalue ratio of DA_s.
   - The Sobolev exponent 2(1+a)≤2m/(m−2) is fixed.
   - Chaining (4.3)→(11)→(12)→Sobolev→(4.8) gives ∫u²≤C(m,P)E^{1+a}, which is (13).
   - The one-step inequality (14) is the rescaled form of (4.9c)/(4.10c) on p. 234.
4. **Iteration normalization (15).** With t=min{1/8,1/(4C₃)} and E_i≤ε≤[t^{m+1}/(4C₃)]^{1/a}, we get C₃(t²+t^{−m}E_i^a)≤t/4+t/4. So E_{i+1}≤(t/2)E_i, and induction keeps E_i≤ε.
   - Drift: Σ|ω_{i+1}−ω_i|≤C₃√ε/(1−√(t/2))≤2C₃√ε≤1/8. Then |ω_i|²≥1/2−2·(1/8)=1/4, which closes the induction that (11)–(12) rely on.
   - Projecting references onto the unit ball does not increase |ω(x)−ω_i| or the drift, because ω takes values in that convex set.
   - The 1/(256C₃²) cap is implied by the third term, since a≤1/2. It is harmless but redundant (mutation M8).
   - Uhlenbeck's hypotheses 8²c₃²ε≤η and ε^a(η/2)^{−2p}<r^{n+2} (p. 234), and the proof choice rc₃=1/2 (p. 235), are the same two constraints in printed form.
5. **Decay factor (16)–(17).** The two inequalities printed on p. 238 are (1−c₅√λ)≥2^{−(p+1)/2} and λc₅2^{p+1}≤ε, with η=1/2. The common choice λ*=min{1/4, 1/(16C₅²), ε*/(2C₅2^{S+1})} gives 1−C₅√λ*≥3/4>2^{−3/4}≥2^{−(s+1)/2} for every s≥1/2, and it satisfies the second inequality uniformly. θ is fixed by √(1−λ*)=4^{−θ}, with θ<1/2.
   - The (5.1) constant C₅ is a finite product of K*, (S+1)², 2^{2S+2}, k₃, the fixed weak-Harnack constant c′(1) and Poincaré, with no internal choice (p. 238 text).
6. **Critical points.** The proof of (5.4) never linearizes at a zero gradient. Either M decreases geometrically, which gives the r^θ modulus and covers M→0, or the perturbation alternative applies at a reference of size ≥ half the current maximum. This is correct, and it is exactly the branch an original critical point falls into.
7. **Oscillation normalization (19)–(20).** Testing with η^p u, where 0≤u≤1, gives ∫η^p|Du|^p≤p^p∫|u|^p|Dη|^p≤(16P)^P|B₁|. Then (10) with r=1/32 gives sup_{B_{3/4}}|Du|^p≤A*, and p≥3 gives |Du|≤max{1,A*}^{1/3}. (18) on B(x,1/4), together with the Lipschitz bound for separated pairs, proves (R1).
   - n=2: a constant extension in x₃ is still weakly p-harmonic (Fubini) and has the same gradient norm. This is correct, and it is distinct from the affine lift.

**How R1 is used.** It is used in the bounded-p branch of analysis §4: λ_i≤C s_i^θ contradicts λ_i>(i/4)s_i^{γ_i} once γ_i<θ. Covering B_{3/4} by balls B(y,1/4)⊂B₁ only changes C by a fixed factor. It is also used for fixed-p affinity of an entire Lipschitz limit in §2.3, by scaling (18) or by Uhlenbeck (6.1).

## 3. Other repaired interfaces

### 3.1 R2: Savin family

Savin's H1 and H2 are imposed only for |p|,|z|≤δ, and he states "no information about F for |p|,|z|>δ" (p. 558). The max(B_d,0) switch, which happens only far from the zero jet, is therefore irrelevant.

The operators are F_d(X,q)=tr(M_d(q)X). Let ε, A, e, d∈[0,1], ξ=(a,b) with b≥b₀, and S_e=diag(I,√e).

- At q=0: Q(h,s)=|h_⊥|²+[b²x²−2αb√e xs+(1+eα²)s²]. The 2×2 block has determinant b² and trace ≤2, which gives b₀²/3≤M₀≤2. This was also re-elaborated in Lean (§7).
- For |q|≤1/8: |v−e_N|≤|q|, |B_d−1|≤2|q|+2|q|², ||S_eΠS_e||≤1, so ||M(q)−M(0)||≤4|q|+3|q|²<5|q|. Hence on |q|≤ρ:=min{1/8,b₀²/30}, B_d≥3/4 and spec M(q)⊂[b₀²/6,3].
- Savin's H2 then holds with λ=b₀²/6 and Λ=3N, since tr(MN)≤Λ' tr N≤NΛ'||N|| for N≥0.
- H4 holds with one K, because D²_{Xq}F=D_qM and D²_{qq}F=tr(D²_qM X) are bounded for |X|≤ρ.
- F(0,q)≡0, which is H3′.

Prop. 4.1 (pp. 571–573) states r₀=r₀(δ,K,universal) and argues by contradiction over a sequence F_k with ||D²F_k||≤K. Cor. 3.3 uses only universal c₀ and β (p. 570). So the threshold and the C^{2,α} bound are common to the family.

Thm. 1.3's conclusion is ||u||_{C^{2,α}(B_{1/2})}≤δ (p. 560), an absolute bound. The amplitude step Z=W/d, d=a₀/σ makes it proportional, ||D²W||≤(δ/σ)a₀. I checked the identity F₁(D²(dZ),D(dZ))=d·F_d(D²Z,DZ) exactly; mutation M3 confirms the check catches a dropped factor. The extension agrees with the true coefficient at every test, because B=|Π(√e q_x,1+eq_t)|²/A≥0 under the test constraint DU·ξ=1, which holds at upper and lower tests by the exact increment.

### 3.2 R4: strengthened bad-scale selection

b is nondecreasing, ≤1 and →0. "No power bound" makes sup f_i=∞ for f_i=b/s^{1/i}, so a_i, M_i>2i and s_i exist. f_i(s_i)>i forces b(s_i)>0 and s_i<i^{−i}. The two approximate-supremum choices give b(s_i)/4<λ_i≤b(s_i). Then 1/λ_i<4/(i s_i^{γ_i}) gives s_i/λ_i^k<(4/i)^k s_i^{1−kγ_i}→0.

The fixed-multiple goodness in analysis §4 uses (2M)^{γ_i}<4 for large i, which gives β<32λ_i. The growing-scale goodness in §8 uses β≤8λ_i(4R_i)^{γ_i}<η_i (since 8<K₀=64) at every radius ≤H_i, given 4R_is_i≤1/8. A log-space run on b=1/(1+log(1/s)), which has no power bound, reproduces the construction (C5); this is evidence only.

### 3.3 R5: coarse-cylinder lemma and its use in §8

- Ellipsoid z+ℓT_e(B₁), ℓ=(H/4)√(η/e): its transverse half-width is ℓ√e=H√η/4 and its axial half-width ℓ≤H/4 when η≤e.
- ||W||≤ηH/(cℓe)=(4/c)√(η/e)≤8√d*.
- ||T_eD²UT_e||=(ce/ℓ)||D²W||≤16(δ/σ)e/H.
- P_new=c(√e W_x,1+eW_t) has axial part ≥c/2, and |T_e^{−1}N_{P_new}|≤2(1+o(1)).
- For λ≤e, |T_e^{−1}h|≤C′r, so for r≤k*ℓ every segment stays in the half-ellipsoid.
- Taylor's formula gives the error Ce r²/H.

In §8.2:

- η_i/e′_i≍κ_i/ν_i→0;
- ℓ_i/r_i≍ν_i^{3/2}√κ_i/4→∞;
- λ_i≤e′_i once ν_i≥2;
- error/(λ_ir_i)≍C/ν_i→0;
- H_i=ν_i²r_i≤λ_i^{−2}s_iD(z_i)=o(D(z_i)).

The actual nonzero slope DU_i(z_i) makes λ_i good, which contradicts its selection. All scalings were checked exactly (C4).

## 4. R3: the frozen appendix compared with I236 and I239

`viscous-appendix.tex` (1685cc94…) was compared step by step with I236 `analytic-attempt.md` §§1–6 (a30077ca…) and the I239 analytic check. For each paid step I re-derived the operation rather than relying on the earlier PASS.

| Paid I236 step | Appendix | Re-derived here |
|---|---|---|
| Statement: m≥1, 0<τ<∞, C₀≥0, V∈C, FIT ⇒ affine; no regularity added | Thm `thm:viscous` | identical quantifiers |
| Lemma 2.1, spatial semiconcavity + PDE ⇒ local Lipschitz: supporting slope bound L; K′=K+1 gives boundary gap r²/2; common s with ω(s)<r²/8; lifted test with zero mixed Hessian ⇒ ψ″≥−C=−K′((L+K′r)²+τm); convexity; secant slopes; reverse inequality from base time t | `lem:time-lipschitz`, all steps present | G_τ of the lifted test checked exactly (C3) |
| §3 cone infimum v_L: u≤v_L≤v; (L−L₀)|h|≤v−u; minimizers in B_{r/2}; fixed-shift supersolution pullback; L-Lipschitz; recovery v_L(z)=u(z)⇒h=0⇒v(z)=u(z) | present; (3.2) merged into one displayed inequality (valid since v≥u) | yes |
| §4 flux a=e^{H/τ}(p,1), Da=e^{H/τ}A_τ/τ, bounds λ_M, Λ_M | present, same constants | finite differences; λ₀ bound sampled (C3) |
| Lemma 4.1, viscosity ⇒ weak for locally Lipschitz f: sup-convolution subsolution; Alexandrov inequality; mollification lower bound −(m+1)Λ_M/ε; a.e. Hessian convergence (JJ Remark 3.3); one-sided Fatou; ε→0 via |b_ε−Df(z)|²/2=o(1) and Df^ε=b_ε; inf-convolution for supersolutions | present, every operation | yes; gradient identity from the quadratic touching from below |
| §5 linearized B, div(BDd)≤0; Lax–Milgram w; w≥0; (w−d)^+ test ⇒ 0≤w≤d; solution Harnack ⇒ w≡0; trace ⇒ d=0 on spheres; open/closed contact set | `thm:contact`, all steps present | yes |
| §6.1 C₀=0; frame (6.1) with G_τ[U]=RG_τ[V] and fit map (p,a)→(p−p₀,a−a₀); affine-slice alternative (second difference, P affine, log growth ⇒ b=0, ψ″=0); reflection −V(x,−t) | present | frame, fit map and reflection checked exactly (C3) |
| §6.2 κ finite and positive; normalized limit; first-moment UI keeps mean 0; Jensen sandwich κ²s/2; equality forces unit second moment; R=1/κ frame and time shift; (6.4); D_xxW≤I/t; synchronized-time theorem of sums with order of limits; variance affine along ((q_j),1) | present, including the order of limits | envelope scaling, weighted mean of q_j and affine variance checked exactly (C3) |
| §6.3 global maximizer y* ⇒ C_tV(y*,t)=V(y*,t), contradicting gap κ²t/2 | present | yes |

Not carried over, and **not needed** by I345: I236's drift remark (end of §6.3) and the §7 failed-shortcut examples. **No paid analytic step is missing.** The appendix adds one citation for the exponential structure (SanchezMorgado). The direct differentiation is given in full, so the citation carries no weight. Presentation deltas P4–P6 are listed in §5.

**How the dependency is used.** I345 §6 applies the appendix theorem at τ=ν>0 in two places:

- to V on R^n×R (m=n) when a=0;
- to the projected W on e^⊥×R (m=n−1≥1) when a≠0, after the exact same-C₀ fit projection (6.2), re-derived in round 1.

At ν=0 it uses the pinned `thm:liouville` instead. Both interfaces match the theorem's quantifiers exactly.

## 5. Actual gaps versus presentation

**Actual mathematical gaps: none.** I found no counterexample and no unpaid operation. In particular I looked for:

- a hidden s-dependent threshold in Uhlenbeck §§4–5;
- a jet radius or ellipticity in the Savin family that degenerates at e=0, A=0, d=0 or ε=0;
- loss of the coarse/base A ordering;
- a dimension-two failure: the n=2 constant extension in R1, and Harnack in total dimension 2 for the m=1 appendix case;
- an appendix step weaker than its I236 original.

None materialized.

**Presentation and bookkeeping items.** None of these affects correctness, but each must be fixed or carried into the manuscript.

- **P1 (consolidation).** The text of record is split across four files, and the frozen analysis.md still says "independently revalidated" (§§1, 9) and carries the compressed §2.2. The manuscript must do four things:
  - replace §2.2 with lemma.md;
  - replace §9 with the appendix plus the addendum's dependency statement;
  - state R2 as a lemma with the explicit constants ρ=min{1/8,b₀²/30}, λ=b₀²/6 and Λ=3N (the addendum says only "for example");
  - state R4 and R5 as lemmas.
- **P2 (immutability).** At HEAD caf19c07, `frontier/experiments/i345_lifted_p_gradient_research/analysis.md` is **still untracked**, since `git show HEAD:` returns the empty hash. Acceptance therefore rests on SHA binding alone, and the bytes should be committed or archived.
- **P3 (typeset copy).** `p-gradient-manuscript/viscous-appendix-typeset.tex` (1daca7fa…) differs from the reviewed `viscous-appendix.tex` by an 8-line diff. Per scope I did not read it. Any build must either use the reviewed bytes or have that delta reviewed.
- **P4 (appendix, limit class).** State explicitly that locally uniform limits of normalized frames keep **both** G_τ=0 and the all-center, all-radius FIT, with coefficients chosen by subsequence per center and radius. I236 §6.2 and I239 §6 state this; the appendix says only "locally compact family" and "PDE passes to limits".
- **P5 (appendix, dimension two).** For m=1, which occurs in I345 when n=2 and a≠0, the linearized equation lives in dimension 2. Either cite a Harnack theorem valid for n=2, or add the diag(B,1) constant-lift remark from I239 §5 and I345 §9.1.
- **P6 (appendix, hypotheses for W).** Spell out that D²_xxW≤I/t gives the locally uniform constant 1/t_min on compact positive-time cylinders, as I236 §2 does.
- **P7 (R1 lemma, reference update).** (14) does not specify the next reference vector. Printed (4.9) uses the B(1/2)-average of ω̃ (p. 234), whose O(r²) bound as printed fits better with ω̃(0) or the B(t)-average. Either standard choice, projected to the unit ball, gives (14) with the lemma's constants. Specify one.
- **P8 (R1 lemma, constants by inspection).** For Sections 2–3 and (5.1), the lemma asserts common constants after inspection rather than operation by operation. This is acceptable because those steps contain no threshold choices, but a manuscript should list the factors: K*, (S+1)², 2^{2S+2}, Moser c(β) for fixed β, c′(1), Poincaré and Sobolev.

## 6. External results that remain citations (not re-audited)

- **Stipulated pinned theorems:** `thm:main`, `lem:linear-lift`, `thm:liouville`, `lem:bad-scales`, `lem:cylinder-comparison`, the geometric part of `prop:nonaffine-limit`, gradient extraction, the source-04 fit compactness and growth, the source-05 barycentric envelope (duality, finite attainment, concave-envelope identity), and the theorem of sums.
- **Kotschwar–Ni Thm 1.1:** the statement and constants were read in round 1; the proof is not re-read.
- **Weak/viscosity equivalence for Δ_p** (Juutinen–Lindqvist–Manfredi; Julin–Juutinen), and standard viscosity stability under uniform convergence (U4).
- **Uhlenbeck (1977):** Moser's Theorems (2.1) and (2.2) themselves, and the source steps (2.4), (2.5), (3.1), (3.3), (4.2) and (4.12)–(4.15). These were read; their constants are structural and they contain no threshold choices. Also Bernstein (6.1).
- **Savin (2007):** Thm 1.1, Cor 1.2, Lemmas 2.1–2.3, Prop 3.1 and Cor 3.2 (proofs on pp. 561–568 not read), and the "follows easily" deduction of Thm 1.3 from Prop 4.1.
- **Classical analysis:** linear constant-coefficient interior estimates; Sobolev and Poincaré; De Giorgi–Nash–Moser Hölder and Harnack for linear divergence-form weak solutions (Crescimbeni–Forzani–Perini, cited through I236 and the appendix, not read); Lax–Milgram and traces; Alexandrov's theorem and Julin–Juutinen Remark 3.3; Arzelà–Ascoli.

## 7. Checks (support only; not proofs)

- [`checks/r2_checks.py`](checks/r2_checks.py) uses the standard library only (`python3 -I`), and every check prints PASS ([run-output.txt](checks/run-output.txt)).
  - **Exact rational identities:** amplitude rescaling; frame G_τ[U]=RG_τ[V]; reflection; fit transform and domain; the Lemma 2.1 lifted-test identity; weighted mean of q_j; affine variance along ((q_j),1); envelope parameter scaling; coarse-ellipsoid geometry and the (7.2)/(7.5) scalings.
  - **Float samples of proved inequalities:** lemma (8), (11), (12), the (15) contraction and drift, the (16)/(17) choices, the R2 eigenvalue window [b₀²/6,3] on |q|≤min{1/8,b₀²/30}, B_d≥3/4, the flux derivative, and the λ₀ bound.
  - **Log-space R4 run** on a function with no power bound.
- [`checks/mutation-log.txt`](checks/mutation-log.txt) records six deliberate errors, all detected (M1–M6). Two mutations (M7, M8) are recorded as non-discriminating because the replaced constants are conservative or redundant, not because a check is missing.
- The round-1 `algebra_checks.py` (0df9689d…) was rerun from a copy, and all checks PASS.
- **Lean** ([checks/lean-audit.txt](checks/lean-audit.txt)): the source `LiftedEllipticity.lean` (20b41178…) was re-elaborated from scratch with Lean 4.34.1 (commit 5045d005…), against the existing mathlib package oleans. No `lake build` was run and nothing was written in `formal/`. Its three theorems depend only on propext, Classical.choice and Quot.sound. Coverage is only the real scalar zero-jet form after the orthogonal split. The split, Savin, and every PDE statement are not formalized, consistent with formal/README.md.
- During this review the parent concurrently added `formal/FrontierSupport/VectorEllipticity.lean` and changed `Audit.lean` and `FrontierSupport.lean` to import and audit it (19:43–19:47). Those new bytes were **not examined**. This round's formal statement covers only the three LiftedEllipticity lemmas at the hashes in input-hashes.json. The new file may formalize the orthogonal split, but no credit is given here.

## 8. Boundaries

- This PASS asserts no novelty, priority or substantiality, and gives no count credit.
- It does not audit the truth of the pinned theorems, which are stipulated.
- It covers no manuscript file other than the frozen `viscous-appendix.tex`.
- Reading limits are listed in [source-map.md](source-map.md).
