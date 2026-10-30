# Independent adversarial proof review r1: T337E

Reviewer: independent proof-review sub-agent (Factory Droid, Claude Opus 5.5), first independent round. Own directory: `frontier/campaigns/2026-10-14/t337e-proof-r1/`. Proof role only: no contribution, novelty, acceptance or count judgement. Count 14/20 was given no weight. Review prose CC BY 4.0; scripts MIT.

## Verdict

**NOT_PASS_R1_REQUIRED_REPAIR (PASS_FULL_T337E withheld).**

One required objection remains, R1. In both the n>2 and the n=2 branches, the proof applies Stadler's Proposition A.1 rigidity at the endpoint radius r₀ = d(p, spt ∂S) = 1. The printed statement allows r₀ ≤ d(p, spt ∂S), but Stadler's proof begins "suppose Θ_{p,r₀}(S)=ω_n holds for some r₀ < |p, spt(∂S)|" and uses strictness (χ_S∩B̄_r(p)=spt S∩B̄_r(p) only for r<|p,spt ∂S|). In the application the endpoint is forced: in the rigid conclusion the centre lies at distance exactly 1 from the boundary. The candidate therefore relies on a case that the cited proof does not cover. A short exhaustion repair exists; I give it in full below and checked it. It does not change the scope. With it incorporated, I found no other mathematical gap: every other frozen quantifier (items 1–7 of the dispatch) is proved, with the optional exposition items O1–O9 below.

The verdict is withheld only because the gate is on the frozen author proof, which as written cites an uncovered endpoint case. No weaker scope is proposed or needed.

## Frozen inputs authenticated

| Item | SHA256 | Status |
|---|---|---|
| author `manifest.json` (external anchor) | `701a9549aa13d547f101ef9dd4ff3c890274384fef4020f6d20bc8b4c7faaa20` | matches dispatch |
| `proof.md` | `0b8a1c15141ac264c538ab97da429b1f2390878e1c7f9b089dc52c3cd5bc7a5d` | matches dispatch and manifest |
| `original-scope.txt` | `f16d3a1ad0c6e777151f2c1862e2a4f560b93272dadc31b102769d3066da70b9` | matches dispatch and manifest |
| `sources/preprints-tree.json` | `eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b` | 13223 entries, `truncated: false`; packet copy byte-identical |

I read `verify.py`, `controls.py` and `diagnostic.py` before running anything. Author `verify.py` on the canonical packet with the external anchor: `PASS_INTEGRITY_ONLY files=88 directories=20`. Only after this did I use the inventory. The 89-file SHA256 list of the canonical packet was identical before and after all runs.

## Source formulas actually read

Stipulated at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; I validated only the new deductions and the exact interfaces. I read in full, from the authenticated copies: source337 `01-introduction`, `02-currents`, `03-radial`, `04-sobolev`, `05-minimizer`, `06-chords`, `07-conclusion`, `08-classical`. Stadler arXiv:2212.07100v1 Appendix A opening through Corollary A.4 (local text 760–999). Lytchak, *Differentiation in metric spaces*: an archived full preprint (see `reading-limits.md`), §1 lines 230–279, §§3–8 lines 335–984, §12 and references lines 1340–1477. Exact ranges and what was not read are in `reading-limits.md`.

## Item 1. Compact reduction, normalization, extremizer inequality, radial inequality

* **All finite-mass fillings.** For a closed ball Y ⊇ spt T, nearest-point projection P: X→Y is 1-Lipschitz (source02 `lem:compact-reduction` proves the same radial formula). For any finite-mass integral S in X with ∂S=T, P#S is integral in Y, M(P#S) ≤ M(S), and ∂P#S = P#T = T because P is the identity on Y ⊇ spt T. Inclusion gives the reverse. So V_Y(T)=V_X(T) with no compact-support assumption on X-fillings. Source02 `thm:current-background`(v) gives a minimizer in Y. Correct.
* **Normalization.** Scaling distances by R⁻¹ scales M(T) by R⁻ⁿ and V by R⁻⁽ⁿ⁺¹⁾, so equality is preserved and m=s_n. Then c_n q m^{1/n} = s_n^{1/n}((n+1)/n)/((n+1)s_n^{1/n}) = 1/n, which is exactly source02 `eq:normalization`.
* **(1).** For an integral n-cycle B in Y, source `thm:main` applied in the proper CAT(0) space Y gives V(B) ≤ c_n M(B)^q, and subadditivity gives V(A) ≤ V(B)+V(A−B). With V(A)=c_n m^q this is source02 `eq:extremizer` with c=c_n. No maximizer construction and no m<s_n is used. Correct.
* **Radial inequality (2).** I read the whole proof of source03 `prop:radial`. It uses only: compactness of Y, the chart formulas of source02, `eq:extremizer`, m>0 and `eq:normalization`. The strict m<s_n appears only in `prop:base` (`eq:base-small-mass`) and in source05 `eq:strict-subthreshold`, neither of which is used for (2). Correct for every centre y∈Y and every nonnegative Lipschitz g.
* **(3).** g=1 gives m ≤ ∫ r√(1−|Dr|²) dμ ≤ ∫ r dμ ≤ (m I(y))^{1/2}. Correct.

## Item 2. Cycle dimension n>2

* **Hypotheses of source04–05 at m=s_n.** `prop:small-set` uses `eq:extremizer`, the normalization, the coarse constant K_n and the dimension-(n−1) sharp theorem (stipulated). Its constant C=nK_n2^{1+2/n} uses only cq₀m^{1/n}=1/n. `lem:intrinsic-coarea`, `lem:rearranged-energy`, `lem:radial-sobolev` and `prop:almost-sobolev` use no bound on m. `prop:sobolev-space` and `prop:compact-embedding` use only finite mass, the cycle identity and the chart representation; the header phrase "0<m<s_n" in source05 is not used in their proofs. Correct.
* **Subthreshold contradiction.** In `prop:minimizer` the only use of m<s_n is (`eq:strict-subthreshold`) Λ<S_*, which is then used solely to force t=1 in `eq:no-critical-mass-loss`. Assuming Λ<S_* for contradiction, the same proof gives a nonnegative minimizer with W=(Λ/n)^{n/2}<s_n, Euler equation and Q(v)=nW. `lem:powers`, `lem:composites`, source06 and source07 then give 2 ≤ ∫L_y dν ≤ 2(W/s_n)^{2/n} < 2, exactly as in the source's final proof. So Λ=S_*. The constant test Q(1)/‖1‖_p² = n m^{2/n} = S_* shows 1 is an attained minimizer. Its normalization v=(Λ/n)^{1/(p−2)}m^{−1/p}=1 and the Euler equation holds trivially (4β·0+n∫ψ=n∫ψ). No compactness at the threshold is claimed. Correct.
* **Endpoint chord estimate.** With v=1: κ=1, s=r, ν=μ/m (the probability normalization is retained), L_y=I(y)/m. `prop:chord-transform` uses the Euler equation, quotient minimality of v (true: Λ=S_*=Q(1)/‖1‖_p²) and the extended radial inequality; it never uses W<s_n. `lem:chord-density` gives L_y ≤ 2(W/s_n)^{2/n} = 2 for ν-a.e. y; only the final "<2" uses W<s_n, and source `rem:chord-sphere` confirms saturation at W=s_n. Hence (4) I(y) ≤ 2m μ-a.e. Correct.
* **Variance.** Source07 with v=1 has B_*=m and gives I(y) ≥ I(o)+m d(o,y)² for every y, with o a minimizer of I. Integrating, ∫I dμ ≥ 2m I(o). With (4), I(o) ≤ m; with (3), I(o)=m. Then (2) at y=o, g=1 forces √(1−|Dr|²)=1 a.e. and equality in Cauchy–Schwarz, so r=1 μ-a.e. and spt A ⊂ S(o,1). Correct.
* **Cone and centre in support.** For the cone S=H#([0,1]×A), H(t,x)=[o,x]_t, the source03 comparison form (`eq:radial-two-point` with fractions t,t′) has total determinant density r t^n √(1−|Dr|²) J, and source02 `lem:quadratic-mass` gives the **measure** inequality ‖S‖ ≤ H#(r t^n√(1−|Dr|²) dt dμ). With r=1 μ-a.e., d(o,H(t,x))=t, so ‖S‖(B(o,b)) ≤ ω_{n+1}b^{n+1}, ‖S‖{d(o,·)=t₀}=0, ‖S‖ outside B̄(o,1) is 0 and M(S) ≤ ω_{n+1}=V(A). Saturation forces ‖S‖(B(o,b))=ω_{n+1}b^{n+1}>0 for all b, so o∈spt S and d(o,spt A)=1. The proof's sketch "the same cone parametrization, restricted to a<t<b" is correct once read as this measure inequality (O4). Final step: see R1.

## Item 3. Cycle dimension 2: completed square, density one, Fubini, charts

* **(5).** With n=2 and g_ε=max(r,ε)⁻²: on {r<ε} the integrands are 2ε⁻² and ≤2ε⁻¹; on {r>ε}, Dg=−2r⁻³Dr gives 2b² and 2b. Hence (2−2ε)ε⁻²μ(B(y,ε)) ≤ ∫_{r>ε}(2b−2b²) = μ{r>ε}/2 − 2∫_{r>ε}(b−½)² ≤ m/2 − 2∫_{r>ε}(b−½)². I re-derived this; it is the source03 computation with the square retained.
* **Density and (6).** At a good pole liminf ε⁻²μ(B(y,ε)) ≥ π, and m/2=2π. So the first term tends to 2π and ∫_{r>ε}(b−½)² → 0 along eligible ε. Monotone convergence gives b=½ μ-a.e. on {r>0}, i.e. |D_xd_y|²=1−d(x,y)²/4, hence d ≤ 2 a.e. Eligible radii are co-countable, so the sandwich extends the limit to all radii. Correct.
* **Fubini.** The failure set is μ⊗μ-null because every good pole has a null x-section. Joint Borel measurability of (x,y) ↦ D_x d_y holds, for example because McShane extensions of d_y∘φ_i are jointly continuous in (z,y) and derivatives are limits of difference quotients (O2). Correct.
* **Chart point and (7).** A full-measure set of x is: a density-one point of D, a Lebesgue point of θ1_D, a metric-differentiability point with Euclidean norm (source02 `lem:euclidean-chart-metrics`), a strong-differentiability point (Lytchak Theorem 1.6), a good pole itself, and a point where (6) holds for μ-a.e. y. The chart contributes lower density ≥ π|θ(0)|, the total density is π, and |θ(0)| is a nonzero integer. So |θ(0)|=1, the chart density is π and the remaining charts contribute o(ρ²). Correct; the text should list "x is a good pole" and the |θ(0)|=1 deduction explicitly (O1, O5). No regularity of the other charts is used.

## Item 4. Lytchak Theorem 1.6 and the uniform chart expansion

I obtained and read an archived full preprint of Lytchak (see `reading-limits.md`).

* **Exact statement (§1, Theorem 1.6).** "Let Z be either CAT(κ) space or a space with curvature ≥ κ. Let S⊂ℝⁿ be a measurable subset, f:S→Z a locally Lipschitz map. Then f has at almost each point a differential D_xf: T_xS → C_{f(x)}Z." C_x is defined in §5.1 as the **metric completion** of the germ cone. §7.7 defines a strong differential D_xf: T_xX→C_z by f^{(o)}_x = exp^{(o)}_z ∘ D_xf for **every** scale (o). At a Lebesgue density point, T_xS=ℝⁿ (Example 6.8). §5.3: in CAT(κ) spaces C_x is a Euclidean cone, exp^{(o)} is an isometric embedding for every scale, and (Nikolaev) C_x is geodesic. Arbitrary measurable chart domains are covered. Y is compact CAT(0), and φ_i is bi-Lipschitz on a bounded Borel E_i.
* **Isometric flat.** For u,u′∈ℝ²: d_C(Dφ u, Dφ u′) = d(φ^{(o)}u, φ^{(o)}u′) = lim d(φ(t_iu_i),φ(t_iu′_i))/t_i = |u−u′|, by the isometric exp and the two-point metric differential normalized to the Euclidean norm. An isometric embedding of ℝ² into a CAT(0) space has convex image (unique geodesics), and D is homogeneous. So E=Dφ(ℝ²) is a flat through the vertex on which cone dilation is scalar multiplication. Correct.
* **Uniform o(|z|).** log_x: Y→C is 1-Lipschitz (Alexandrov angle ≤ comparison angle; Lytchak Remark 6.12). For any scale, the blow-up of log_x satisfies log^{(o)}∘exp^{(o)} = inclusion C⊂C^ω (on germs (γ(st_i))↦ρ_{t_i}(γ,s), then by continuity on the completion). Hence (log_x∘φ)^{(o)} = Dφ as constant sequences. If d_C(log_xφ(z_i), Dφ(z_i)) ≥ ε|z_i| along z_i→0 in D, take t_i=|z_i| and a subsequence z_i/t_i→w; under a nonprincipal ultrafilter on it the ultralimit distance is ≥ε, contradicting the blow-up identity. So log_x(φ(z)) = Dφ(z)+o(|z|) uniformly on D. The author's inference is correct. It needs no properness or local geodesic completeness of C.
* Lytchak's §12 reduces n>1 to n=1 by "standard reasoning ([Kir94],[MM00])". This is a published classical theorem; I did not re-prove it (reading limit, not an objection).

## Item 5. Two-sided contraction, Busemann squeeze, parallel set, f

* **(8).** For unit e∈E, put a_±=r cos∠(v,±e). The cone cosine law is exact: d_C(v,te)² = r²+t²−2ta_+. Contraction gives d(y,φ(z)) ≥ d_C(v,log_xφ(z)) ≥ d_C(v,z)−o(|z|), and d_C(v,z) ≥ d_C(v,te) − t|z/t−e|, so no continuity in e is needed. Expanding along z/t→±e (density one) gives ℓ(e) ≥ −a_+/r and −ℓ(e) ≥ −a_−/r, so a_++a_− ≥ 0. Busemann functions of the line te in C are b_±(v)=−a_± (Lytchak Example 4.2), and b_++b_− ≥ 0 gives a_++a_− ≤ 0. Equality: ℓ(e)=−a_+/r for all e, hence d_C(v,z)²=r²+|z|²+2rℓ(z) for all z∈E. With w=−rℓ^♯, h²=r²(1−|ℓ|²)=r⁴/4. Correct; (9) checked.
* **Parallel-set lemma.** At v: b_+(v)=−⟨e,w⟩, b_−(v)=⟨e,w⟩. In a complete CAT(0) space asymptotic rays exist from every point (no properness). Along the ray from v toward +∞, b_+ drops at unit speed, b_− is 1-Lipschitz, and b_++b_− ≥ 0 forces exact unit increase; symmetrically for the other ray. Then |b_+(c(s))−b_+(c′(t))|=s+t certifies a geodesic line through v, asymptotic to both ends of L, hence parallel. Flat strip and the splitting P(L)=ℝ×C₁ hold in CAT(0) spaces. The ℝ-coordinate of v is ⟨e,w⟩ (Busemann normalization), so the identity descends to (C₁,E₁). C₁ is closed and convex in C (limits of parallel lines are parallel lines in a complete space), hence complete, so the iteration is legitimate (O3). After two steps v=(w,n) with d_N(n,n₀)=h. Correct.
* **f.** P(E)=ℝ²×N is closed and convex, so its nearest-point projection is 1-Lipschitz. (w,n)↦(w,d_N(n,n₀)) is 1-Lipschitz for the ℓ² product. So f is globally 1-Lipschitz on Y. (11): |f(y)|²=|w|²+r⁴/4=r² and |f(y)−(0,0,1)|²=r²−r⁴/4+(r²/2−1)²=1. These hold μ-a.e., extend to spt A=spt μ by continuity, and f(x)=0. (12) follows from the uniform expansion, the projection fixing E, and 1-Lipschitzness of the last map. Correct.

## Item 6. Noncancellation

* f#A is an integral 2-cycle supported in f(spt A)⊂Σ. Constancy (Federer 4.1.31) gives f#A=k[[Σ]].
* Remote sheets: by (11), f⁻¹(B_{Rρ}(0))∩spt A = B(x,Rρ)∩spt A. Hence a test supported in B_R sees only A⌞B(x,Rρ). Off-chart part: by the mass bound with Lip(ρ⁻¹f)=ρ⁻¹, its contribution is ≤ Cρ⁻²·o(ρ²)=o(1). Chart part: by the chart action with a Borel first coefficient, it equals ∫θ(ρζ)1_D(ρζ) b(F_ρ) det D(π∘F_ρ) dζ. Here |ζ| ≤ CR is automatic, since |F_ρ(ζ)| = ρ⁻¹d(x,φ(ρζ)) for μ-a.e. carried chart points.
* McShane extensions F̃_ρ have a common Lipschitz bound and agree with F_ρ (and in derivatives, at density points) on D/ρ. Density one makes the largest hole in the fixed disk vanish, and with (12) this gives F̃_ρ→(ζ,0) uniformly. Replacing the weight by σ costs ≤ C‖θ(ρ·)1_D(ρ·)−σ‖_{L¹(B_{CR})}→0. The fixed normal current σ[[B_{CR}]] then has pushforwards converging in flat norm by the straight-line homotopy formula. No chart piece is assumed normal. The blow-up of f#A is σ times the plane; that of k[[Σ]] is k times the same plane. So |k|=|σ|=1. Correct.

## Item 7. Minimum filling, interior point, rigidity, converse

* f#S is a compactly supported integral 3-current with ∂f#S=±[[Σ]]. Subtracting ±[[B₁(c)]] leaves a compactly supported top-dimensional cycle in ℝ³, which is 0 (source08 `lem:top-dimensional-constancy`). c∈spt f#S⊂f(spt S), since f(spt S) is compact. For p∈spt S with f(p)=c, 1-Lipschitzness and f(spt A)⊂Σ give d(p,spt A) ≥ 1. M(S)=c₂(4π)^{3/2}=4π/3=ω₃. Correct.
* **Stadler A.1 hypotheses.** Y is a locally compact CAT(0) space. S∈I_{3,c}(Y) is an area minimizer in Y (V_Y=V_X), and p∈spt S∖spt ∂S. Monotonicity on r ≤ d(p,spt ∂S) with Θ ≥ ω₃, together with open-ball left continuity, gives ‖S‖(B(p,1)) ≥ ω₃=M(S). So Θ_{p,1}=ω₃. Then: **R1**.
* **Converse.** K=F(B̄_R) is convex (images of Euclidean segments are the unique geodesics) and compact, so π_K is 1-Lipschitz on the complete space X. For any finite-mass integral filling S, π_K#S is supported in K with boundary T. Via the isometry it is an integral (n+1)-current in ℝⁿ⁺¹ supported in B̄_R; constancy forces it to be ±[[B_R]] (compatible orientation), so M(S) ≥ ω_{n+1}R^{n+1}, and [[F(B_R)]] attains this. M(T)=s_nR^n gives c_nM(T)^q=ω_{n+1}R^{n+1}. Scale restoration and the radius formula are correct. Isometry in X holds because Y is convex.

## Required objection

**R1 (Stadler endpoint radius; both branches).** Proof §3 (centre o, r₀=1=d(o,spt A)) and §7 (point p, r₀=1 ≤ d(p,spt A), with equality in the conclusion) invoke the equality case of Stadler Proposition A.1 at r₀ equal to the boundary distance. Stadler's proof treats only r₀<|p,spt ∂S|. The text "equality at a radius no greater than that distance" and the reading ledger's "full proposition and proof were read" do not address this.

Verified repair, to be written into the proof. Let k=n+1 or 3.

1. Θ_{p,r} is nondecreasing on (0,1] and ≥ω_k, and Θ_{p,1}=ω_k. Hence Θ_{p,r}=ω_k for all r∈(0,1].
2. Apply Stadler's proven case at each r₀<1. K_{r₀}=spt S∩B̄_{r₀}(p) is convex and isometric to the Euclidean r₀-ball, with p corresponding to the centre: in a Euclidean r₀-ball only the centre is within r₀ of every point. Multiplicity is 1 there.
3. K_{r₀}=K_{r₁}∩B̄_{r₀}(p) for r₀<r₁. Composing with orthogonal maps fixing the centre makes the isometries compatible. This gives an isometric F: B₁→U=spt S∩B(p,1), which extends to F: B̄₁→Ū⊂Y because Y is complete.
4. ‖S‖(B(p,1))=ω_k=M(S), so S=S⌞U and spt S=Ū=F(B̄₁).
5. Push forward by Ψ=F⁻¹ (defined on spt S; the result does not depend on the Lipschitz extension). Ψ#S is an integral k-current in ℝ^k supported in B̄₁ with |multiplicity|=1 a.e. Its boundary Ψ#A is supported in ∂B₁, because spt A⊂spt S∩{d(p,·) ≥ 1}=F(∂B₁). Constancy on the two components of ℝ^k∖∂B₁ gives Ψ#S=±[[B₁]], so S=±F#[[B₁]] and A=±F#∂[[B₁]].

Step 5 also supplies the orientation constancy that the proof's "S is its integration current up to orientation" leaves implicit (Stadler's multiplicity is unsigned).

## Optional objections

* **O1** §4: state that the selected x is itself a good pole (density exactly π). (7) uses it.
* **O2** §4: give the joint-measurability construction behind the Fubini step.
* **O3** §5: note that P(L), its cross-section C₁ and P(E) are closed convex subsets of the complete cone. The iteration and the 1-Lipschitz projection need this.
* **O4** §3: cite source02 `lem:quadratic-mass` and the source03 comparison form for the **measure** bound on the cone (annuli, spheres, centre in support). "Usual cone mass bound" gives only total mass.
* **O5** §4/§6: derive |θ(0)|=1 explicitly from the chart lower density ≥π|θ(0)| and total density π.
* **O6** §5: "Lytchak §7.7" should be paired with §5.1 (completion), §5.3 (isometric exp in CAT(κ)) and §6.12/Example 6.8. The strong differential is defined for all scales, which is what the uniform argument uses.
* **O7** Reading ledger: an archived full Lytchak preprint was retrievable from the Internet Archive copy of the author's Cologne URL (receipt in `reading-limits.md`). Its numbering is preprint pages 1–34, not journal pages 128–161. Theorem 1.6, §7.7 and §12 match the author's citations. I did not verify equivalence to the published St Petersburg Math. J. text.
* **O8** Tooling: the author `verify.py` checks source blobs and receipts with bare `assert`. Under `python -O` an altered, resealed source body is accepted (under its new anchor). Blob failures also carry no reason text. Use explicit raises. The external anchor still protects the canonical run.
* **O9** §2: mention that `prop:radial` is also used in its source05 H-extension (`prop:sobolev-space`(iv)) for the n>2 tests. It holds unchanged.

## Validation run (supports the review; proves no mathematics)

* Author `verify.py` on the canonical packet with the external anchor: PASS (88 files, 20 directories).
* Reviewer `independent-source-check.py`. It uses no author receipts or bindings. It maps the three copied families by fixed directory prefix to the repository's canonical `sources/preprints-tree.json` and matches 14+16+13=43 Git blobs. Not copied: each family's `paper.pdf` only. The packet tree copy and context copies (`AGENTS.md`, `sources/upstream.json`, `sources/CONTENTS.md`) are byte-identical to the repository. Negative controls on the disposable copy: an appended byte to `05-minimizer.tex` was rejected (blob mismatch), and an extra `source337/extra.tex` was rejected (no canonical path). Both mutations were removed and the copy re-verified.
* Author `controls.py`, run only on a fully authenticated disposable copy under `/var/tmp`: 14/14, identical to the frozen `controls-result.json`. Author `diagnostic.py` replay equals `diagnostic-result.json`. These finite rational checks are diagnostics only.
* Reviewer `author-copy-controls.py` (results in `author-copy-controls-results.json`). It runs the author verifier on reason-checked clones: positive, plus the 13 author mutations, each with the exact exception type and reason substring, plus two resealed-under-new-anchor attacks. The altered source blob was rejected by AssertionError and the renamed canonical-tree entry by KeyError. All PASS. A documented limitation case shows acceptance under `python -O` (O8).
* All scratch was created under `/var/tmp/t337e-proof-r1-scratch/` and removed at the end. The canonical packet's 89-file SHA256 list was unchanged.

## Review packet seal

`manifest.json` lists every file (except itself) and directory of this packet with size and SHA256, including the ignored `private/` Lytchak copy. `review-verify.py` requires two external anchors, for the manifest and for the verifier. It rejects root, ancestor and payload symlinks, hardlinks, nonregular nodes, nested manifests, parent traversal and any missing, extra or changed entry:

    python3 -B review-verify.py --expected-manifest MANIFEST_SHA256 --expected-verifier VERIFIER_SHA256

`review-controls.py --packet DIR --scratch EMPTY_DIR --expected-manifest … --expected-verifier …` runs 25 copied controls, each checked for exit status and the exact failure reason (two positives, one of them under `python -O`, and 23 rejections: wrong and malformed anchors, edited, deleted and extra files including in `private/`, an extra empty directory, a nested manifest, root, ancestor and payload symlinks, parent traversal, a hardlink, a FIFO, an edited manifest, an edited verifier, a swapped packet verifier run from outside, a self-resealed verdict flip and a reseal by `seal.py`). `review-controls-results.json` records the run against the pre-final seal, taken before that file existed. The same controls were rerun against the final seal. Every case gave the same status and reason; the only difference was the positive payload count, 12 before the results file was added and 13 after. The external anchors are reported to the parent outside the packet. `seal.py` writes the manifest. It is not needed for verification.

## Independence and conduct

I did not read the parallel reviewer's draft or any contribution review. I read the parent's `proof-r1-dispatch.txt` and `sealed-preflight.json` as context only, and I treated the parent's Busemann and noncancellation suggestions as author material to be checked. No nested agents. No staging, commits, uploads, shared-ledger or count edits. The additional primary body (the Lytchak preprint) is kept in ignored `private/`.
