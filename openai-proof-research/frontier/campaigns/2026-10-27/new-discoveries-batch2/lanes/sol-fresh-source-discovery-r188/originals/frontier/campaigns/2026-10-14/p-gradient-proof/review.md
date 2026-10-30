# I345 independent adversarial proof review (proof gate only)

2026-10-14. Reviewer: Claude Opus 5.5 (independent review sub-agent; no child agents, no git operations, no edits outside this directory).
Scope: **proof gate only.** This is not a novelty or contribution decision, not an acceptance, and not a count increment.

## Verdict

**PASS, conditional.** I found no mathematical gap in the unrestricted claim, and I do not downgrade it. The verdict depends on four things: the stipulated pinned OpenAI theorems, the I236 finite-τ theorem as gated by I239, and the named classical interfaces (Kotschwar–Ni, compact-p C^{1,θ}, weak/viscosity equivalence, and Savin). The I344 unequal-parameter objection is **resolved**: the replacement bound O(κ²λ+η(1+log ν)) is proved and suffices. Before the manuscript stage, three documentation repairs are **required** (R1–R3). They concern provenance and self-containedness, not the logic of the argument. Four reading-scope items stay **UNRESOLVED** at the reviewer level (U1–U4). Each is a classical input or an earlier internal gate that I did not re-read in full.

Claim reviewed, verbatim from analysis.md §1. For each integer n≥2 there are α_n∈(0,1/3] and C_n<∞ with the following property. For every finite p≥3, every bounded weak solution u∈W^{1,p}_loc(B1) of ∫|Du|^{p-2}Du·Dφ=0 has its continuous representative in C^{1,α_n}(B1/2), and

    ||Du||_∞(B1/2) + [Du]_{α_n;B1/2} <= C_n osc_B1 u.

No sign, critical-point, level-set, gradient-modulus or boundary hypothesis is imposed. This is the claim stated in the task, and the review keeps it at that strength. The range is exactly p≥3. Nothing is claimed for 2<p<3, since ε=1/(p−2)≤1 is used (see R7).

## Reviewed files (SHA-256)

| File | SHA-256 |
|---|---|
| frontier/iterations/i345-lifted-p-gradient-research.md | d81860cf6f6ab3c73f56963d7e58cf28131bf8bb277779542a15a191d8b6a8ec |
| frontier/experiments/i345_lifted_p_gradient_research/analysis.md | f88c4ad3f983eb405912679864c7b8d5e64e933eb486f6cf1c49a8e9deabaa25 |
| frontier/experiments/i345_lifted_p_gradient_research/reading-and-failures.md | 9768928f507709c9af2ecbc6249e9672b1161a4fa50bd3041ebd69572621b017 |
| frontier/experiments/i345_lifted_p_gradient_research/input-authentication.json | 01a4dcf5f3299715765af1e34cfa44b58c7b232b229f8d6bee171479d47b4271 |
| frontier/sources/i345_lifted_p_gradient_research/literature.md | f08ddc4eda402780fdfa08a966bc63d469e86bc183b6348ffe9c1bbf656a9490 |
| frontier/iterations/i344-affine-lift-p-gradient-route.md | ba36168c8fea4e7a6cc3ea216e49198eee6853143479f89446df74cb9158fe51 (matches prescribed) |
| frontier/experiments/i236_viscous_contact_propagation/analytic-attempt.md | a30077ca36f40e6613e340d3f8ae0ac692000f7b39d6eb4113897f40b7c68931 (matches I239-audited bytes) |
| frontier/NEW-TEN-2026-10-14.md | 7cac04ef2f6d135e29101616fc86125056e00e4c9480388225923477877e0f23 |
| AGENTS.md | e9ab951853e1607e8d125adb5609a89214a46bb655fda39874257b8210093e7e |

The I345 files are **untracked** in git at review time (`??`). Acceptance must bind to the exact bytes above. Pinned sources and the other inputs are listed in [source-map.md](source-map.md).

## Section-by-section audit

Each item records what I reconstructed independently and its status.

### A. Uniform Lipschitz bound (analysis §2.1): PASS

I read the actual Kotschwar–Ni Theorem 1.1 (arXiv:0711.2291v1 HTML, retrieved 2026-10-14). The hypothesis is v>0 p-harmonic on B(x0,R) with sectional curvature ≥ −K². The conclusion, for each ε∈(0,1) and with u=−(p−1)log v, is

    sup_{B(x0,R/2)} |∇u|² <= 5(n−1)/(R²(1−ε)) · (c_{p,n} + (n−1)b²_{p,n}/(8ε)) + C(n,K,p,R,ε),

where b=2(p−1)/(n−1)−2 and c=(2(p/2−1)²/(n−1)+(p−2)p/2)_− + (p/2+1)max{p−1,1}. Also C=(n−1)²K²/(1−ε)+10(n+p−2)(n−1)(1+KR)/((1−ε)R²)+5max{p−1,1}(n−1)/((1−ε)R²).

Take K=0 and ε=1/2. For p≥3 the negative-part term is zero. Every term is then O_n(p²)/R², so |∇log v|=|∇u|/(p−1)≤K_n/R uniformly for p≥3. `checks/algebra_checks.py` evaluates the bound for p∈[3,10⁷] and n=2..8 and confirms that it is bounded. The theorem needs n≥2 because n−1 appears as a denominator. The shift v=u−inf u+M gives M≤v≤2M, hence |Du|≤2K_nM/R. Correct.

### B. Compact-p regularity (analysis §2.2): PASS as a classical input; reading item U1

Uniform C^{1,θ} estimates for p∈[3,P] are standard (Uhlenbeck, DiBenedetto, Tolksdorf, Lieberman), so I accept the fact. I did **not** re-read Uhlenbeck's proof. I345 itself records that Uhlenbeck PDF pages 5–8 were not read.

This input carries real weight. In the bounded-p branch with finite effective viscosity, the limit coefficient is ν+ε_*(2q_t+|q_x|²) with ε_*>0. That operator has gradient-dependent viscosity and is covered by neither the source Liouville theorem nor I236. Without compact-p uniformity, the bounded-p branch of §4 would therefore be unpaid. See R1.

### C. Uniform qualitative flatness (analysis §2.3): PASS

Reconstruction. Suppose the common o(r) Euclidean affine modulus fails. Then f_i(Y)=[u_i(y_i+r_iY)−u_i(y_i)]/r_i are L-Lipschitz, defined on domains that exhaust R^n, and stay at least δ from every linear map on B2. Arzelà–Ascoli gives an entire L-Lipschitz limit f.

The equation (P), D²u[Du]+ε|Du|²Δu=0, is a positive multiple (p−2)|Du|^{p−4} of the p-Laplacian where the gradient is nonzero. Both sides vanish at zero gradient, so viscosity solutions of (P) and of Δ_p coincide. (P) is invariant under the blow-up scaling, and its operators converge uniformly on compact jet sets as ε_i→ε_*∈[0,1].

- **Finite p_*:** f is a weak p_*-harmonic function (by equivalence) with a global Lipschitz bound. Scaling the fixed-p C^{1,θ} estimate shows it is affine.
- **p_*=∞:** F(Y,b)=f(Y)+b is infinity-harmonic by pinned `lem:linear-lift`, which holds in any dimension, and it lives in dimension n+1≥3. Scaling pinned `thm:main` on B_R gives [DF]_{α;B_{R/2}}≤C·2Lip(F)R·R^{−1−α}→0, so F is affine and f is affine.

Either way f_i→f uniformly on B2 contradicts the δ separation. The n=2 case is handled correctly through the dimension-three lift, without any planar theorem. Lifting a Euclidean fit, with slope (g,1) and exact in b, gives cylinder goodness on Z_λ⊂B_{2r}, so b(s)→0.

### D. Lift equation (analysis §3): PASS, including critical points

Reconstruction. At an upper test φ of U=u+b, the vertical restriction gives φ_b=1 and H_bb≥0. Set φ_σ=φ+σ(b−b0)²/2. Since ∂_b(φ_σ)_b=H_bb+σ>0, the implicit function theorem gives a C¹ branch b(y). The function ψ(y)=φ_σ(y,b(y))−b(y) has Dψ=D_yφ(y,b(y)), which is C¹, so ψ∈C². Its Hessian is K=H_yy−H_yb⊗H_by/(H_bb+σ), and ψ≥u with equality at y0. So ψ is a genuine C² upper test of u, and the viscosity inequality for (P) gives tr((g⊗g+ε|g|²I)K)≥0.

Next, H_σ−diag(K,0)=vv^T/(H_bb+σ) with v=(H_yb,H_bb+σ), which is positive semidefinite. Also M=(g,1)⊗(g,1)+ε|g|²Π is positive semidefinite, its yy block is g⊗g+ε|g|²I, and M_bb=1. Hence tr(MH)+σ=tr(MH_σ)≥tr(M_yyK)≥0, and letting σ→0 gives L(DU,H)≥0.

At g=0, M=e_b⊗e_b and the inequality reduces to H_bb≥0. Lower tests are symmetric. `checks/algebra_checks.py` verifies every matrix identity exactly over random rationals, including the reduction of the lift to (P) for smooth jets. The lift is correctly **not** claimed to be p-harmonic.

### E. Selection and the bounded-p branch (analysis §4): PASS

The strengthened running maximum is valid. Choose h_i so that the truncated supremum of b(s)s^{−γ_i} on [h_i,1/8] exceeds 2i. Then (4.2) and (4.3) follow, and (4.3) gives s_i/λ_i^k→0 for each fixed k. The source `lem:bad-scales` proof (03-reduction.tex lines 132–156) is equation-free and applies verbatim to the lifted p-family. It uses only b, its monotonicity, and admissibility.

Bounded-p branch: λ_i≤C s_i^θ together with λ_i>i s_i^{γ_i}/4 gives a contradiction once γ_i<θ. This uses B.

### F. Geometric compactness reuse (analysis §4, source prop:nonaffine-limit): PASS

I re-read source lines 214–300. Every step is equation-free except the single line (282) that identifies the limiting PDE: boundedness, equicontinuity, the sheared-domain decomposition, passage of the fits with C0=8Λ, and non-affinity. These steps use only `lem:bad-scales`, `lem:cylinder-comparison` and the slope bounds (4.1), all of which I345 pays for its family. The PDE line is replaced (G and H below).

### G. Rescaled PDE, jet constraint, extension, negative viscosity (analysis §5): PASS

I recomputed (5.1) and (5.2) exactly; see the checks script. The derivation runs as follows:

- The test gradient is c_i q_i. The Hessian is (c_i/r_i)S_λD²φS_λ.
- Dividing (L) by λc_i³/r_i gives C_i=ε|Π q|²/λ.
- The constraint q·ξ=1/c_i holds at every upper and lower test, because U is exactly linear along ξ. On tests it gives |Πq|²=A+λ(2φ_t+|D_xφ|²)+λ²φ_t².
- The max(C_i,0) extension is degenerate elliptic and continuous, and it agrees with the true coefficient at every test. Stability is therefore legitimate.
- Bounded contact: V_i−K|z|² with K>M attains an interior maximum. The test gradient there is bounded by 2K, and |Πq|²≥0 is a squared norm, so A_i≥−C_Mλ_i and ν_i≥−C_Mε_i→0.

Note that the crude slope bound would only give A_i≥−O(√λ_i), so the contact argument is genuinely needed.

The transport identity (5.4) also checks. Physical shift τξ corresponds to σ=τ/(r_i√λ) and w=(a,b√λ), with δ=(β−b)/√λ, and |δ|≤2M|w| from boundedness on a ball of radius 2.

### H. Finite effective viscosity (analysis §6): PASS

- S_λΠS_λ=S²−(Sξ)⊗(Sξ)→diag(I−a⊗a,0). max(C_i,0)→ν uniformly on compact q-sets. The limit equation is F_{ν,a}.
- **a=0:** F reduces to G_ν. ν=0 gives the source `thm:liouville`; ν>0 gives I236. In both cases V is affine.
- **a≠0, PDE:** V(se+y,t)=ks+W(y,t). Each test ks+ψ of V has a Hessian that annihilates e, and V−φ=W−ψ, so it is a genuine local test. Both the rank-one term and ν tr((I−a⊗a)X_xx) reduce to the isotropic G_ν on e^⊥.
- **a≠0, fits:** I re-derived the projection (6.2) line by line. With h=dℓe+h_⊥, we have h−pℓ=h_⊥−p_⊥ℓ. The increment of the exact term is kdℓ, and p·h=d²ℓ+p_⊥·h_⊥. This gives FIT for W with the same C0 and time coefficient q+d²−kd. No bound on d or k is needed.
- **Dimensions:** the reduced dimension is m=n−1≥1 for n≥2, so both the source (m≥1) and I236 (m≥1) apply.

V affine contradicts non-affinity. **Original critical slopes are covered:** they correspond to A_i≲λ_i/ε_i, which is exactly this finite-ν branch, and negative A_i is controlled by G.

### I. Uniform lifted small-solution estimate (analysis §7): PASS (documentation repair R2)

- **Ellipsoid normalization:** recomputed exactly. The coefficient is B=|Πq|²/A=1+ε(2q_t+|q_x|²)+ε²Aq_t², and T_eD²UT_e=(ce/ℓ)D²W (checks script). If η≤e, the ellipsoid lies inside the η-cylinder: axial extent ≤H/4 and transverse extent (H/4)√η. The bound ||W||≤(4/c)√(η/e) follows.
- **Savin hypotheses:** the family F_{ε,A,e,ξ,d}(X,q)=X[(dq_x,1+edq_t)]+max(B_d,0)tr(S_eΠS_eX) is linear in X and degenerate elliptic everywhere (H1). For |q|≤1/8 we have B_d≥1/2, so the operator is polynomial there with bounded C² norm (H4) and vanishes at X=0. At q=0 the coefficient matrix M0=e_N⊗e_N+S_eΠS_e has spatial block I−a⊗a≥b0²I and time Schur complement exactly 1. I verified this exactly. The parent's explicit bound (b0²/3)|·|²≤M0≤2|·|² is consistent with the checks. Uniform H2 follows by continuity on a common small q-ball.
- **Uniformity of Savin's constant:** Theorem 1.3 states c1 "depending on F". The proof of Proposition 4.1 (pp. 571–573), however, is a contradiction argument over sequences F_k with ||D²F_k||≤K, and r0 is stated to depend only on δ, K and the universal constants (n,λ,Λ). So the threshold and the C^{2,α} bound are uniform over the compact parameter family.
- **Proportionality:** the amplitude rescaling Z=W/d with d=a0/σ∈(0,1] gives ||D²W||_{B1/2}≤Ca0 exactly. Without it, Savin's absolute bound would not suffice. Correct.
- **Taylor step:** for h∈Z_λ(0,r;P_new) with λ≤e we have |T_e^{−1}h|≤C'r, because T_e^{−1}P_new=c(D_xW,1+eW_t) and |P_new|≥c/2. Taylor's formula then gives (7.6), error ≤Ce r²/H.

### J. Unequal-parameter repair (analysis §8.1): PASS; the I344 objection is resolved

The objection was well founded. Source `lem:cylinder-comparison` is stated for **one** parameter θ², and I344 compared a Λλ base fit against an η=κλ coarse fit. I reconstructed the replacement:

1. **Common ball.** The η-cylinder contains the ball of radius √(Λλ)r, since κ≥64>Λ=32. On that ball |(P−Q)·h|≤(Λλ+η)r≤2ηr, so |P−Q|≤2κ√λ/√Λ and the angle is O(κ√λ). This is larger than √η by the factor √κ, so the equal-parameter lemma does not apply.
2. **Axial point.** Take z+t r n_P with t=c0κ^{−1/2}. Its transverse offset from the Q-axis is ≤c0C1√κ√λ r≤√η r when c0C1≤1, so the point lies in both cylinders. There |(P−Q)·n_P|≤2η/t=O(κ^{3/2}λ).
3. **Norm comparison.** |P|−|Q|≤(P−Q)·n_P. In the other direction, |Q|−|P|≤|Q|·|n_P−n_Q|²/2+(Q−P)·n_P=O(κ²λ). Hence ||P|−|Q||≤Cκ²λ.
4. **Chain.** The comparisons from r_i to H_i=ν²r_i use equal η at ≤2log₂ν+1 dyadic steps. Both slopes have norm in [1/2,L+1] by (4.1), and η is good at every radius ≤H_i by (4.2) and R_is_i→0. This adds O(η(1+log ν)).

**Sufficiency.** A_i=ν_iλ_i/ε_i≥ν_iλ_i, and A↦1−c^{−2} is Lipschitz on [1/2,L+1]. So |A'−A|/A≤C[κ²+κ(1+log ν)]/ν. With κ=64·4^γν^{2γ} and γ_i→0, this tends to zero once 4γ_i<1. Therefore A'>0, A'/A→1 and e'~νλ. A purely vector O(κ√λ) comparison would give relative error κ/(√λ ν), which does not tend to zero, so the quadratic route is necessary and it works. The numerical bookkeeping is in the checks script.

### K. Infinite-viscosity closure (analysis §8.2): PASS

The available domain is H_i=ν²r_i≤s_iλ_i^{−2}D(z_i)=o(D(z_i)), with ν≤1/λ since ε,A≤1. The scale conditions all hold:

- η/e'~κ/ν→0;
- b'≥(1−√η)/(L+1);
- ℓ_i/r_i~ν^{3/2}√κ/4→∞;
- λ_i≤e'_i.

The resulting error divided by λ_i r_i is ~C e'/(λν²)~C/ν→0. With the nonzero slope DU_i(z_i), λ_i becomes good, contradicting the selection. This branch needs only A_i>0 eventually and ε≤1; it does not need ε→0.

### L. Finite-τ Liouville input (analysis §9 versus I236): PASS through I239; R3 required

I read the full I236 analytic proof (SHA a30077…, the exact bytes I239 audited, with PASS adopted in i239-viscous-proof-parent-disposition.md). Its theorem covers every m≥1, 0<τ<∞, finite C0, and every continuous entire G_τ-solution with the all-center, all-radius sheared FIT. It concludes affinity, with no extra regularity hypothesis. This is exactly the interface I345 §6 uses. I spot-checked its main steps: the time-Lipschitz bound via the scalar h(t), the cone-infimum v_L, the exponential flux identity div a(Df)=(E/τ)G_τ[f], the sup-convolution Fatou passage, Harnack applied to the replacement, and the common-time trace calculation. I found no defect, but I did not redo I239's full audit (U2).

I345 §9 is a **compressed restatement** of I236, not a self-contained proof. For example, it omits the strict cone recovery (3.2)–(3.4), the Lax–Milgram comparison and the extremal normalization. Its claim to have "independently revalidated" I236 overstates what the text shows.

### M. Derivative extraction and consequence (analysis §10): PASS

This step is identical to source lines 311–375, which I checked: α=γ/(2+γ)≤1/3, a uniform Taylor error, two-center comparison, and restriction to b=0 followed by rescaling. The rate ||Du_p−Dv||≤Cδ^{α/(1+α)} follows from finite differences, where δ is the uniform distance between the values of u_p and v, provided v satisfies a C^{1,α} bound. The text supplies that bound by passing the Taylor estimate to the limit. This is correctly labelled a consequence and not a separate result.

## Prior objections carried forward

| Objection | Disposition |
|---|---|
| I344 used the equal-parameter norm lemma for unequal Λλ/η fits | **Resolved.** The common-axis O(κ²λ) bound plus the equal-η chain is proved and suffices (J). |
| Earlier restricted routes (I230/I241) did not cover original critical points | **Resolved.** The lift treats zero original test gradients (D). Near-critical slopes fall in the finite-ν branch with the contact lower bound (G, H). |
| Earlier routes did not cover arbitrary selected slopes | **Resolved.** Every fit slope of the lift satisfies P·e_b≥1−√λ, so it is nonzero. Selection, transport and projection cover every direction a, including a=0 and a≠0. |
| Uniform qualitative flatness was unpaid (I241) | **Resolved** by expanding-domain entire rigidity (C). |

## Required repairs (before manuscript or acceptance)

These do not change the argument, but the proof of record is incomplete without them.

- **R1 (compact-p input).** Add an explicit primary citation whose constants depend only on structural bounds, so that p∈[3,P] gets one θ and one C. Alternatively, write out the uniformity check with Uhlenbeck pp. 5–8 actually read. State in the text that this input is needed for the bounded-p, finite-ν subcase (B).
- **R2 (Savin uniformity, stated as a lemma).** State a lemma: for operators satisfying H1, H2 and H4 with common (n,λ,Λ,δ,K), Savin's threshold c1 and C^{2,α} bound are common. Cite the sequence argument in Proposition 4.1 (p. 572) and record that Savin pp. 5–13 were not read in this chain. Fix explicit constants: q-radius 1/8 (so B_d≥1/2) and ellipticity b0²/3 (parent note `p-gradient-parent/ellipticity.md`).
- **R3 (I236 dependency).** Replace the claim "independently revalidated" in §9 with a citation of I236 (SHA a30077…) plus the I239 PASS as the proof of record. If the manuscript must be self-contained, include I236's full proof.
- **R4.** State the strengthened bad-scales lemma, with the choice of h_i, as a lemma rather than inline prose.
- **R5.** State §7 as a quantified lemma. Hypotheses: c∈[1/2,L+1], A>0, e=εA≤1, b≥b0, η≤d_*e, λ≤e, r≤k_*ℓ. Conclusion: P_new=DU(z)≠0 and the λ-fit error is ≤Ce r²/H, with constants depending only on n and L. Make explicit that A here is computed from the **coarse** slope, and that (8.4) is what relates it to the base A.
- **R6.** Bind acceptance to the exact SHA-256 values above, since the I345 files are untracked.
- **R7 (scope).** Keep "p≥3". The proof uses ε≤1 in e≤1 and in the parameter family. Do not extend the claim to 2<p<3 without a separate argument.

## UNRESOLVED (reviewer reading scope; none is a known gap)

- **U1.** Uhlenbeck's compact-p uniformity proof was not re-read by me, and I345 did not read pp. 5–8. The result is classical.
- **U2.** I did not repeat the full I239 audit of I236. I rely on the adopted PASS and the matching SHA.
- **U3.** Savin pp. 5–13 (the Harnack lemma and Corollary 3.3) were not read. They are universal-constant statements that Proposition 4.1 uses.
- **U4.** The weak/viscosity equivalence for the p-Laplacian (Julin–Juutinen; Juutinen–Lindqvist–Manfredi) is used as a classical input. Its sources were not re-read here.

## Checks

`checks/algebra_checks.py` uses only the standard library and runs with `python3 -I algebra_checks.py`. It verifies, with exact rational arithmetic over 200 random instances each:

- the Schur/PSD identities of the lift and its reduction to (P);
- the rescaled PDE coefficient (5.2) and the |Πq|² identity;
- the ellipsoid coefficient B and the scaling T_eD²UT_e;
- the time Schur complement of M0 being exactly 1, plus a float check that M0 is positive definite;
- that the Kotschwar–Ni constants divided by (p−1)² stay bounded for p up to 10⁷;
- the unequal-parameter exponent bookkeeping;
- a radial p-harmonic sanity identity.

All checks print PASS. Four deliberate mutations (dropping ελφ_t², changing ε²A to εA, changing the Schur-complement assertion, perturbing the Schur denominator) each cause an assertion failure. **These checks support the review and do not replace it.** They are not a formalization. No Lean proof of the theorem exists. The parent's `LiftedEllipticity.lean` covers only the polynomial ellipticity inequality, and I did not review it.

## Boundaries

This proof PASS does not assert novelty, priority or substantiality. The contribution gate must still compare the result against primary literature, including convex-ring and planar p→∞ gradient work and value-rate papers. It also does not assert the truth of the pinned theorems, which are stipulated.
