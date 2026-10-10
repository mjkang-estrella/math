# I66 — Logarithmic robustness of the periodic defocusing blowup mechanism

**Author verdict: complete proposed deduction, requiring fresh independent proof and contribution reviews. No acceptance, count increment, commit, publication, or priority claim.** The proposed theorem is stability of the source's open blowup set after adding a nonhomogeneous logarithmic factor to the nonlinearity. It does not extend the linear dispersive estimates to arbitrary metrics or potentials. Two other precisely quantified targets were screened first. The key operation here is a time-dependent amplitude normalization, followed by a stable-graph construction with different polynomial weights for the phase and the other spectral coordinates. Applying the source's exponential-weight graph unchanged would fail.

All statements and lower proof operations in `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. Only applicability and new deductions are considered. The eight accepted findings are R006, R008–R014; the parent owns their status. In particular, this is independent of I65's algebra-rounding work and has no consequence for its status.

## 1. Evidence and exact source interfaces

The [full brief](../sources/i66_dispersive_equation_discovery/full-brief.txt), four mutable front-page snapshots, AGENTS.md, complete inventory, relevant prior reports and reviews, and accepted findings are frozen in [the input manifest](../sources/i66_dispersive_equation_discovery/inputs-manifest.json). Prior evidence is hash-referenced, not recursively copied. I07's inverse-energy gap, I36's final **technical only** judgment, I37's routing obstruction, and I52/I54/I57/I58's standard-map extraction history were inspected. None is revived here. All writes are in the three assigned I66 paths; no agents were spawned.

The complete inventory has 13,223 entries and 749 manuscripts. `rg --files --no-ignore` enumerated all 9,340 cached corpus files. Every cached Git blob was checked against that inventory. Four fixed-domain searches retain sorted **line multisets**, including multiplicity, in [searches.json](../sources/i66_dispersive_equation_discovery/searches.json). This is search coverage, not semantic reading of 749 manuscripts. The selected four manuscripts have 59 cached text artifacts, individually frozen with pinned URLs, Git blobs, and SHA-256 in [pinned-manifest.json](../sources/i66_dispersive_equation_discovery/pinned-manifest.json). Passage ranges identify what was actually read; the full cached corpus is only hash-referenced.

Abbreviate the four directories by W (critical local smoothing), P (planar endpoint convergence), H (higher-dimensional endpoint convergence), and B (stable periodic defocusing blowup). All dates in these directory names are September 24, 2026. The full names are in the manifest. These are the actual interfaces, not conclusions inferred from inventory names:

* **W**, `00-introduction.tex`, `thm:main`: for every ε>0, the Euclidean half-wave on R³ maps `J^ε L³` to `L³(R³×[1,2])`. Loss zero is not asserted. `09-physical-wave.tex`, `prop:phys-annular`, gives the annular version. Its predecessor-volume proof uses exact straight-ray backflow, a quadratic discriminant identity, a nonvanishing gradient on the physical input slice, and Jacobian `r⁴/(1+|A_*|²)`. `01-framework.tex`, `lem:fw-uniform`, only promotes sequential bounds within one fixed polynomial setup, including uniform tails. The source already includes the full strict Euclidean range, finite-time wave maximal estimates, maximal/nonmaximal Bochner–Riesz consequences, and their standard restriction/Kakeya implications.
* **P**, `01-introduction.tex`, `thm:main`, and `09-endpoint.tex`, `thm:maximal`: at H^{1/3}(R²), a translated-unit-ball **L¹-output** maximal estimate, and a common all-real-times continuous representative obtained by a Gaussian limit uniform in time. The paper does not assert endpoint L³ output. `08-dyadic.tex`, `thm:distribution`, has an unspecified fixed p>2 for compact smooth packet arrays and a two-dimensional ball-growth condition. `09-endpoint.tex`, `lem:endpoint-localized-dual` and `lem:endpoint-square-sum`, use projected spatial area, `m_{J,Q}≤r²`, a common time graph, heavy/light children, and a positive convexity deficit.
* **H**, `introduction.tex`, `m:main`, and `endpoint.tex`, `e:maximal`: the corresponding conclusion at `s_n=n/[2(n+1)]`, n≥3. The stronger companion already includes uniform Gaussian convergence on the common time line. `weak.tex`, `w:weak`, concerns n-dimensional growth and packet moments, with density/sparsity gains; it is not an α-dimensional endpoint theorem. `endpoint.tex`, proof of `e:dual-square`, uses `m_{J,Q}≤r^n` and integration of a kernel against spatial Lebesgue measure. These lower operations must change for a singular measure.
* **B**, `main.tex`, `thm:blowup`: there exist a sufficiently large odd p and a finite k>8 with an open set of H^k(T¹²) data blowing up at the Schrödinger scale, with positive limiting normalized amplitude at a point. Gaussian full support and higher-dimensional product examples are already in the paper; the latter do not assert stability. `profiles.tex`, `profile:existence`, gives a nonvanishing radial Q, with `a=1/(p−1)`, fixed b, and all fixed-order symbol bounds `|∂^j Q|≤C_j〈y〉^{-2a-j}`. In particular Q is not a compactly supported or L² profile.

For B the exact spaces and lower operations are essential. Write `s_0=6−a` and

\[
 \|v\|_Y^2=\|v\|_{\dot H^{s_0}(\mathbb R^{12})}^2+
                 \|v\|_{\dot H^k(\mathbb R^{12})}^2,
\]
\[
 \|v\|_{Y_L}^2=(2\pi L)^{12}\sum_{m\in\mathbb Z^{12}}
 [(L^{-2}+|m/L|^2)^{s_0}+|m/L|^{2k}]|v_m|^2.
 \tag{1}
\]

`linear.tex`, `lin:spatial`, gives uniform embedding/algebra bounds, cutoff localization, and the dyadic symbol bound
`R^{6−β−s_0}+R^{6−β−k}` for a symbol of order −β on radius R. The constant mode in (1) has norm `(2π)^6 L^a |z|`; it cannot be dropped. `linear:decay` gives an actual semigroup bound on the stable subspace, not just generator eigenvalues. There are bounded coordinates π with `πE=I`, where

\[
 E=(iQ,\partial_1Q,\ldots,\partial_{12}Q,(a-ib+D/2)Q),\qquad
 \Lambda=\operatorname{diag}(0,\tfrac12,\ldots,\tfrac12,1).
\]

At scale L, `E_L=χ(y/L)E`, `π_L=(πJ_LE_L)^{-1}πJ_L`, and `P_L=E_Lπ_L`. For a fixed sufficiently long step M and `L'=Le^{M/2}`, `linear:torus` gives

\[
 \|A_L\|:=\|(I-P_{L'})\mathcal F_L|_{\ker\pi_L}\|\le1/8,
 \quad \|\mathcal F_L\|+\|E_L\|+\|\pi_L\|\le C_M,
\]
\[
 e_L:=\pi_{L'}\mathcal F_L-e^{M\Lambda}\pi_L,
 \qquad \|e_L\|\longrightarrow0. \tag{2}
\]

The proof retains escaping norm through an energy-observation inequality before passing to a local limit. Equation (2) gives no general quantitative rate. `nonlinear.tex` gives cutoff residual `O(L^{-2-a})`, quadratic polynomial remainders, a graph using the weight 2^n, and a continuous degree argument selecting phase, center, and blowup time. Those are inherited operations, not contributions of I66.

## 2. Three distinct targets and early comparison

**A — variable-coefficient wave smoothing.** For every smooth compact boundaryless three-dimensional Riemannian manifold (M,g) and every ε>0, ask whether
`||exp(it√(−Δ_g))f||_{L³(M×[1,2])}≤C_{g,ε}||(1−Δ_g)^{ε/2}f||_3`.
This broad target is rejected: the positive-curvature metric obstruction requires p≥10/3 for the full gain, whereas the target has p=3. Beltran–Hickman–Sogge's [published primary paper](https://msp.org/apde/2020/13-2/apde-v13-n2-p03-p.pdf), printed p.404 and §4C, explicitly derives this from the Minicozzi–Sogge examples. The relevant page was rendered and read because its extracted inequalities were garbled. W itself distinguishes this setting. Small coefficient error alone does not preserve W's physical predecessor estimate at arbitrarily high frequency. No claim about an arbitrarily small prescribed metric neighborhood is made from this screen.

**B — an exceptional-set endpoint.** Fix n≥2 and α=n−1/10. For every A≥1, ask for `C(n,A)` such that every probability measure μ supported on the unit ball and satisfying `μ(B(x,r))≤Ar^α` for all r>0 obeys

\[
 \int\sup_{0<t<1}|e^{it\Delta}f(x)|\,d\mu(x)
 \le C(n,A)\|f\|_{H^{s_\alpha}},\qquad
 s_\alpha={n(n+1-\alpha)\over2(n+1)}, \tag{3}
\]

initially for Schwartz f. This is meaningful without choosing pointwise representatives of arbitrary Sobolev data. Du–Zhang's current [v3 primary text](https://arxiv.org/html/1805.02775v3), Theorems 2.2 and 2.4, gives the familiar loss-bearing fractal estimate and divergence-set application; its R^ε is not removed by P/H's Lebesgue conclusion. At the rescaled short time, pushing μ to `N^α μ(·/N)` and using only H's n-growth estimate leaves a factor `N^{(n−α)/p}` in the weak norm, on top of `N^{s_n}`. This elementary use reaches (3)'s exponent only if the usable p is at least `2(n+1)/n`, which is not supplied by the source's “some p>2.” Moreover, the area-dependent spatial localization in the common time tree must be replaced. This identifies two specific losses; it neither refutes (3) nor proves a new dimension bound. Later fractal/sequential counterexample literature was also searched, but no priority or sharpness conclusion is inferred from search absence. **Disposition: unresolved, not selected for full development.**

**C — logarithmic robustness of periodic defocusing blowup.** The selected target changes the equation itself:

\[
 i u_t+\Delta u=|u|^{p-1}u\left(1+{\kappa\over\log(2+|u|^2)}\right)
       \quad\hbox{on }\mathbb T^{12}. \tag{4}
\]

The sought quantifiers are `∃ odd p, integer k>8, κ_*>0; ∀ real |κ|≤κ_*; ∃ nonempty H^k-open U_κ; ∀u_0∈U_κ`, finite-time blowup with the same limiting normalized amplitude. The coefficient remains positive after taking κ_*<log 2, so (4) is a smooth scalar gauge-invariant defocusing nonlinearity. This is not the logarithmic Schrödinger equation `u log|u|²`, nor a change of initial data for the unmodified equation.

The actual nearest primary operations are the exponential Lyapunov–Perron construction in Buck–Carballeira–Gómez-Serrano–Shi [2609.23685v1](https://arxiv.org/html/2609.23685v1), Proposition 4.8; Li's symmetry-parameter matching and conditional open sets in [2304.02078v2](https://arxiv.org/html/2304.02078v2), Theorems 1.4–1.5 and §6.3; and periodic cutoff/finite-codimension constructions in Cao-Labora–Gómez-Serrano–Shi–Staffilani [2410.04532v1](https://arxiv.org/html/2410.04532v1), Theorem 1.1. The first treats specific pure-power whole-space equations, the second focusing pure powers, and the third a different scaling in dimension eight. Donninger–Wallauch's [2006.04600v1](https://arxiv.org/html/2006.04600v1) is a genuine robustness antecedent, but for a semilinear wave equation; its §1.1, equation (1.5), requires a perturbing power q<p. For nonzero κ, the magnitude `r^p/log(2+r²)` is not O(1+r^q) for any fixed q<p, so even that specific growth interface would not cover this perturbation. None of these inspected statements is (4)'s periodic defocusing theorem. This is a bounded comparison, not a certificate that every perturbative NLS paper has been excluded.

Current unversioned arXiv pages were captured before relying on versions. They list Buck v1, Li v2, Cao-Labora et al. v1, Du–Zhang v3, and Donninger–Wallauch v1. An initial Du–Zhang v2 retrieval is retained but superseded in the comparison by v3. The attempted Donninger–Wallauch v2 returned 404; the correct v1 succeeded, and the attempted Vienna institutional PDF mirror returned 502. Raw successful/error bytes, headers, extraction failure/fallback, and URLs remain in [primary evidence](../sources/i66_dispersive_equation_discovery/primary/). No content is imputed to a failed response.

## 3. The proposed theorem

**Theorem C66 (author proof; independent review pending).** Under B's stipulated premises, there are an odd p≥201, an integer `k=⌈3p/4⌉`, a source profile Q with `a=1/(p−1)`, and κ_*>0 with the following property. For every real `|κ|≤κ_*`, equation (4) has a nonempty open set of initial data in `H^k(T¹²;C)` such that each corresponding solution belongs to
`C([0,T);H^k)∩C¹([0,T);H^{k−2})` for some finite T>0, and for some x_* and phase θ,

\[
 (T-t)^a\left({T-t\over T}\right)^{-ib}e^{-i\theta}
 u(t,x_*+\sqrt{T-t}\,y)
 =c_\kappa(\sigma)\,[\chi(y/L)Q(y)+v(s,y)], \tag{5}
\]

where `s=log(T/(T−t))`, `σ=log(1/(T−t))=S+s`, `S=log(1/T)`, `L=e^{σ/2}`, and

\[
 c_\kappa(\sigma)=\left(1+{\kappa\over2a\sigma}\right)^{-a},
 \qquad \|v(s)\|_{Y_L}=O(\sigma^{-1}). \tag{6}
\]

Here (5) is interpreted on the expanding torus. In particular
`lim_{t↑T}(T−t)^a |u(t,x_*)|=|Q(0)|>0`, so continuous H^k extension through T is impossible. Constants may depend on the chosen p, Q, k and the eventual fixed neighborhood. No uniformity as p→∞, no assertion for arbitrary κ, and no first-order asymptotic coefficient for the error v is claimed.

The proof below closes the selected target. It does not nominate the supporting profile estimate, composition lemma, spectral identity, or recurrence bounds as separate findings.

## 4. Paying the nonpolynomial regularity interface

**A permissible p and k.** The source's stated `P=|Q|^{p−1}≤1` is not enough by itself to choose k<p. Its actual profile operations give the better fixed-power bound

\[
 \|P\|_\infty\le17/50 \quad\hbox{for all sufficiently small admissible }a.
 \tag{7}
\]

Here is the deduction. Use the source's fixed matching radius r_b. The limiting amplitude A_0 equals one in the core and is strictly decreasing outside it. Its formula
`w_0(r)=6r^{-11} A_0(r)^{-2}∫_0^r A_0(t)^2 t^{11}dt`
therefore gives `w_0(r)≥r/2`. Consequently the limiting coefficient
`V_0=b+r²/16−w_0²/4` is at most b. The matching disk has `b<0.335<0.34`. The stated compact C¹ convergence of μ_a,w_a gives uniform convergence of V_a on the fixed ball. This is uniform over the possibly nonunique matched profiles: otherwise choose a violating sequence and then a convergent subsequence of matching parameters. At r_b the exterior-pressure estimate gives P_a→0. If the maximum of A_a on the closed ball occurs inside, `−ΔA_a+P_aA_a=V_aA_a` and `ΔA_a≤0` give `P_a≤V_a` at that maximum; if it occurs at the boundary its pressure is already small. The source's uniform exterior pressure bound controls all r≥r_b. These observations prove (7), including the origin by smoothness.

For an odd p≥201 sufficiently large for (7) and the source spectral classification, set k=⌈3p/4⌉. Then
`k>8`, `k>7−2a+(17/25)p`, and `k+3<p`.
The actual linear choice in B is `k>max{8,6−2a+2B+1}`, with `B=p||P||∞`; (7) pays it. All fixed-order source estimates remain available at this k. This is a choice inside B's proof, not a claim that the source's initially unspecified k automatically satisfies k<p.

**Uniform composition lemma.** For the fixed k above, let H:R²→R² be C^{k+3} on a fixed disk, H(0)=0, with derivative bounds at most h. For inputs of Y_L norm bounded by R and values in that disk, uniformly for L≥1,

\[
 \|H(f)\|_{Y_L}\le C_R h\|f\|_{Y_L},\qquad
 \|H(f)-H(g)\|_{Y_L}\le C_R h\|f-g\|_{Y_L}. \tag{8}
\]

One proof, including the low-frequency issue, is as follows. Use smooth periodic Littlewood–Paley cutoffs at scales `2^j≥L^{-1}`, with the remaining lowest block containing the constant mode. Their kernels are periodizations of fixed Schwartz kernels and have uniform L¹ bounds. For the telescoping difference
`H(S_{j+1}f)−H(S_j f)=Δ_j f∫_0^1 DH(S_j f+tΔ_j f)dt`,
derivatives of the coefficient up to m=k+1 have bounds `C_R h 2^{mj}` by the chain rule and Bernstein. Hence its projection to frequency 2^ℓ has L² bound
`C_R h 2^{-m(ℓ−j)_+}||Δ_j f||_2`.
After multiplication by `2^{sℓ}`, the relative-index kernels are summable for 0<s<m. Schur/Young summation gives the homogeneous estimates at s=s_0,k. For the lowest block, the same derivative argument and `|H(z)|≤h|z|` give the bound with initial weight L^{-s}; this retains the zero mode. In addition `L^{-s_0}||H(f)||_2≤hL^{-s_0}||f||_2`. The first component of (1) is uniformly equivalent to the squared sum of this term and the homogeneous s_0 norm. These facts prove the first inequality. Extend H by a fixed disk cutoff if necessary; the extension preserves H(0)=0 and the required bounds. To prove the second, write the difference as `(f−g)∫DH(g+t(f−g))dt`, split off the constant DH(0), apply the first inequality to `DH−DH(0)` (the extra derivative is available), and use the source's uniform algebra and embedding bounds. Approximate in Y_L by smooth Fourier truncations to justify the identities for general inputs. The same argument works on Y by starting the telescope at j→−∞; the low-frequency limit vanishes because s_0<6. No L² hypothesis on Q is introduced.

## 5. Construction I: normalize the amplitude, then use an anisotropic graph

Put `N(z)=|z|^{p−1}z`, and
`F(V)=iΔV−(D/2+a)V+ibV−iN(V)`.
The source similarity equation is `U_s=F(U)`. For (4) it becomes

\[
 U_s=F(U)-i\kappa {N(U)\over\log(2+e^{2a\sigma}|U|^2)}.
\]

Set `U=c_κ(σ)V`. Direct substitution gives

\[
 V_s=F(V)+H_{\sigma,\kappa}(V), \tag{9}
\]
\[
 H_{\sigma,\kappa}(z)=-{c'\over c}z
 -i\left[c^{p-1}\left(1+{\kappa\over\log(2+e^{2a\sigma}c^2|z|^2)}\right)-1\right]N(z).
 \tag{10}
\]

All logarithms are natural, the prime means d/dσ, and `dσ/ds=1`. Choose first a fixed bound `|κ|≤1/4` and σ sufficiently large depending on a. Then c,c^{-1} are bounded and

\[
 {c'\over c}={\kappa\over2\sigma^2(1+\kappa/(2a\sigma))},\quad
 c^{p-1}=(1+\kappa/(2a\sigma))^{-1}. \tag{11}
\]

For every fixed disk and every integer `0≤m≤k+3<p`,

\[
 H_{\sigma,\kappa}(0)=0,\qquad
 \|H_{\sigma,\kappa}\|_{C^{k+3}}\le C|\kappa|\sigma^{-2}. \tag{12}
\]

Here are the uniformity details, including z near zero. Denote the logarithm in (10) by ℓ. The bracket in that equation is **exactly**
`κ(1+κ/(2aσ))^{-1}(ℓ^{-1}−(2aσ)^{-1})`.
For `r=|z|≥e^{-aσ/2}`, ℓ≥aσ−C, and
`|ℓ−2aσ|≤C(1+|log r|)` on the fixed disk. Its jth spatial derivatives have bounds `C_j r^{-j}`. Differentiating the reciprocal difference and the homogeneous polynomial N gives
`C_m |κ|σ^{-2} r^{p−m}(1+|log r|)`.
These are bounded at zero because m<p. On `0<r<e^{-aσ/2}`, use instead that all Euler derivatives of `q↦1/log(2+q²)` are bounded, and that its ordinary derivatives times q^j are bounded as well. With `q=e^{aσ}cr`, each product derivative has bound `C_m|κ| r^{p−m}`; this is exponentially small in σ and hence at most `C_m|κ|σ^{-2}`. At z=0 the same bounds follow by smoothness of N divided by a positive smooth denominator. The linear term in (10) is covered by (11). Differentiation at the boundary between the two regions is not used; these are two bounds for the same smooth function. This proves (12).

Combine (8), (12), and the uniformly bounded source cutoff profile `Q_σ=χ(y/e^{σ/2})Q`. Thus the new forcing and its Lipschitz constant on a fixed perturbation ball in Y_L are O(|κ|σ^{-2}), uniformly in the expanding torus. This pays the full spatial tail and zero-mode interface, not just the forcing on a fixed core. It avoids the invalid assertion that a nonpolynomial Nemytskii map has uniform arbitrarily high derivatives under this scaling.

### 5.1 Step maps and the special phase column

Take M sufficiently large for (2), and write `σ_n=S+nM`, `L_n=e^{σ_n/2}`, `d_n=e^{-(1+a/2)σ_n}`. The source cutoff defect is O(d_n). The source's fixed-slab integral-equation argument, now using (8)–(12), yields

\[
 v_{n+1}=\mathcal F_n v_n+h_n(v_n),\qquad
 \|h_n(0)\|\le C_M(|\kappa|\sigma_n^{-2}+d_n), \tag{13}
\]
\[
 \operatorname{Lip}_{\|v\|\le d}h_n
 \le C_M(d+|\kappa|\sigma_n^{-2}+d_n). \tag{14}
\]

The between-step norm is bounded by `C_M(||v_n||+|κ|σ_n^{-2}+d_n)`. To verify (13)–(14), on a fixed slab the free propagator and source potential are uniformly bounded. The source polynomial remainder is quadratic. Equation (12) adds a bounded Lipschitz forcing with the displayed size. Contraction on finitely many short subslabs, then Gronwall for solutions and their differences, gives (13); subtracting the linear difference evolution gives (14). Since σ changes by only M, all polynomial bounds have fixed comparison constants. Only derivatives up to the fixed k+3 enter. This also gives uniqueness and joint strong continuity in κ, starting scale, and the input by smooth approximation, exactly as in the source; operator-norm continuity in Schrödinger time is not asserted.

Separate the phase column `E_n^0=iQ_{σ_n}` from the other thirteen columns `E_n^+`. There is a quantitative improvement, needed only for this one column:

\[
 \|\mathcal F_n E_n^0-E_{n+1}^0\|\le C_M d_n. \tag{15}
\]

Indeed gauge covariance gives `DF(Q_σ)(iQ_σ)=iF(Q_σ)`. Multiplying the source cutoff residual `∂_sQ_σ−F(Q_σ)` by i shows that `iQ_σ` solves the source linearized equation up to forcing of norm O(d_n). Duhamel on a fixed slab proves (15). Applying the uniformly bounded projections and coordinates gives both
`||(I−P_{n+1})F_n E_n^0||≤C_Md_n`
and `||e_n E_n^0||≤C_Md_n`. This does **not** assign a rate to (2) on arbitrary inputs.

### 5.2 A polynomially decaying graph, with all summation losses paid

Write
`v_n=w_n+E_n^+u_n^++E_n^0u_n^0`, with `π_nw_n=0`.
The diagonal multiplier on u^+ is `D_+=diag(e^{M/2},…,e^{M/2},e^M)`; on u^0 it is 1. The source recursions hold with h_n from (13). Define a Lyapunov–Perron map by the forward w recurrence, prescribing w_0, and the backward coordinate sums

\[
 u_n^+=-\sum_{j=n}^\infty D_+^{n-j-1}
       [e_jv_j+\pi_{j+1}h_j(v_j)]_+,
\]
\[
 u_n^0=-\sum_{j=n}^\infty
       [e_jv_j+\pi_{j+1}h_j(v_j)]_0. \tag{16}
\]

Use the norm

\[
 \|(w,u^+,u^0)\|_{\mathcal X_S}
 =\sup_{n\ge0}\{\sigma_n^2(\|w_n\|+K|u_n^+|)+K\sigma_n|u_n^0|\}. \tag{17}
\]

This is a Banach space of sequences in the indicated closed subspaces; comparisons for varying S use physical-torus dilation. The elementary summation bounds used below are

\[
 \sigma_n\sum_{j\ge n}\sigma_j^{-2}\le M^{-1}+S^{-1},\quad
 \sigma_n^2\sum_{j\ge n}\rho^{j-n}\sigma_j^{-2}\le(1-\rho)^{-1}
 \quad(0<\rho<1). \tag{18}
\]

The first is the decreasing-function integral test, including the first term; the second uses σ_j≥σ_n. Exponentially decaying d_j satisfies the analogous bounds with an extra factor tending to zero as S→∞, even after multiplication by any of the displayed powers of σ. Also `(σ_{n+1}/σ_n)^2≤2` once S is large.

For completeness the contraction budget is explicit in its order of choices. Fix M; choose K large enough that the forward terms from `A_nw_n` and `B_n^+u_n^+` cost at most `2(1/8+C_M/K)<1/2`. By (2), choose the starting scale large enough that `sup_n||e_n||≤ε`, with ε as small as needed after K is fixed. The remaining linear forward phase term has norm at most `C_M sup_n σ_n d_n/K` by (15). The coordinate sums applied to e_n(w_n+E_n^+u_n^+) cost at most C_{M,K}ε, using (18); their application to the phase column costs a quantity tending to zero with S by (15). Thus all linear costs other than the forward contraction can be made less than 1/8. No series of the form `Σ ε_j/σ_j` occurs: the only σ_j^{-1} input is the special phase column, whose defect has the exponential bound (15).

On a ball of radius δ in (17), `||v_n||≤Cδ/σ_n` and the same bound holds for differences with δ replaced by their sequence distance. Equation (14) therefore bounds a difference of h_n by

`C_M[δ σ_n^{-2}+|κ|σ_n^{-3}+d_n σ_n^{-1}] · distance`.

Forward weights, the geometric positive-coordinate sum, and the neutral sum (18) make their total Lipschitz cost at most
`C_{M,K}(δ+|κ|/S+o_{S→∞}(1))`.
Choose δ small and then S large so this is below 1/8 uniformly for |κ|≤1/4. Finally the zero-input forcing in (13) has sequence-image norm at most `C_{M,K}(|κ|+S²e^{-(1+a/2)S})`. Reduce κ_* and enlarge S so it is less than δ/4; require `S²||w_0||≤cδ`, with c sufficiently small, to put the prescribed zeroth stable coordinate in the invariant ball. The complete map is a strict contraction there. This proves existence and uniqueness of the sequence solving the exact recursions, since consecutive sums in (16) telescope.

In particular there is a continuous graph `G_{S,κ}(w_0)=(u_0^0,u_0^+)` on that ball. The contraction estimate gives

\[
 |G_{S,\kappa}(w_0)|
 \le C\{S\|w_0\|+|\kappa|/S+S e^{-(1+a/2)S}\}. \tag{19}
\]

The sharper component bounds are `w_n,u_n^+=O(σ_n^{-2})` and `u_n^0=O(σ_n^{-1})`; fixed-slab estimates give (6) at every time. Joint continuity follows by iteration starting at zero: every fixed coordinate is continuous on finite slabs, and the tails in (16) are uniform by (18) on compact ranges of S. Uniform contraction then passes continuity to the fixed point. No differentiability of the graph is required.

### 5.3 Recover an open physical neighborhood

Choose S_0 large, put T_0=e^{-S_0}, and use the smooth periodic reference datum

\[
 u_{\mathrm{ref},\kappa}(x)=T_0^{-a}c_\kappa(S_0)\chi(x)Q(x/\sqrt{T_0}).
\]

For parameters `d'=(θ,ζ,β)`, set `T=T_0e^β`, `x_*=√T_0 ζ`, `S=S_0−β`, and L=e^{S/2}. This is an exact change of variables separately for each T, with (9)'s σ-dependent coefficient retained; it does not invoke a scaling symmetry of the modified equation. The starting perturbation for (9) is
`v_0=e^{-iθ} T^a c_κ(S)^{-1} u_in(x_*+√T y)−χ(y/L)Q(y)`.
The source parameter expansion now has precisely one extra scalar ratio `c_κ(S_0)/c_κ(S)`. Equations (11) and the source symbol bounds, including two parameter derivatives, give

\[
 v_0=E_L C d'+r,\qquad C d'=(-\theta+b\beta,\zeta,\beta),
\]
\[
 \|r\|\le C\{\rho^2+\sqrt{T_0}\rho+
       |\kappa|\rho/S_0^2+\varepsilon_{\rm data}\}
       \quad (|d'|\le\rho), \tag{20}
\]

where `ε_data=C(T_0)||u_in−u_ref,κ||_{H^k}` uniformly on the fixed parameter ball and |κ|≤κ_*. The nearby H^k data are only translated/dilated continuously, never differentiated in the parameters. Constants can be made uniform for `|S−S_0|≤ρ≤1`. The source cutoff remains strictly inside a physical cell.

Use the continuous degree map
`Φ(d')=π_Lv_0−G_{S,κ}((I−P_L)v_0)`.
Since `π_LE_L=I` and `(I−P_L)E_L=0` exactly, (19)–(20) give

\[
 |\Phi(d')-Cd'|\le C\{S_0\rho^2+S_0\sqrt{T_0}\rho+
 |\kappa|\rho/S_0+S_0\varepsilon_{\rm data}
 +|\kappa|/S_0+S_0e^{-(1+a/2)S_0}\}. \tag{21}
\]

Here is a compatible choice, rather than an implicit circular smallness requirement. After the graph constants are fixed, choose a small number d>0 and put `ρ=d/S_0`. Take d small enough that the first term in (21), divided by ρ, is less than one sixth the smallest singular value of C, and so that (20)'s stable argument fits the graph ball. Then take S_0 sufficiently large that the two exponential terms divided by ρ are correspondingly small and all previous step conditions hold. Reduce κ_* sufficiently that `Cκ_*/d` is small; this also controls `Cκ_*/S_0` and the graph's forcing budget. Finally choose a **positive** physical H^k radius making the data term small. The sum in (21) is then strictly less than `|Cd'|` on `|d'|=ρ`. The same bounds keep the stable argument inside `S²||w_0||≤cδ` throughout the ball: its leading size is O(d²/S_0²), and the data radius can be decreased further. This verifies the graph-domain condition, not just the boundary inequality.

The straight-line homotopy has no boundary zero, so degree supplies parameters for every datum in this open ball. At the resulting zero the normalized solution lies on the graph. Finite similarity slabs correspond to finite physical H^k intervals; (8), or the ordinary inhomogeneous version of its proof, gives local well-posedness and uniqueness for the smooth nonpolynomial nonlinearity. The construction continues through every t<T. Equation (6) and the uniform Y_L→L∞ embedding give (5)'s center limit, since χ(0)=1, c_κ(σ)→1 and Q(0)≠0. H^k→C⁰ precludes extension through T. This proves C66. ∎

## 6. Construction II: a spectral correction and its separate limitation

The second construction attacks the same equation without first normalizing its entire nonlinear map. It constructs a higher-order approximate orbit by solving a forced linear equation on the source spectral complement. It is useful as an independent check of the leading cancellation and of what the first construction actually pays.

Let A=DF(Q). The profile belongs to the generator domain: cutoff approximation and the source symbol estimates make both Q's tail and the commutator with the cutoff tend to zero in Y. Homogeneity and F(Q)=0 give

\[
 A Q=-i(p-1)N(Q)=-iN(Q)/a. \tag{22}
\]

If π_0 is the phase row, `π_0 A=0` on the generator domain; hence `π_0(iN(Q))=0`. Thus the leading forcing is **not** a nonzero neutral resonance. A naive claim of an unavoidable logarithmic phase drift at order 1/σ would be wrong.

Set `q_1=−κQ/2`. On each fixed compact ball the expansion of the unnormalized generator has forcing `f_1/σ`, where `f_1=−iκN(Q)/(2a)`, and (22) gives `Aq_1+f_1=0`. Define

\[
 g_2=\tfrac12D^2F(Q)[q_1,q_1]
       -{i\kappa\over2a}DN(Q)q_1
       +{i\kappa\over4a^2}N(Q)\log|Q|^2,
 \quad H_2=-q_1-g_2. \tag{23}
\]

All terms belong to Y: logarithms add at most a log factor to the integrable dyadic symbol tails, and N is polynomial. A has a bounded inverse R on the complement of the phase line. On its stable subspace it is
`R h=−∫_0^∞ S(t)h dt`; on the thirteen positive symmetry coordinates it is the inverse diagonal multiplier Λ_+^{-1}. These integrals converge in Y, belong to the generator domain by semigroup integration, and invert A. Take

\[
 \gamma=-\pi_0H_2,\qquad
 q_2=R(H_2-\pi_0(H_2)iQ),\qquad \vartheta(\sigma)=-\gamma/\sigma.
\]

Then `V_app=e^{iϑ(σ)}(Q+q_1/σ+q_2/σ²)` has residual O_{R,j}(σ^{-3}) on every fixed ball in every fixed C^j norm. To see this, q_2 is locally smooth by elliptic regularity applied to `Aq_2=H_2−π_0(H_2)iQ`; bootstrap on nested compact balls handles the smooth drift and potential. Q is bounded away from zero on each such ball. Taylor expansion is therefore uniform there. The coefficient at σ^{-1} is (22); the coefficient at σ^{-2} in `∂_sV_app−F_σ(V_app)` is
`−q_1+iγQ−Aq_2−g_2=0` by (23). The regularizing 2 inside the logarithm contributes only O_{R,j}(e^{-2aσ}). All other remainder terms are O_{R,j}(σ^{-3}). This proves the stated compact approximation.

This construction alone does **not** complete C66. Membership q_2∈Y and qualitative cutoff convergence provide no rate at radius e^{σ/2}, and do not justify Taylor expansion where q_2 might dominate the small tail of Q. General Y functions can have arbitrarily slowly vanishing cutoff tails. One would need a weighted resolvent estimate preserving the log-symbol tail and a global nonlinear remainder estimate before using this construction on expanding tori. Construction I supplies a different solution to these interfaces through the uniform composition bound (12); it does not silently assume that missing resolvent theorem. The two approaches agree on q_1, as they must, but differ after it: global nonlinear conjugation and an anisotropic graph versus a resolvent-corrected approximate orbit.

## 7. Attacks on the vulnerable steps and finite validation

Several invalid shortcuts were explicitly tested and excluded.

1. With raw logarithmic forcing of order 1/σ, the source's exponential sequence weight diverges. Even after normalization, σ^{-2} is not controlled by that weight. A finite numerical plateau is not evidence of exponential decay.
2. A single polynomial weight σ² on all coordinates loses one power in the phase backward sum. Conversely, using σ on all coordinates and only `||e_n||→0` can require the divergent series `Σ1/[n log(n+2)]`. This is a **counterexample to that abstract estimate**, not to the source defect or equation (4). Equations (15), (17), and (18) are the paid repair.
3. The source's bound P≤1 does not pay k<p. The maximum-principle deduction (7) is needed before the nonpolynomial derivative estimate; it cannot be postponed or replaced by numerical pressure samples.
4. An expansion of the logarithm on a fixed core is not uniform to the cutoff radius, and it is not uniform near zero of arbitrary perturbations. The two-region derivative proof of (12), followed by (8), addresses both cases.
5. A leading O(1/σ) term is not automatically a phase resonance. Equation (22) is an exact cancellation, checked independently of the normalization formula.

The [diagnostic program](../experiments/i66_dispersive_equation_discovery/diagnostics.py) contains exact-rational checks of admissible p/k inequalities, binomial normalization coefficients, the homogeneity cancellation, and the discrete weighted sums; finite decimal-jet checks inspect the normalized nonlinearity at core, transition, and small-amplitude points. It also records failures of the two scalar weighting shortcuts. These finite checks test algebra, normalization, and summation edges. They do not prove the PDE theorem or a universal estimate.

The [read-only verifier](../experiments/i66_dispersive_equation_discovery/verify.py) checks the immutable input snapshots, selected Git blobs, entire 9,340-file corpus manifest, line-multiset searches, source/primary passage hashes, primary response bytes and text extractions, sealed artifacts, and fresh diagnostic reproduction. It treats changes to the four shared ledgers as informational and never refreshes an old seal. Run from the project root:

```bash
python frontier/experiments/i66_dispersive_equation_discovery/verify.py
```

An evidence PASS means that this recorded package reproduces. The analytic proof claim is the author's written Sections 4–5, not the verifier output. There has been no independent review within I66.

## 8. Contribution boundary and handoff

The proposed contribution is robustness of an **open periodic defocusing blowup mechanism under an asymptotically same-order, nonhomogeneous logarithmic nonlinearity**. Its mathematical usefulness is that the singularity mechanism survives a change of constitutive law that is not exponentially negligible in similarity coordinates before normalization. It does not merely embed the old solutions in a larger space or randomize an already open event.

The source and primary antecedents own the profile, spectrum, expanding-torus contraction, polynomial stability, degree mechanism, and general stable-manifold methodology. I66's proposed bridge consists of their compatible use with (7), the exact normalization and all-input estimate (12), the quantitatively controlled phase column (15), and the differently weighted graph and degree budget (17)–(21). Whether this combined operation meets the project's **substantial** threshold is specifically reserved for an independent significance review. No MathDB score was invented or used, and exact-phrase search is not offered as proof of novelty.

The parent should commission a fresh full-proof review and a separate contribution review of C66 as written, including the fixed choice of k, homogeneous composition argument, phase-column identity, polynomial graph constants, and physical degree radius. The unproved weighted-resolvent extension of Construction II and the exceptional-set target (3) remain outside the theorem. No remaining interface from Construction II is needed for Construction I's proof. No new R-number should be assigned before those independent gates.
