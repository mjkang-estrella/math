# I228 — independent proof gate for I224

## Partial review (before completion of source-contract checking)

The gate is pending. I have read the complete submitted analytic argument, AGENTS.md, sources/upstream.json, and the pinned section 02-flatness.tex. All pinned results and lower operations are stipulated; this review concerns their applicability only. No other active review has been read.

The lift and quadratic-cone calculation have the required signs. The source three-point operation defines its third gradient as -2p0 and evaluates its third matrix on p0. For the enlarged class the third lower bound is indeed -2F0|p0|², after dividing the -2p0 inequality by four. Thus the candidate's bounded forcing correction survives that otherwise delicate normalization. The source penalty Hessian is independent of the equation and its negative r^(-1/2) term dominates the resulting bounded error.

Remaining checks include the full reduction/cylinder contracts, the simultaneous choice of slow tangent scales, all-center/all-scale compactness, and the final strict comparison. This partial record is not a proof approval or a contribution verdict.

## Final independent verdict

**PASS for both Theorem R and Theorem S, relative to the stipulated pinned theorems and lower operations.** I found no substantive unpaid estimate in the complete I224 candidate. The enlarged inequality class, forced three-point estimate, strengthened bad-scale selection, exact homogeneous limiting equation, and derivative extraction are compatible. The value comparison in S has the correct signs and does not require differentiability of the forced solution. This verdict does not certify literature novelty or authorize an accepted-count change.

This is an independent check of the actual candidate and actual source contracts, not an acceptance of the phrase “same argument.” The expansions below specify how the source operations apply. The initial partial review above was written before reading the complete reduction source; this final verdict supersedes its pending status.

### 1. Exact scope of the conclusions

For each integer d≥3, R provides dimension-only a_d∈(0,1/3] and A_d<∞ such that every bounded u∈C(B1) solving the normalized equation with bounded continuous f satisfies

    ||Du||∞,B1/2 + [Du]C^(0,a_d)(B1/2)
      ≤ A_d (osc_B1 u + ||f||∞,B1).

The critical-jet convention is -λ_max(X)≤f for an upper test with p=0 and -λ_min(X)≥f for a lower test with p=0. No existence or uniqueness assertion for arbitrary signed f is needed.

For S, v∈C(cl B1) is infinity-harmonic, 0≤v≤1, and inf_B1|Dv|≥m with 0<m≤1. For 0<ε≤min(1,m²), every existing u∈C(cl B1) with the same boundary values and continuous |f|≤ε has

    ||u-v||∞,B1 ≤ κ,
    ||Du-Dv||∞,B1/2 ≤ C_d κ^(a_d/(1+a_d)),   κ=ε/m².

The nonvanishing condition is on all of B1 for v. There is no assumed gradient bound or differentiability for u. The proof supplies local C¹,a_d regularity at every interior point through R and fixed-radius coverings.

### 2. Source interface actually checked

I read in full the pinned manuscript's sections 01-introduction.tex, 02-flatness.tex and 03-reduction.tex in the reused corpus. Their Git blob hashes were independently matched to sources/preprints-tree.json. The relevant contracts are:

* `thm:main` and `cor:interior-c1`: exact infinity-harmonic functions; used for the comparator v, never substituted for forced regularity.
* `lem:cone-slopes`, `prop:affine-blowups`: source monotonicity and the fixed-center affine-tangent argument. For forced functions the candidate proves the perturbed slope inequality first; the source's terminal argument is then used only for an exact homogeneous limit with constant origin slopes.
* `lem:sum-rule`: continuous functions, an interior product maximum, a C² penalty, closed superjets, and diag(X_j)≤A+ηA². This operation itself assumes no PDE.
* `prop:three-point`: its original theorem assumes exact infinity-harmonicity. The candidate does not meet that theorem verbatim. Instead it reuses its equation-free localization/Hessian calculation and replaces each of its three jet inequalities; these replacements are checked below.
* `lem:family-flatness`: the needed inputs are uniform bounds/Lipschitz control, closure, affine fixed-center tangents and the all-separation three-point estimate. The candidate establishes each for the enlarged class.
* `lem:bad-scales`: the relevant selection and boundary-distance estimates use the scalar modulus b and goodness definition. The stronger selection remains valid.
* `lem:cylinder-comparison`: same function, same parameter θ², slopes in [c_*,C_*], concentric radii H≤H'≤2H or equal radii with axial/transverse center offsets ≤H/4, θH/4. No equation appears in this contract or its proof.
* `prop:nonaffine-limit`: its source statement is attached to the homogeneous family. Its proof separates geometric compactness and nonaffinity from one PDE-stability passage. All geometric hypotheses are supplied here; that PDE passage is replaced by the calculated vanishing-forcing passage.
* `thm:liouville`: every m≥1, a continuous entire solution of D²V[(D_xV,1)]=0, and one finite constant C0 for fits at every center and every R>0 on |ℓ|≤R, |h-pℓ|≤R. It imposes no differentiability hypothesis on V. Here m=d and C0=256.
* The final part of section 03 extracts actual derivatives from the power-law cylinder fits. It uses only those fits and the common Lipschitz bound.

I did not audit these pinned results. Sections 04–08 and their internal Liouville proof are not needed to check this interface and were not read. No other active review was opened.

### 3. Closure, Lipschitz control, slopes and tangent functions

Write I_F for the pair of test inequalities

    X[p] ≥ -F|p|² at upper tests,
    X[p] ≤  F|p|² at lower tests.

Both operators are continuous in (p,X), including p=0. Strict-contact stability therefore proves closure under locally uniform limits. The algebraic lift identity, normalization at zero, and oscillation bound also pass to limits. Closure does not assume a derivative exists.

For an upper test φ of U(y,t)=w(y)+t one has φ_t=1. If p=D_yφ≠0, the affine graph with Dℓ·p=1 makes φ(y,ℓ(y))-ℓ(y) an upper test for w and gives

    D²[φ(y,ℓ(y))-ℓ(y)][p] = D²φ[(p,1)].

The normalized equation bounds this below by -F|p|², which is at least -F|(p,1)|². If p=0, vertical restriction gives φ_tt≥0 and the required bound. Lower tests give the other inequality. Thus every normalized solution enters I_F after lifting; the full test gradient of a lift is never zero. This does not replace the original normalized convention with a different equation.

For the radial upper barrier C in I224 §3.2, C'=L_R^++F'(R-ρ)>0 for 0<ρ<R and C''=-F'. Thus Δ∞C=-F'|DC|²<-F|DC|². Its outer-boundary excess is F'R²/2≥0, and it agrees at the center. A positive maximum must be away from the center and boundary, where C is C², giving a contradiction. Division by the radius and F'↓F proves

    L_r^± ≤ L_R^± + FR.

Fixed-radius oscillation bounds give common local Lipschitz bounds, including a common bound on cl B7/8 for the normalized lifts. For each fixed center, the last display makes limsup_r L_r^± no larger than liminf_R L_R^±. Hence finite limits exist. At a positive maximizer h_r, the value at the old center is a permitted negative increment from z+h_r, so L_r^+(z)≤L_r^-(z+h_r). The FR error vanishes only after first using continuity at fixed R and then R↓0. This proves equality of the two limiting slopes. No uniform continuity of infinitesimal slopes is being assumed.

For H_j(X)=(W(z+r_jX)-W(z))/r_j the forcing constant is r_jF. Every locally uniform limit H is therefore an exact entire infinity-harmonic function. Its positive and negative origin slopes equal the same L_* at every radius. The source's final cone argument applies to this H: origin growth gives |H(X)|≤L_*|X|; comparisons with increasingly large balls give global L_*-Lipschitz control. Opposite extremizers saturate this bound, lie on opposite rays of a single line, and sending the two line endpoints to infinity forces H(X)=P·X. When L_*=0, H=0 directly. Thus these are actual linear, degree-one homogeneous tangent functions. Their slopes need not yet be unique, and the proof does not claim otherwise.

### 4. Forced three-point operation: all jet constants and signs

Let W_i satisfy I_Fi with F_i≤F0, have a common Lipschitz bound L, and converge uniformly to affine ℓ_i. Evaluations at ±e/2 bound q_i=Dℓ_i; hence W_i-ℓ_i have one common Lipschitz bound C. Negative midpoint defects are reduced to positive defects by changing both signs, which preserves I_Fi.

For a fixed violating δ>0 use exactly the source penalty, including the affine terms in Ψ. Its equation-free localization gives r≤8||W_i-ℓ_i||∞/(δν)→0, |h|≤2Cr², and interior maximizing triples after choosing B_out>(C+3C²/2)/ν. The cutoff B and its first two derivatives are fixed in i. With e=(x-y)/r and f0(r)=r-r^(3/2)/8, the jet vectors are

    p1=q_i+f0 DB/2-h/r²+a e,
    p2=q_i+f0 DB/2-h/r²-a e,
    p0=q_i-h/r²,
    a=B f0'-2|h|²/r³ ≥ δ/4

for all sufficiently large i. These vectors are uniformly bounded. Crucially the third superjet, for -2W_i, has gradient -2p0, not p0.

An upper jet (p,X) for -2W corresponds to the lower jet (-p/2,-X/2) for W. Its inequality gives X[p]≥-2F0|p|². At p=-2p0, division by four gives X3[p0]≥-2F0|p0|². The other two bounds are X1[p1]≥-F0|p1|² and X2[p2]≥-F0|p2|². This also holds if any vector vanishes; no normalization by its length is performed.

Apply the matrix inequality to σ=(p1,p2,p0). At each fixed maximizing triple let η↓0; the matrices may depend on η, but their uniform scalar lower bound does not. It follows that

    A[σ] ≥ -F0(|p1|²+|p2|²+2|p0|²).

The right side is bounded independently of i. The source's second variation gives r'=2a, r''=0, c'=O(1), h'=-(f0/2)DB=O(r). The |h|²/r² term has bounded second variation, as do the cutoff cross terms; the remaining term is

    B f0''(r)(2a)² = -3B a²/(8√r).

It tends to -∞. This contradicts the bounded lower bound and proves T for the enlarged class, uniformly over every nonzero endpoint separation. No derivative of f or of W_i was inserted. Subtracting ℓ_i was used for the maximum, not as an assertion that the PDE is invariant under affine subtraction.

### 5. Moving centers and tiny separations

Uniform bounds on cl B7/8 give a uniformly convergent subsequence U_i→U0 there and z_i→z_*∈cl B3/4. This limit point is interior to B7/8 even when D(z_i)→0. Choose R_i↓0 dominating r_i, |z_i-z_*| and the uniform error. Such a choice is compatible with affine tangents because every chosen R_i sequence has an affine-tangent subsequence; no preselected tangent scale has to dominate the errors.

The R_i-blowups converge uniformly on B1 to that affine function, are uniformly Lipschitz, and satisfy I_Ri. T applies with a common bounded forcing constant. For H,K∈cl B2, the points z_i+r_iH and z_i+r_iK lie in B_(R_i/4)(z_*) eventually. Substitution in T and division by r_i gives their midpoint defect bounded by ε_i|H-K|, with ε_i→0. The r_i-blowups have an affine limit on B2 by continuity and midpoint subdivision. Exact vertical increments give its slope P·e_t=1.

Uniform error <δ on B2 then provides a fit for the actual allegedly bad λ_i≥δ on its cylinder, since that cylinder lies in B2. I224's phrase “bad delta-cylinder” should be read this way: δ is the error threshold, while the failed parameter can be λ_i. This is a wording clarification, not a missing mathematical step. No monotonicity of goodness in λ is required.

### 6. Strengthened selection and geometric compactness

Failure of every power bound makes b(s)s^(-γ) unbounded near zero for each γ>0. For γ_i↓0 with γ_i≤1/2, take a factor-two approximate maximum on a truncated interval large enough that its value exceeds both i and the supremum on [1/i,1/8]. This gives the stated running-maximum inequality, s_i<1/i, and b(s_i)/s_i^γi≥i. Approximate suprema then give a bad λ_i with b(s_i)/4<λ_i≤b(s_i). In particular λ_i→0 and

    r_i/λ_i ≤ 4D(z_i)s_i/b(s_i)
             ≤ 3s_i^(1-γ_i)/i → 0.

For fixed M≥2, D(z)≥D(z_i)/2 at |z-z_i|≤Mr_i eventually. Every r≤Mr_i is admissible, and

    β_Ui(z,r) ≤ b(2Ms_i)
       ≤2b(s_i)(2M)^γi <32λ_i<1.

Thus Λλ_i is good for all these centers and all these radii, with Λ=32. The index threshold may depend on M; the parameter Λ does not. Strengthening the maximum did not discard the small-radius fits.

Here is the full geometric input to the reused compactness operation. For θ_i²=Λλ_i, the lift's exact vertical increment gives 1/2≤|P|≤L+1 for every relevant fit eventually. At the base center, compare successively doubled radii from r_i to Rr_i. The source cylinder lemma yields O(θ_i(1+log R)) direction error and O(θ_i²(1+log R)) norm error. Given a normalized box of size K, choose fixed R≫K(1+log R); the box then lies in the enclosing fit with the lemma's quarter-radius margins. Compare fits at each box center at radius Rr_i with that enclosing fit, then use a finite sequence of doublings/halvings to Sr_i for any fixed S>0. These operations satisfy exactly the two center/radius alternatives of the source lemma. The number of comparisons depends on K,S, not i.

After rotation and normalization this gives |p_i'|+|q_i'|≤C_(K,S). The cylinder decomposition in the source gives the contained domain

    |ℓ|≤S/2,   |h-p_i'ℓ/(1+λ_iq_i')|≤S

and error ≤ΛS/c_i. A large enclosing fit bounds the functions on each box. For equicontinuity, first choose S so 2ΛS is small, then choose the increment small relative to the finite bound C_(K,S). There is no need for C_(K,S) to remain bounded as S↓0. This proves locally uniform subsequential convergence on the exhausted entire space without any PDE regularity estimate. The source's geometric operation is therefore applicable, not merely asserted applicable.

### 7. Actual limiting PDE, full Liouville fits and nonaffinity

The rescaling has physical gradient c_i(√λ_i D_xφ,1+λ_iφ_t) and Hessian

    (c_i/r_i) [ D_xx²φ       √λ_i D_xtφ
                √λ_i D_txφ  λ_i φ_tt ].

Its infinity Laplacian is (λ_ic_i³/r_i)D²φ[(D_xφ,1+λ_iφ_t)]. Thus upper tests satisfy precisely

    D²φ[(D_xφ,1+λ_iφ_t)]
      ≥ -(r_i/(c_iλ_i))
         (λ_i|D_xφ|²+(1+λ_iφ_t)²),

with the opposite lower bound for lower tests. Because c_i≥1/2 and r_i/λ_i→0, the residual tends to zero uniformly on compact jet sets. Strict-contact stability gives the exact homogeneous equation D²V[(D_xV,1)]=0. The limit is not a solution with a retained forcing or a merely formal linearization.

For every fixed center and R>0, use the geometric fit at S=4R and extract its bounded coefficients along a further subsequence. The shears converge to p; the larger contained domain has strict margins around |ℓ|≤R, |h-pℓ|≤R. Local uniform convergence gives the required estimate with one C0=8Λ=256. Set a=q+|p|²/2 to match the source notation. The coefficient subsequence may depend on the center and radius because V has already been fixed. This establishes the full quantifiers in `thm:liouville`.

If V=p·x+qt, the nonzero physical slopes c_i(√λ_i p,1+λ_iq) have λ_i-cylinders inside one fixed normalized box. The residual there is r_ic_iλ_i(V_i-p·x-qt)=o(r_iλ_i), so λ_i is good eventually. This contradicts its selection. This last step uses neither an equation nor derivatives. The exact Liouville theorem contradicts the resulting nonaffine entire limit and hence proves a dimension-only power bound for b.

### 8. Derivatives at every point and the estimate in R

Choose A strictly larger than the power-law constant times (1/4)^(-γ); this strictness puts Ar^γ above β even though goodness need not be monotone. The same small r0 works for every center in cl B1/2. On r_j=2^(-j)r0 the inscribed radii are ρ_j=√A r_j^(1+γ/2). Subtracting two fits on B_ρ(j+1) bounds |P_j-P_(j+1)| by Cr_j^(γ/2). Its geometric tail converges uniformly.

For ρ_(j+1)<|h|≤ρ_j, divide the fit error by |h|, using the lower bound ρ_(j+1), and add the slope tail. This gives a uniform remainder C|h|^(1+a), a=γ/(2+γ). Hence DU exists at each center; no almost-everywhere differentiation theorem or inhomogeneous differentiability input is used. Comparing the two center expansions at z', z'+|z-z'|e gives the uniform Hölder gradient estimate. For larger separations use the Lipschitz bound. Reducing γ≤1 gives a≤1/3.

For M=osc u+||f||∞>0, division by M sends f to f/M and oscillation to at most one. This is valid also at zero-gradient tests because both Hessian eigenvalues scale by 1/M. Multiplication back proves R; M=0 means u is constant. Fixed-radius interior coverings give the B3/4 version and local C¹,a regularity. Spatial rescaling gives the stated forcing factor R||f||∞ in the radius-R gradient bound. These are dimension-only constants.

### 9. S: strict barriers, critical jets and interpolation

With κ=ε/m², T_+'=1+2κ(1-s)≥1 and T_-'=1+2κs≥1 on [0,1], while T_+''=-2κ and T_-''=2κ. Their boundary ordering and deviations ≤κ are correct. The comparator v is C¹ locally by the pinned homogeneous theorem; its nonvanishing gradient ensures every test for v or T_±(v) has nonzero gradient.

If φ is a lower test for T_+(v), apply the local increasing C² inverse of T_+ to φ. The resulting lower test for v has normalized infinity Laplacian ≤0. The test chain rule gives Δ∞^Nφ≤-2κ|Dv|²≤-2ε. Thus w_+ is a strict supersolution of -Δ∞^Nw≥2ε. Upper tests of w_- similarly give Δ∞^Nφ≥2κ|Dv|²≥2ε. C² regularity of v or w_± is unnecessary; the inverse is applied to the C² test.

If u-w_+ has positive maximum, the doubled-variable maxima approach the positive diagonal maximum set, which is a compact subset of B1 because the boundary difference is nonpositive. At such an interior maximum, differentiation only in the w_+ variable gives p=(x-y)/η=Dw_+(y), with |p|≥m. The theorem of sums for u and -w_+ gives X≤Y and thus X[p]≤Y[p]. The upper inequality for u and lower inequality for w_+ give

    X[p] ≥ -f(x)|p|² ≥ -ε|p|²
          > -2ε|p|² ≥ Y[p].

For the lower barrier, maximize w_-(x)-u(y)-|x-y|²/(2η). Now p=Dw_-(x), |p|≥m, and

    X[p] ≥ 2ε|p|² > ε|p|² ≥ Y[p],

where Y[p]≤-f(y)|p|²≤ε|p|². Both contradict X[p]≤Y[p]. Closed-jet inequalities are legitimate: the gradients stay nonzero and the operators and f are continuous there. No critical jet is discarded on assumption; the comparator's gradient excludes such a jet at these particular contacts. Elsewhere, R covers critical gradients of u through its lifted test argument. This proves w_-≤u≤w_+ and the value estimate without sign-changing uniqueness.

For ε=0 one can use any κ>0, with strict gap 2κm², and let κ↓0; this avoids relying on a non-strict doubled-variables argument. In the stated positive-ε theorem, κ≤1 gives osc u≤3. R on B3/4 gives common dimension-only C¹,a bounds. It applies to v as well: nonzero Dv makes the homogeneous unnormalized and normalized tests equivalent, or its exact lift directly belongs to the same inequality class. For x∈B1/2 and h≤1/8 the segment remains in B3/4, and

    |(Du-Dv)(x)·e| ≤ 2κ/h+C_d h^a.

Take h=min(1/8,κ^(1/(1+a))). When the minimum is capped, κ is bounded below by a fixed dimension-only threshold, so enlarging C_d gives the same κ^(a/(1+a)) estimate. Thus S follows with its stated quantifiers and no m-dependence outside κ.

### 10. Limitations, minor wording and provenance

The only corrections I would request are expository: §3.4 should call the eventual fitted parameter λ_i rather than δ, and §4's “smooth-composite variable” should say C¹ comparator variable. Neither changes the argument, adds a hypothesis, or changes this PASS verdict. The explicit expansions above supply the abbreviated source applications without discovering a new estimate or repairing a failed theorem.

The auxiliary p-energy route is not needed for R or S and remains unsubmitted. The supplied oscillatory examples are consistent with a≤1/3 and b≤1/4; they do not contradict either theorem. This gate does not extend the candidate to arbitrary-source existence, boundary gradient estimates, removal of inf|Dv|≥m, an optimal exponent, or p-to-infinity gradient convergence.

Exact source/read scopes and hashes are in `frontier/experiments/i228_forced_infinity_proof/input-authentication.json` and `frontier/sources/i228_forced_infinity_proof/literature.md`. Only the three authorized output paths were written. No research code, experiments, tests, snapshots, seals, shared edits, staging, commits, publication, subordinate agents or other active reviews were used. Hashing/extraction were provenance operations. Contribution remains a separate parent gate.
