# I273 analytic record

**Disposition: two unresolved targets; proved technical diagnostics only. No substantial theorem is nominated.** Every pinned theorem and lower operation used below is stipulated true. The arguments below validate new deductions, not upstream truth. Entropy is in nats, trace norm is unhalved, and Hilbert–Schmidt norm is denoted by ||·||₂. No numerical experiment is used.

## 1. Strongest target: uniform stability of GAD minimum-output states

Fix **0<γ<1 and 0<ν<1**. Put t=1−γ, b=γ(1−ν), c=γν, A=A_{γ,ν},

    e(p)=g(γν(1−ν)+γt(p−ν)²),    s₀=e(ν),
    φ_θ=√(1−ν)|0⟩+exp(iθ)√ν|1⟩,
    M_n={ |φ_{θ₁}⊗⋯⊗φ_{θ_n}⟩⟨φ_{θ₁}⊗⋯⊗φ_{θ_n}| : θ_j∈R }.

For an n-qubit density matrix ρ define

    D_n(ρ)=S(A^{⊗n}(ρ))−n s₀,
    d_n(ρ)=min_{P∈M_n} ||ρ−P||₁.

The source's arbitrary-partner minimum-output additivity gives D_n≥0 for all density matrices. The proposed substantive target is the following **pure-input** assertion:

    ∀γ,ν∈(0,1) ∃K(γ,ν)<∞ ∀n≥1 ∀unit ψ∈(C²)^{⊗n}:
        d_n(|ψ⟩⟨ψ|)² ≤ K(γ,ν) D_n(|ψ⟩⟨ψ|).               (U)

There is no dimension cap, product-input restriction, normalization of D_n by n, or claim of constants uniform at parameter endpoints. Mixed-input uniform stability would be a different stronger target. **(U) is not proved or refuted here.** Worldwide priority of (U) is not established by the bounded literature search.

This is not the old bosonic Target B: that target fixes the number of modes, imposes input entropy, centering and a mean-energy bound, and varies an unequal-temperature attenuator. Here the channel is a finite qubit channel, the input entropy is unconstrained, and the difficult quantifier is one constant for all block lengths. Nevertheless, the earlier uniqueness/inversion operations are already spent work; repeating them is not a contribution claim.

### Exact pinned dependencies

Family 276, `build/paper.tex`, `thm:main` and `cor:partner-additivity`; `sections/partners.tex`, `eq:minimum-output-value`; `sections/output.tex`, `lem:partner-branch`, `prop:pure-bound`, `cor:mixed-bound`; and `sections/thermal.tex`, `thm:thermal` and its complete two-factor mixture proof. The mixture uses the accepted zero-block theorem `thm:block`; it is not reaudited. `lem:e-convex` is stipulated. The scalar derivative and strengthened concavity estimates used next are independently derived below. The exact source minimum and its attaining latitude are already source conclusions, not findings.

## 2. Complete technical theorem: exact rigidity and an explicit nonuniform bound

Let s=γ(1−2ν) and

    L=[1+(1+s²)/t²]^{1/2},    h=ν(1−ν).

For every n≥1:

1. D_n(ρ)=0 **if and only if** ρ∈M_n, for arbitrary density matrices ρ.
2. For every pure ψ, with ρ_j its one-site marginal,

       D_n(ψ) ≥ 2γt Σ_j(p_j−ν)²,                           (P)
       D_n(ψ) ≥ 2bc L^{−2(n−1)} det ρ_j   for each j.       (B)

3. Every pure ψ satisfies d_n(ψ)²≤K_n D_n(ψ), where the explicit valid constant is

       K_n=8[(1+2/h)n L^{2(n−1)}/(bc)+1/(γt h)].           (N)

These statements are complete author-level deductions. Their exponential block-length cost is explicit. They are classified **TECHNICAL ONLY**: strict entropy concavity, channel injectivity and product-projector union bounds are routine lower operations. No independent reviewer acceptance is claimed.

### 2.1 Population cost

For 0<u<1/4, writing r=√(1−4u), direct differentiation gives

    g'(u)=2 atanh(r)/r ≥2.

The endpoint r=0 is interpreted by continuity. Thus

    e(p)−e(ν) ≥2γt(p−ν)².

The accepted population entropy inequality S(A^{⊗n}(ψ))≥Σ_j e(p_j) proves (P), also for mixed inputs. No strict-convexity inference from a merely qualitative lemma is needed.

### 2.2 A quantitative remainder in the actual thermal mixture

For states Q₀,Q₁ and 0≤w≤1,

    S(wQ₀+(1−w)Q₁)−wS(Q₀)−(1−w)S(Q₁)
        ≥(1/2)w(1−w)||Q₀−Q₁||₂².                         (C)

Proof: first regularize both states by mixing with εI/d. Along an affine state segment with difference H, the second derivative of entropy is

    −Σ_{a,b} |H_ab|² [log λ_a−log λ_b]/[λ_a−λ_b].

The diagonal coefficient is 1/λ_a. All eigenvalues are at most one, so every coefficient is at least one, by the mean-value theorem for log. Consequently f''≤−||H||₂². Integrating the scalar strong-concavity inequality gives (C); entropy continuity and ε↓0 remove regularization. The derivative follows by differentiating the resolvent integral for log, or by diagonalizing its Fréchet derivative. Ruskai–Yard §3.1 and Appendix B were read for this standard operation, but the displayed estimate is derived here and does not import their tensor-minimum theorem.

Split any pure input at site j, using x=1−p, y=p:

    ψ=√x|0⟩ψ₀+√y|1⟩ψ₁,   R_i=A^{⊗(n−1)}(|ψ_i⟩⟨ψ_i|).

For 0<p<1 the source thermal substitution is α=ax, β=by, η=cx, δ=dy, K=√t√xy. Let U₀=α+β, U₁=η+δ and u=U₀U₁−K²>0. Its endpoint mixture has weights

    w₁=βU₁/u,    w₂=ηU₀/u,

and its two states T₁,T₂ have the **same cross block**. Their difference is exactly

    T₁−T₂=diag((u/U₁)(R₁−R₀), −(u/U₀)(R₁−R₀)).

Applying (C) and the source endpoint entropy lower bounds gives an addition to the branch inequality of at least

    (bcxy/2)(U₀/U₁+U₁/U₀)||R₁−R₀||₂²
        ≥bcxy||R₁−R₀||₂².                                (T)

Every other term in that argument is a nonnegative slack. Each branch entropy is at least (n−1)s₀ and e(p)≥s₀. Hence D_n≥the right side of (T). When p=0 or 1, det ρ_j=0 and the eventual claim (B) is immediate; no division by a zero branch mass is made.

### 2.3 Inverting the remaining channel: all costs retained

In the orthonormal Pauli basis I/√2,X/√2,Y/√2,Z/√2, A has the two-by-two I,Z block

    [[1,0],[s,t]],

and X,Y multipliers √t. Its inverse has block [[1,0],[−s/t,1/t]]. The operator norm of this block is at most its Frobenius norm L, and L≥t^{−1/2}. Therefore

    ||(A^{⊗r})^{-1}||_{2→2} ≤ L^r.

For two normalized pure branch projections P₀,P₁,

    ||P₀−P₁||₂²=2(1−|⟨ψ₀,ψ₁⟩|²),
    det ρ_j=xy(1−|⟨ψ₀,ψ₁⟩|²).

Substituting the inverse estimate in (T) proves (B). The source channel acts identically on each site, so site permutations justify applying this argument separately to every j; no simultaneous reuse of incompatible branch decompositions is required.

### 2.4 From one-site marginals to one latitude product

Let σ_j be a top-eigenvalue pure state of ρ_j, and let z_j=1−λ_max(ρ_j). Since its eigenvalues sum to one,

    z_j≤2 det ρ_j,     Z=Σ_j z_j≤n L^{2(n−1)}D_n/(bc).      (Z)

The local projectors commute on different sites. The pointwise inequality 1−Π_j σ_j≤Σ_j(1−σ_j), followed by expectation in ψ, proves

    1−|⟨ψ,⊗_j σ_j⟩|²≤min(1,Z).

Write q_j for σ_j's excitation probability. From ρ_j=(1−z_j)σ_j+z_j(I−σ_j), |q_j−p_j|≤z_j. Choose φ_{θ_j} with the same relative phase as σ_j (arbitrary if an amplitude vanishes). The squared amplitude distance and hence the pure-state infidelity obey

    1−|⟨σ_j,φ_{θ_j}⟩|²
        ≤[(√q_j−√ν)²+(√(1−q_j)−√(1−ν))²]
        ≤(q_j−ν)²/h.

The denominators in the rationalized square-root differences are at least √ν and √(1−ν), respectively. Product infidelity is at most the sum of local infidelities. Using (P), z_j²≤z_j, the pure-state trace-distance identity, and the triangle inequality squared gives

    d_n(ψ)²≤8[Z+(2Σ_j(p_j−ν)²+2Z)/h]
             ≤8[(1+2/h)Z+D_n/(γt h)].

Together with (Z), this proves (N), including n=1 (where the marginal determinants vanish).

### 2.5 All exact minimizers, including mixed states

For a pure minimizer, (B) forces every one-site marginal to be pure. The preceding projector bound then has Z=0, so the entire vector is a product. Equation (P) forces each product factor's population to be ν. Conversely, every such product attains n s₀.

For a mixed minimizer choose its spectral decomposition ρ=Σ_i w_i P_i with positive weights. Entropy concavity and the pure minimum give

    n s₀=S(A^{⊗n}(ρ))≥Σ_i w_i S(A^{⊗n}(P_i))≥n s₀.

Thus every component is a pure minimizer and the first concavity gap vanishes. Applying (C) to any component versus the remaining mixture implies that all component outputs coincide. A^{⊗n} is injective because t>0, so all P_i coincide. A genuinely mixed spectral decomposition is impossible. This proves exact rigidity for all ρ.

For each **fixed** n, compactness now also gives a qualitative mixed-state stability modulus. It does not give a modulus uniform in n or a nominated quantitative finding.

## 3. Two routes toward (U), and their precise unpaid steps

### Route A: replace exponential inversion by entropy coercivity

The proof of (N) would become block-length-uniform if one proved the following sufficient estimate for some C(γ,ν)<∞:

    ∀n≥1 ∀pure ψ:  Σ_j det ρ_j ≤ C(γ,ν)D_n(ψ).            (LP)

Indeed, the last part of §2 uses only Z≤2Σ_j det ρ_j and (P), and would give

    K=8[2(1+2/h)C+1/(γt h)].

(LP) is stronger than what is needed to prove (U); its falsity would not refute (U). The paid source-mixture estimate controls **noisy conditional branch differences**, not input marginal determinants with a uniform coefficient. Applying a generic inverse has the exponential cost in §2.3. That missing bridge is not hidden in the notation.

There cannot be a uniform inverse estimate on all state differences. With Z the Pauli matrix and r≥1,

    ρ_±=(I^{⊗r}±Z^{⊗r})/2^r

are states, ||ρ_+−ρ_-||₁=2, A(Z)=tZ, and

    ||A^{⊗r}(ρ_+−ρ_-)||₁=2t^r.                            (I)

This exact diagnostic rules out the generic inverse shortcut. These are mixed high-entropy states, not an admissible pure sequence refuting (U) or (LP). It would be an error to call (I) a near-minimizer counterexample.

### Route B: a relative-entropy remainder, then a uniform nonlinear neighborhood

There is an exact alternative identity with no inverse channel. For any selected phases θ_j, set Φ=⊗φ_{θ_j}, σ_j=A(|φ_{θ_j}⟩⟨φ_{θ_j}|), σ=⊗σ_j, and

    E_θ(ρ)=Σ_j Tr ρ_j(I−|φ_{θ_j}⟩⟨φ_{θ_j}|),
    r₀=√(1−4γν(1−ν)),    a₀=2t atanh(r₀)/r₀.

Then, for every density matrix ρ,

    D_n(ρ)=a₀ E_θ(ρ)−D(A^{⊗n}(ρ)||σ).                    (R0)

Proof: the input Bloch vector is u=(2√h cosθ,2√h sinθ,1−2ν), and the output vector is (√t u_x,√t u_y,u_z). Its norm is r₀ and log σ_j=αI+(atanh r₀/r₀)r·Pauli. The adjoint channel multiplies the traceless x,y coordinates by √t and z by t, adding only a scalar from its nonunital shift. Thus its vector part is parallel to u, and

    −A^*(log σ_j)=s₀ I+a₀(I−|φ_{θ_j}⟩⟨φ_{θ_j}|).

The scalar follows by expectation in φ_{θ_j}, giving s₀. Tensor logarithms add, so the cross entropy is n s₀+a₀E_θ. Subtract output entropy to obtain (R0). The σ_j are positive definite, so every relative entropy in this identity is finite.

Choose θ_j to minimize the local quantity E_θ (align each available local coherence). A sufficient, presently unproved remainder is

    D(A^{⊗n}(ψ)||σ) ≤ a₀ E_θ(ψ)−c min(E_θ(ψ),1)          (R1)

with c>0 depending only on γ,ν. The product-projector bound gives d_n(ψ)²≤4 min(E_θ(ψ),1), so (R1) would prove (U) with K=4/c. This is a sufficient stronger estimate, not a proved contraction theorem. Ordinary data processing relative to a pure input reference has infinite input relative entropy and supplies nothing here. Omitting the **negative** relative-entropy term in (R0) reverses the useful direction and is invalid.

Ruskai–Yard's local-additivity proof gives a second route to studying neighborhoods of product minimizers, but cannot be substituted for (R1). The phase circles give exact zero tangent directions, so the required Hessian is on the normal directions to the entire product manifold. Local nonnegativity does not furnish a uniform positive normal gap. Even a normal Hessian bound would still need a radius and nonlinear remainder bound uniform in n, plus exclusion of low-deficit inputs outside that neighborhood. The smallest eigenvalue of σ is λ_-^n; naively bounding resolvent derivatives by λ_min^{-1} incurs another exponential loss. No uniform remainder or global entry argument is proved here. The fully read positive-definite proof portion is a comparator, not a premise claiming global stability.

## 4. Second target: the old uniform cubic threshold obstruction

The exact target, already screened in I114, is one numerical a>0 such that for **every** finite two-player game with finite-dimensional entangled value v<1, d=|A||B|, every 0<δ<1−v, every k≥1 and every finite-dimensional joint tensor-product strategy,

    Pr[W_k≥ceil((v+δ)k)]≤exp(−aδ³k/(1+log d)).             (G)

No question-law, question-alphabet or strategy-dimension dependence is permitted in a. The source proves universal δ⁵ and fixed-law δ³. These are not new results. The source's complete conditioning-to-threshold proof permits a budget T and produces rate δT/[16(1+log d)]. Hence a uniform square-root conditioning error would suffice for (G); another application of its fourth-root estimate does not.

### 4.1 Exact obstruction to a distribution-free common-reference lemma

Here is a complete diagnostic of the I114 weighted-root suggestion. For L≥3, let X=Y=Z/LZ and let μ assign mass 1/(2L) to each pair

    z_{2j}=(j,j),    z_{2j+1}=(j+1,j),   j∈Z/LZ.

Its support graph is a single cycle of length 2L. In a fixed two-dimensional real Hilbert space put u(α)=(cosα,sinα),

    Ψ_{z_{2j}}=u(2πj/L),    Ψ_{z_{2j+1}}=u(2π(j+1/2)/L),
    Ψ_{x=j}=u(2π(j−1/4)/L),    Ψ_{y=j}=u(2π(j+1/4)/L).

Both endpoint anchors of each edge are at angle distance π/(2L) from its pair vector, modulo 2π. Consequently

    Σ_z μ(z)[||Ψ_z−Ψ_x||²+||Ψ_z−Ψ_y||²]
        =4(1−cos(π/(2L))).                                (E)

The average pair vector is exactly zero: it is the sum of the 2L equally spaced unit vectors. For **every** common vector χ, including an unnormalized or optimally selected mean,

    Σ_z μ(z)||Ψ_z−χ||²=1+||χ||²≥1.                        (V)

For a unit common vector or a component root the value is exactly two. Therefore any common-reference replacement estimate from these local squared errors must have coefficient at least

    1/[4(1−cos(π/(2L)))] ≥ 2L²/π².

The source κ_μ=8(2L−1)(2L) has the same L² order. Weighted means or a better root do not make this operation distribution free. This is an exact analytic construction, not a scan and not a new spectral-gap theorem.

**Admissibility boundary:** these vector fields meet the local-anchor and mass properties used in the root path argument (take one flag, weight one, total mass one). They are not asserted to arise from the source's actual tested-event/resolvent exposure construction. No game predicate, repeated strategy, tested set C and small τ realizing them has been produced. Thus (E)–(V) refute the generic common-reference shortcut, **not** the desired square-root conditioning bound or (G). A new sampler could keep question-dependent states instead of using one reference. Worldwide impossibility is not inferred.

### 4.2 Smoothing the question law does not close the exponential budget

For μ' with TV(μ,μ')≤ε, the same fixed one-game strategy changes success by at most ε. Taking suprema gives |v(μ)−v(μ')|≤ε. For any fixed k-fold strategy and any acceptance event, the difference is at most TV(μ^{⊗k},μ'^{⊗k})≤kε, by independent maximal couplings and a union bound. This remains valid with arbitrary joint measurements: condition on the classical question strings and use the same conditional answer law.

A fixed-law cubic estimate transferred this way acquires additive kε. A fixed smoothing parameter cannot give a bound exponentially small for all k. Choosing ε exponentially small in k to suppress the additive term can make the source's inverse-minimum-mass coefficient exponentially large (for example smoothing a zero support cell with weight ε), destroying the useful exponent. This diagnoses this particular smoothing route; it is not a theorem excluding every support modification or a multiplicative change-of-measure argument.

The exact unpaid step remains an actual dimension- and question-law-uniform quantum rounding/conditioning argument with O(√τ) loss, or a different threshold mechanism avoiding that interface. Song's accessible primary abstract concerns the all-wins event. Its PDF fetch failed; a complete audit of its near-perfect-success proof was not performed, and no proof-level novelty certification for (G) is claimed.

## 5. Rejected screens and terminal obligations

Family 283's quantifier is ∀U ∃target-dependent unrestricted Boolean oracle, with one uniform circuit. I114 already derived arbitrary precision from the actual recursive/compilation operations. Stinespring dilation, coherent labels, phase compilation or ordinary error scheduling alone would recycle those operations. Efficient oracle construction is a different unsolved obligation, not supplied by the stipulated theorem. No third serious target is developed.

Family 284 provides total Boolean functions on its allowed lengths with R≥c_k m^{2−1/k}/log²m and Q≤C_k√m log^{b_k}m for each fixed k. Its complete probabilistic tournament proof was read: complementary comparison probabilities alone halve expected total weight, and a nearly undefeated candidate retains weight. Constant-margin majority amplification is routine. A new transitive total compiler would have to pay I147's exact heterogeneous-role/totality obstruction; no such compiler is obtained. Exponent substitution, expected-cost relabeling or a promise version is rejected.

**Strongest surviving research target:** (U), unresolved. The paid results are (P), (B), (N), exact rigidity, the identity (R0), and the two game-route diagnostics. They do not meet the requested substantiality bar. To resume meaningfully, prove (LP), prove (R1), provide a weaker sufficient uniform estimate for (U), or construct an actual pure near-minimizer sequence disproving (U). A future positive result also needs an independent proof gate and a broader proof-level priority check. For (G), generic vector fields must be separated from realizable exposure fields, and the unread Song proof must be obtained before claiming a new threshold improvement.

No acceptance recommendation, accepted-count change, subordinate agent, shared edit, staging, commit, publication, numerical scan or history verifier replay accompanies this record.
