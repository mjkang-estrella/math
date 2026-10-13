# I280 — constructive discovery for uniform GAD stability

**Full (U) remains unresolved.** This record proves dimension-independent amplitude control, (U) on the entire class of inputs with phases separating by site, a trace-norm remainder for the conditional branch tree, and a global nonlinear bound for parity-phase states of arbitrarily large support. These are partial progress, not a proof for arbitrary phases and not an acceptance nomination. Eleven findings remain accepted toward twenty; no count changes.

All OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. The deductions below are independently checked. Entropy and relative entropy use natural logarithms; trace norm is unhalved. Work is confined to this project and the assigned I280 files. No children, live sibling reads, shared edits, staging, commits, publishing, numerical scans, or history replay were used.

## 1. Target and actual dependencies

Fix 0<γ,ν<1, put t=1−γ and h=ν(1−ν), and let A=A_(γ,ν). Set

    φ_θ=√(1−ν)|0⟩+e^(iθ)√ν|1⟩,
    M_n={P_(φ_θ1⊗⋯⊗φ_θn)},
    s0=g(γh),   D_n(ψ)=S(A^⊗n(P_ψ))−n s0,
    d_n(ψ)=min_(P∈M_n)||P_ψ−P||_1.

The only main target is

    ∃K(γ,ν)<∞ ∀n≥1 ∀unit pure ψ: d_n(ψ)^2≤K(γ,ν)D_n(ψ).   (U)

There is no bound on n, normalization of D_n by n, mixed-input assertion, or uniformity at parameter endpoints.

The actual pinned family-276 files were read completely and authenticated against both a fresh pinned raw fetch and the exact path's Git blob in `sources/preprints-tree.json`: `build/paper.tex`, `build/sections/output.tex`, `thermal.tex`, and `partners.tex`. Used labels are `eq:channel`, `eq:v-main`, `cor:partner-additivity`, `eq:minimum-output-value`, `lem:partner-branch`, `eq:partner-branch`, `eq:recursion`, `thm:thermal`, `eq:thermal-table`, and `eq:thermal-factors`. The source's zero-block theorem and its endpoint applications are stipulated lower operations. The branch inequality, rather than merely its population-Jensen corollary, is essential here.

The completed I273 report, full analysis, reading log, authentication JSON, literature note, and parent disposition were read. I279 was read and independently checked in §2. No I277/I278 live contact records or parallel GAD outputs were inspected. I273's exact rigidity, exponential-cost bound, and R0 identity are predecessor facts; they are not renominated. Neither injectivity nor fixed-n compactness is used as a uniform stability argument.

## 2. Independent check of I279

Write a=φ_0, b=φ_π, z=⟨a,b⟩=1−2ν, and

    ψ_n=(a^⊗n+b^⊗n)/√(2(1+z^n)).

Here |z|<1. Partial trace of the two cross terms gives z^(n−1)(|a⟩⟨b|+|b⟩⟨a|); combining them with P_a+P_b gives the diagonal marginal

    ρ_j=diag((1−ν)(1+z^(n−1)), ν(1−z^(n−1)))/(1+z^n),
    det ρ_j=h(1−z^(2n−2))/(1+z^n)^2 →h.

By linearity of the actual channel formula,

    X=A(|a⟩⟨b|)
     =[[ (1−ν)(1−2γν), −√(th)],
       [ √(th), ν(2γ(1−ν)−1)]].

Direct expansion gives

    det X=γh(1−4γh)>0,
    Tr X*X=1−6γh+8γ²h².

For the singular values s1,s2 of a 2×2 matrix, (s1+s2)^2=Tr X*X+2|det X|. Hence

    ||X||_1=κ=√(1−4γh)<1,   κ²−z²=4th>0.

Let σ_a=A(P_a), σ_b=A(P_b), τ_n=(σ_a^⊗n+σ_b^⊗n)/2, and ω_n=A^⊗n(P_ψn). Exact subtraction yields

    ω_n−τ_n=[(X^⊗n+(X*)^⊗n)/2−z^n τ_n]/(1+z^n),
    ||ω_n−τ_n||_1≤(|z|^n+κ^n)/(1−|z|^n).

To check dimension dependence, put δ=||ω_n−τ_n||_1/2. The positive and negative parts of their difference give states R,S such that (ω_n+δS)/(1+δ)=(τ_n+δR)/(1+δ). Concavity and the binary-mixture entropy upper bound on these two representations imply

    |S(ω_n)−S(τ_n)|≤δ n log 2+(1+δ)h_2(δ/(1+δ))→0.

Thus D_n≤log 2+o(1), because both components of τ_n have entropy n s0. The lower limit also equals log 2: measure Pauli X separately on the factors. The two equally likely labels produce independent outcomes of means ±m, m=2√(th)>0. The sign of the sample mean has error at most 1/(nm²). Binary Fano and the standard Holevo measurement bound give S(τ_n)−n s0≥log 2−o(1). These are the ordinary coding/measurement operations used in the pinned paper, not a new literature claim.

Consequently Σ_j det ρ_j~nh while D_n→log 2. **(LP) is false.** The same family cannot refute (U), since its entropy excess does not tend to zero and d_n²≤4. The generic inverse-channel cost also remains genuinely exponential, as the predecessor's Pauli example shows.

This cat has nonnegative computational amplitudes: it deletes the odd-parity strings of the Bernoulli product law. It therefore lies in the phase-separating class treated below. The partial theorem charges its one parity constraint once, consistently with I279.

## 3. A branch tree that charges the full amplitude law

Expand any unit vector as

    ψ=Σ_(x∈{0,1}^n)√q(x)e^(if(x))|x⟩,
    r_n(x)=ν^|x|(1−ν)^(n−|x|).

Choose phases arbitrarily where q(x)=0. For a prefix v of length j−1 with q(v)>0, let ψ_v be the normalized remaining pure vector, p_v=q(X_j=1|v), and let ω_v=A^⊗(n−j+1)(P_ψv). At depth n define the scalar output state with entropy zero. Apply the actual `lem:partner-branch` at every node, without Jensen averaging over prefixes. It gives

    ℓ_v=S(ω_v)−e(p_v)−(1−p_v)S(ω_v0)−p_v S(ω_v1)≥0,
    e(p)=g(γh+γt(p−ν)^2).

Zero-probability nodes are omitted; zero-weight child states can be chosen arbitrarily. Repeated substitution, using q(v0)=q(v)(1−p_v) and q(v1)=q(v)p_v, gives the exact identity

    D_n(ψ)=B_n(q)+L_n(ψ),                                 (T0)
    B_n(q)=Σ_(j=1)^n Σ_(|v|=j−1) q(v)[e(p_v)−s0],
    L_n(ψ)=Σ_(j=1)^n Σ_(|v|=j−1) q(v)ℓ_v≥0.

At one-site nodes ℓ_v=0. The equality in (T0) is telescoping of the defined slacks; no equality is asserted in the source lower bound.

For u∈(0,1/4), set R=√(1−4u). Differentiating g gives g'(u)=2 atanh(R)/R≥2, with continuous endpoint interpretation. Integration gives

    e(p)−s0≥2γt(p−ν)^2.                                  (T1)

For the Bernoulli relative entropy k_ν(p), log s≤s−1 gives

    k_ν(p)=p log(p/ν)+(1−p)log((1−p)/(1−ν))
          ≤(p−ν)^2/h.                                    (T2)

This includes p=0,1 by limits. It is the standard relative-entropy/χ² comparison; the relevant primary comparator is Sason–Verdú, Theorem 2(a), read with its full proof. Here the two-point calculation is independently derived.

The finite classical chain rule follows by taking q-expectations of

    log(q(x)/r_n(x))=Σ_j log(q(x_j|x_<j)/r_1(x_j))

on the support of q. Therefore, with c_A=2γth>0,

    D_n(ψ)≥B_n(q)≥c_A KL(q||r_n).                         (A)

This holds for every pure ψ and every n, regardless of its phases. A useful equivalent expansion is

    KL(q||r_n)=KL(q||⊗_j q_j)+Σ_j k_ν(q_j(1)).

Unlike a sum of marginal determinants, the first term is the total correlation of the computational probability law. A single global parity constraint has a bounded cost.

### 3.1 Uniform entry into the fixed-amplitude phase torus

Define χ_f=Σ_x√r_n(x)e^(if(x))|x⟩. Its overlap with ψ is the nonnegative affinity F_a=Σ_x√(q(x)r_n(x)). Jensen's inequality for log, on the q-support, gives

    log F_a≥Σ_x q(x)log√(r_n(x)/q(x))=−KL(q||r_n)/2.

The pure-projector trace-distance identity then proves

    ||P_ψ−P_χf||_1²=4(1−F_a²)
      ≤4(1−exp(−KL(q||r_n)))
      ≤4(1−exp(−D_n(ψ)/c_A))≤(4/c_A)D_n(ψ).              (AT)

This is a **global, dimension-independent entry estimate** into the manifold of all arbitrary phases with Bernoulli product amplitudes. It is not entry into M_n: arbitrary f can be entangling. On q-zero strings χ_f depends on the arbitrary phase extension, but (AT) holds for every extension.

### 3.2 Complete uniform theorem for phases separating by site

Suppose f(x)=α+Σ_j θ_j x_j modulo 2π on the support of q. The probabilities q can be arbitrary, with zeros and arbitrary correlations. Choose this same additive phase extension on zero-probability strings. Then χ_f is, after a global phase, the latitude product φ_θ1⊗⋯⊗φ_θn. Thus, for all n and all such ψ,

    d_n(ψ)^2≤4(1−exp(−D_n(ψ)/c_A))
            ≤[2/(γt h)]D_n(ψ).                           (AS)

This is a complete proof of the restricted assertion. It includes genuinely entangled inputs with correlated amplitudes, rather than just product states or one-copy inputs. It imposes a phase restriction, not a parameter subregime, and does not prove full (U).

For the I279 cat, q(x)=2r_n(x)/(1+z^n) on even strings and zero on odd strings. Hence KL(q||r_n)=log(2/(1+z^n))→log 2. Formula (A) consequently gives D_n≥c_A log(2/(1+z^n)). This independently verifies that the amplitude bound pays a bounded parity cost, not nh.

## 4. A trace-norm branch remainder without spectator loss

For any two density matrices Q0,Q1 and 0≤w≤1,

    S(wQ0+(1−w)Q1)−wS(Q0)−(1−w)S(Q1)
      ≥(1/2)w(1−w)||Q0−Q1||_1².                          (SC)

This is a standard Pinsker concavity remainder (Carlen, Corollary 3.3, is a read primary comparator). An independent derivative proof fixes all norms and constants. For a positive-definite state ρ and Hermitian H, in its eigenbasis the negative entropy Hessian is

    −S''_ρ[H,H]=Σ_ab |H_ab|²/L(λ_a,λ_b),
    L(a,b)=∫_0^1 a^s b^(1−s)ds,

where the diagonal convention is L(a,a)=a. The formula follows by the resolvent derivative of log; equivalently L(a,b)=(a−b)/(log a−log b). Let J=sign(H), with an arbitrary ±1 choice on its kernel, so J is Hermitian, J²=I, and Tr HJ=||H||_1. Weighted Cauchy–Schwarz and L(a,b)≤(a+b)/2 give

    ||H||_1²
      ≤[Σ_ab |H_ab|²/L(λ_a,λ_b)] [Σ_ab L(λ_a,λ_b)|J_ab|²]
      ≤−S''_ρ[H,H] Tr(ρJ²)=−S''_ρ[H,H].

The logarithmic-mean bound follows by integrating weighted arithmetic/geometric mean. Along the affine segment, H=Q0−Q1 is constant. Integrating the scalar strong-concavity inequality proves (SC). Mixing both endpoints with εI/d and then taking ε↓0 handles singular states. No eigenvalue lower bound survives in the constant, and no dimension factor occurs.

Apply this to the actual thermal endpoint mixture at a branch of population p. Put x=1−p, y=p, b=γ(1−ν), c=γν,

    U0=1−tp−γν,   U1=tp+γν,   u=U0U1−txy,
    R_i=A^⊗r(P_ψi),   r=number of remaining sites.

In the source table, w1=by U1/u and w2=cx U0/u. The states T1,T2 have identical cross blocks and

    T1−T2=diag((u/U1)(R1−R0), −(u/U0)(R1−R0)),
    ||T1−T2||_1=[u/(U0U1)]||R1−R0||_1.

Combining (SC) with the stipulated endpoint entropy bounds, which recover the original branch weights, yields the refined branch inequality

    ℓ_v≥η(p_v)||ω_v0−ω_v1||_1²,
    η(p)=bc p(1−p)/(2U0(p)U1(p))≥2bc p(1−p).             (BR)

The expression is well-defined at every p, since interior γ,ν make both U's positive; η(0)=η(1)=0. For p=ν, U0U1=h and η(ν)=γ²h/2.

For each ordering π of the input sites, define

    Q_π(ψ)=Σ_(j=1)^(n−1) Σ_(prefix v in order π)
               q(v)η(p_v)||ω_v0−ω_v1||_1².

The preceding proof, the tree identity, and the order-independent classical chain rule give

    D_n(ψ)≥c_A KL(q||r_n)+Q_π(ψ),
    D_n(ψ)≥c_A KL(q||r_n)+max_π Q_π(ψ).                  (BT)

The trace norm matters: tensoring a branch difference with any spectator density matrix leaves its trace norm unchanged. Its Hilbert–Schmidt norm instead acquires the spectator purity. This removes that artificial loss from the *remainder*, not from the unproved comparison to the input product overlap. Q_π still uses noisy branch differences. No inverse-channel bound has been silently added.

## 5. Complete nonlinear theorem for an arbitrarily large parity-phase defect

For an arbitrary subset T of m sites, local phases θ_j, and real α, consider

    Ψ_(n,T,α,θ)=exp(iα Z_T)(φ_θ1⊗⋯⊗φ_θn),
    Z_T=⊗_(j∈T) Z_j, with identity on the other sites.

For m=0 or 1 this is a latitude product. For m≥2, all n, all T and all α, the following explicit global bound holds:

    d_n(Ψ)^2≤[1/(4γ²t h²)]D_n(Ψ).                        (PP)

**Proof.** Diagonal one-site phase rotations commute with A up to the same output rotations, so entropy and distance to M_n are unchanged. Spectator factors add exactly s0 each; permutations reduce the problem to θ=0 and n=m. Let Φ_m=φ_0^⊗m. Then

    ψ_m(α)=cos α Φ_m+i sin α Z^⊗m Φ_m.

The two branch overlaps are real, so this vector is normalized. All its computational probabilities are r_m. Conditioning its first site on 0 or 1 leaves ψ_(m−1)(α) or ψ_(m−1)(−α), with branch probabilities 1−ν,ν. The two output entropies agree by complex conjugation because A has real coefficients. Since e(ν)=s0, the source branch recursion gives

    D_m(ψ_m(α))≥D_(m−1)(ψ_(m−1)(α))≥⋯≥D_2(ψ_2(α)).

At m=2 the conditional one-site vectors are

    u_+=√(1−ν)e^(iα)|0⟩+√ν e^(−iα)|1⟩,
    u_−=conjugate(u_+).

Their output diagonal entries agree, and their off-diagonal difference is 2i√(th)sin(2α). Therefore

    ||A(P_u+)−A(P_u−)||_1²=16t h sin²(2α).

Apply (BR) at p=ν. Both child deficits vanish, giving

    D_m≥D_2≥8γ²t h² sin²(2α).                            (PP1)

Finally, z=1−2ν and ⟨Φ_m,Z^⊗mΦ_m⟩=z^m. The squared overlaps with the two latitude products Φ_m and Z^⊗mΦ_m are respectively

    cos²α+sin²α z^(2m),   sin²α+cos²α z^(2m).

Thus

    d_m²≤4(1−z^(2m))min(sin²α,cos²α)
         ≤2 sin²(2α).

The last inequality uses sin²α cos²α≥min(sin²α,cos²α)/2. Combining with (PP1) proves (PP), including the cases sin(2α)=0 where the input is a latitude product. Restoring spectators and local rotations completes the proof. ∎

For generic α these states are entangled across cuts of T, and T may contain every site. This is an exact nonlinear all-amplitude estimate, not a formal Hessian or a fixed-entanglement-width result. It pays a collective phase defect at a two-site conditional stage once. It is still a special input family, not full (U) or a certified substantial new theorem.

## 6. The exact unresolved inequality

For arbitrary q and f, define the input's nonseparable phase defect

    G_q(f)=1−max_(θ∈R^n)|Σ_x q(x)e^(i(f(x)−θ·x))|².        (G)

Let ψ_(q,θ)=Σ_x√q(x)e^(iθ·x)|x⟩. Direct overlap gives

    min_θ ||P_ψ−P_ψ(q,θ)||_1²=4G_q(f),
    ||P_ψ(q,θ)−P_φθ||_1²≤(4/c_A)D_n(ψ),

the second inequality following from (A) and affinity, independently of θ. The triangle inequality squared therefore gives

    d_n(ψ)^2≤8G_q(f)+(8/c_A)D_n(ψ).                      (R)

Consequently the following robust phase inequality would finish the full target:

    ∃C(γ,ν)<∞ ∀n,q,f: G_q(f)≤C(γ,ν)D_n(ψ_(q,f)).         (PH)

It would give K=8C+8/c_A. This is the **exact unpaid phase step** after the proved amplitude control. It is also necessary up to constants: if (U) holds with K, apply the triangle inequality to ψ, its closest latitude product, and ψ_(q,θ). The same affinity estimate gives

    G_q(f)≤(K/2+2/c_A)D_n(ψ).

Thus this is an equivalent phase formulation with paid amplitude error, rather than a claim that phase-free entropy tensorization solved the problem. A concrete stronger sufficient mechanism suggested by the trace remainder is

    G_q(f)≤C[ c_A KL(q||r_n)+max_π Q_π(ψ_(q,f)) ].         (TP)

No proof or refutation of (TP) is supplied. (BT) would imply (PH) if it were proved. This tree functional differs from the refuted sum of original marginal determinants; its boundedness by D_n is already proved. Conditional noisy distinguishability would have to control global phase alignment, and that comparison is the missing new mechanism.

For q=r_n, the amplitude cost and every conditional population cost are zero, yet G can be positive. In this case G=d_n²/4 exactly. Proving a flat-amplitude phase theorem alone would not automatically settle arbitrary q: a dimension-uniform transport estimate for entropy or a robust phase argument would still be needed. (PH) explicitly includes this robustness.

## 7. Dead ends and limits of the proof-discovery search

1. **Discarding branch information by Jensen.** The source's Σ_j e(p_j) estimate misses classical amplitude correlations. Keeping the tree gives (A); it still misses nonseparable phases unless a remainder is used. The parity-phase family has q=r_n, demonstrating the distinction exactly.
2. **Summed original marginal determinants.** I279 analytically refutes (LP). Replacing original marginals by noise-free conditional marginal determinants also has no proved entropy comparison; conditioning does not authorize charging the same cat defect repeatedly. No such estimate is nominated.
3. **Generic inversion.** For ρ_±=(I^⊗r±Z^⊗r)/2^r, A^⊗r(ρ_+−ρ_-)=t^r(ρ_+−ρ_-). A trace-norm branch remainder cannot turn this into a dimension-independent inverse on arbitrary differences. These mixed states do not refute pure near-minimizer (U).
4. **Flattening amplitudes and applying entropy continuity.** (AT) is uniform in input distance. Entropy continuity at output dimension 2^n gives an n-dependent term; it does not bound D_n(χ_f) by a constant times D_n(ψ). The flattened phase problem cannot be transported this way.
5. **Inductively matching two approximate branch products.** The branches may have different minimizing phases. A triangle argument inflates the coefficients on their deficits, so an induction with a single K does not close merely from separate branch stability. The trace remainder supplies distinguishability, but no proved gluing inequality recovers the required global input overlap.
6. **Depolarizing comparison.** A primary stability paper was found and fully read at §§II–III. It is not a GAD theorem. Even for ν=1/2, the Bloch multipliers are (√t,√t,t), not isotropic. The tempting post-map after a depolarizing channel of multiplier √t would have multipliers (1,1,√t); its Pauli weight (√t−1)/4 is negative. This is not a completely positive entropy-monotone degradation. No transfer is obtained.
7. **Local Hessian or relative entropy only.** I273's R0 has a negative divergence term. Its R1 remains unpaid. Formal normal positivity and a fixed-n expansion do not provide either a uniform nonlinear radius or global entry. The new amplitude entry (AT) covers only the phase torus; (PP) pays a phase family globally. Neither supplies the general phase radius or entry step.

The primary-literature search is bounded and does not establish worldwide novelty or worldwide openness. The new partials use standard branch recursion, classical divergence comparison, concavity, and direct overlap calculations; no independent substantiality or acceptance claim is made. A future completion must prove (PH), prove a sufficient coercivity mechanism such as (TP), or give an admissible pure near-minimizer counterexample, and then undergo independent proof and contribution review.
