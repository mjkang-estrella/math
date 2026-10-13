# I285 — phase coercivity for a bounded number of parity variables

**Verdict: restricted (TP), hence restricted (PH)/(U), proved globally; unrestricted (PH)/(TP)/(U) remain unresolved. No counterexample and no acceptance claim.** The new restriction is on the number of parity variables in the phase, not on block length, amplitudes, support sizes, support intersections, phase angles, or proximity to a minimizer. Twelve accepted findings toward twenty are unchanged.

All OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. Entropy is in nats and trace norm is unhalved. Every new lemma below has an exact proof. No external advanced theorem is used. The predecessor amplitude theorem, trace-tree remainder and one-parity theorem are spent inputs, not new findings.

## 1. Definitions, dependencies and statement

Fix 0<γ,ν<1. Write

    t=1−γ, h=ν(1−ν), b=γ(1−ν), c=γν,
    c_A=2γth, δ=min(ν,1−ν), s=γ(1−2ν),
    L=[1+(1+s²)/t²]^(1/2).

Let A be the GAD channel, r_n=Bernoulli(ν)^⊗n, s0=g(γh), and

    ψ_(q,f)=Σ_x √q(x)e^(if(x))|x⟩,
    D_n(ψ)=S(A^⊗n(P_ψ))−n s0,
    G_q(f)=1−max_θ |Σ_x q(x)e^(i(f(x)−θ·x))|².

The noisy branch-tree functional Q_π is exactly I280 §4's functional, with the same weights

    η(p)=bc p(1−p)/(2U0(p)U1(p)),
    U0(p)=1−tp−γν, U1(p)=tp+γν.

At a prefix v in the site ordering π, its summand is q(v)η(p_v)||A^⊗tail(P_ψv0)−A^⊗tail(P_ψv1)||_1². Leaves and zero-weight branches contribute zero. Put Q*=max_π Q_π. I280 proves

    η(p)≥2bc p(1−p),
    D_n(ψ)≥c_A KL(q||r_n)+Q*.                         (1)

The actual pinned family-276 channel formula, `lem:partner-branch`, `eq:recursion`, thermal endpoint mixture, and `eq:minimum-output-value` were read; the authentication record lists immutable URLs and exact extents. I273's finite-size projector/inverse operations are rederived in §2. No full-n marginal-determinant bridge is assumed. I279's false summed-original-marginal proposal remains excluded.

**Theorem.** Fix an integer k≥1. Suppose that, modulo 2π on the support of q,

    f(x)=α+θ0·x+F(Bx),                                 (2)

where B is a binary matrix of rank at most k, Bx is computed over GF(2), and F is an arbitrary real-valued function on its image. Then for every n≥1 and every probability law q, including laws with zeros and arbitrary correlations,

    G_q(f)≤C_k(γ,ν)[c_A KL(q||r_n)+Q*].                (TP_k)

No support or angle restriction is imposed on B or F. The constant is independent of n, B, F and q. One explicit, deliberately unoptimized choice is

    m_k=2k,
    A_k=2(1+2/h)L^(2(m_k−1))/(bc),
    β=4/h+2,
    H_k=2(1+4k)² δ^(−3k),
    C_k=max{2H_k A_k m_k, H_k(2β+2)/c_A}.             (3)

Consequently G_q(f)≤C_k D_n(ψ), and the original distance target holds on this class with K_k=8C_k+8/c_A. Rank zero gives G_q=0 directly.

This includes any fixed number of arbitrary-support, overlapping parity-phase gates, and arbitrary functions of those parities. At k=1 it extends the spent flat-amplitude parity theorem to every correlated amplitude law. At k≥2 it includes interactions among the parity variables themselves. It does **not** prove a constant independent of k.

Diagonal one-site phase rotations preserve G_q, D_n and every Q_π: the channel formula shows phase covariance; after conditioning, both children have the same remaining local rotations, while the conditioned site's rotation is a scalar. Thus α and θ0 in (2) can be removed. On q-zero strings choose the structured extension F(Bx); the actual state and tree do not depend on this choice.

## 2. A finite-core estimate directly in terms of the tree

This is a finite-dimensional lower operation, not the new structural theorem by itself. For an m-site pure state ψ with law a, select, for each j, any fixed ordering τ_j of those m sites beginning at j. For every phase extension f, define χ_f=Σ_x√r_m(x)e^(if(x))|x⟩. We prove

    G_(r_m)(f)≤A_m Σ_(j=1)^m Q_(τ_j)(ψ)+β KL(a||r_m),
    A_m=2(1+2/h)L^(2(m−1))/(bc).                      (4)

For m=1 the left side is zero; the argument also applies with all determinants zero. A core of size zero has zero phase defect and needs no estimate.

In the normalized Pauli basis the I,Z block of A is [[1,0],[s,t]], while X,Y have multiplier √t. Its inverse block is [[1,0],[−s/t,1/t]]. The block's operator norm is at most its Frobenius norm L, and the other inverse multipliers are at most L. Tensor products in Hilbert–Schmidt norm therefore give

    ||A^⊗r(H)||_2≥L^(−r)||H||_2.                     (5)

Split ψ at site j with weights 1−p,p and pure children P0,P1. The root contribution to Q_(τ_j), (1), ||·||_1≥||·||_2, and (5) imply

    Q_(τ_j)≥2bc p(1−p)L^(−2(m−1))||P0−P1||_2²
             =4bc L^(−2(m−1))det ρ_j.               (6)

Here det ρ_j=p(1−p)(1−|⟨ψ0,ψ1⟩|²). At p=0 or 1 it is zero and no child division is needed. The inverse cost in (6) is retained and depends on m; later m≤2k, never m=n without a rank restriction.

Let σ_j be a top-eigenvector projector of ρ_j, z_j=1−λ_max(ρ_j), and Z=Σ_j z_j. Since z_j≤2det ρ_j,

    Z≤[L^(2(m−1))/(2bc)] Σ_j Q_(τ_j).               (7)

The commuting local-projector inequality I−⊗σ_j≤Σ_j(I−σ_j) gives input infidelity to ⊗σ_j at most Z. Let p_j be ρ_j's excitation probability and u_j that of σ_j. The spectral decomposition gives |u_j−p_j|≤z_j. Choose a latitude factor φ_j with the relative phase of σ_j. Rationalizing square roots yields its infidelity to σ_j at most (u_j−ν)²/h. Hence product infidelity between ⊗σ_j and ⊗φ_j is at most [2Σ_j(p_j−ν)²+2Z]/h. Pure-projector trace distance and the squared triangle inequality give

    d_m(ψ)²≤8[(1+2/h)Z+(2/h)Σ_j(p_j−ν)²].           (8)

For k_ν(p)=KL(Bernoulli(p)||Bernoulli(ν)), k_ν(ν)=k_ν'(ν)=0 and k_ν''(p)=1/[p(1−p)]≥4, so k_ν(p)≥2(p−ν)², including endpoints by limits. Also

    KL(a||r_m)=KL(a||⊗_j a_j)+Σ_j k_ν(p_j)
              ≥2Σ_j(p_j−ν)².                       (9)

The nonnegative first term follows from log u≤u−1 (or its elementary finite-law proof). Thus (8) is at most 8[(1+2/h)Z+KL(a||r_m)/h].

For the affinity a0=Σ_x√(a(x)r_m(x)), Jensen on the a-support gives a0≥exp(−KL(a||r_m)/2), and

    ||P_ψ−P_χf||_1²=4(1−a0²)≤4 KL(a||r_m).         (10)

A second squared triangle inequality, to the latitude product used in (8), gives

    G_(r_m)(f)=d_m(χ_f)²/4
       ≤4(1+2/h)Z+(4/h+2)KL(a||r_m).                (11)

Substitute (7) to obtain (4). This proves the exact finite-core constant. It does not compare the entropy of χ_f with that of ψ, and uses no entropy continuity.

## 3. A core of at most twice the parity rank

Reduce B to its image, so it has full row rank r≤k. Choose r independent columns, call their sites b_1,…,b_r, and use these columns as the syndrome basis. The chosen columns are now the standard vectors e_i. Every other column has a coordinate vector a_j∈GF(2)^r.

Call i reused when some site j≠b_i has a_(j,i)=1. For each reused i choose one such witness site w_i. Witnesses lie outside the chosen basis; the same witness may serve several i. Let C consist of the basis sites and the distinct witnesses. Then

    r≤m=|C|≤2r≤2k.                                  (12)

Let R be the remaining sites. A non-reused syndrome coordinate is affected by exactly its basis site in the **entire original block**. Every nonbasis column is supported on reused syndrome coordinates. These assertions follow directly from the definition; they do not need an independence assumption on q.

Write z(y)=e^(iF(y)), and define the zero-syndrome core restriction g_C(x_C)=z(B_Cx_C). We next prove a uniform pointwise gluing estimate:

    G_q(F∘B)≤2(1+4r)² δ^(−m) G_(r_m)(F∘B_C)       (13)

for **every** q on the original block. In particular, q need not be the product law. This is the phase rank-one step that prevents an entropy-continuity transport loss.

Choose product phases u_j of modulus one and a global phase λ such that w(x_C)=λΠ_(j∈C)u_j^(x_j) attains the core overlap. Put g=G_(r_m)(F∘B_C). Then

    E_(r_m)|g_C−w|²=2(1−√(1−g))≤2g.

Every core string has probability at least δ^m, so, for every x_C,

    |g_C(x_C)−w(x_C)|≤ε, ε=√(2g/δ^m).              (14)

Denote the basis phases by u_i=u_(b_i). For a witness w with support S={i:a_(w,i)=1}, let rep(S) be the string with those basis sites 1 and all other core sites 0. The strings e_w and rep(S) have the same syndrome, so (14) gives

    |u_w−Π_(i∈S)u_i|≤2ε.

For each i∈S, the strings e_w+e_(b_i) and rep(S\{i}) also have the same syndrome, giving

    |u_w u_i−Π_(l∈S\{i})u_l|≤2ε.

Multiply the first bound by u_i and combine the two bounds. All other factors have modulus one, so

    |u_i²−1|≤4ε.                                    (15)

Every reused i has a witness. Choose β_i∈{−1,1} nearest to u_i for reused i; since max(|u_i−1|,|u_i+1|)≥1, (15) gives |u_i−β_i|≤4ε. For non-reused i set β_i=u_i. Evaluating (14) on rep(y) and replacing at most r factors proves, for every syndrome y,

    |z(y)−λΠ_i β_i^(y_i)|≤(1+4r)ε.                 (16)

For each original site j put v_j=Π_i β_i^(a_(j,i)). Because reused β_i are signs, their integer exponent can be reduced modulo two. For non-reused i the integer sum Σ_j a_(j,i)x_j is exactly x_(b_i), already in {0,1}. Consequently the identity

    Π_j v_j^(x_j)=Π_i β_i^((Bx)_i)                  (17)

holds on the entire original cube. Equations (16)–(17) supply one global additive phase approximant with pointwise error at most (1+4r)ε.

For any unit-modulus functions z,w and any law q, if a=E_q(z conjugate(w)), then

    1−|a|²≤2(1−Re a)=E_q|z−w|²,

because the difference of the right and left sides is |1−a|². Apply this to the approximant (17), then use (14), to prove (13). This proof is exact even when ε is large; the estimate is merely then uninformative. There is no small-defect hypothesis or compactness/Hessian argument.

## 4. Paying the core tests with the original noisy tree

Fix any ordering of R and put all its sites before the core. For a full R-prefix v, let q_R(v) be its probability, q_v the conditional law on C when q_R(v)>0, and y_v=B_Rv. Define the deterministic bounded function

    a(v)=G_(r_m)(x_C↦F(y_v+B_Cx_C)), 0≤a(v)≤1.      (18)

It is defined also at q_R-zero prefixes. At such prefixes conditional states/laws can be chosen arbitrarily; every q-weighted contribution is zero.

Choose the m fixed core orderings τ_j from §2, and let π_j be the full ordering R followed by τ_j. Applied at each positive prefix, (4) gives

    E_(q_R) a(v)≤A_m Σ_j E_(q_R)Q_(τ_j)(ψ_v)
                  +β E_(q_R)KL(q_v||r_m)
               ≤A_m m Q*+β KL(q||r_n).              (19)

For the tree comparison, E_(q_R)Q_(τ_j)(ψ_v) is **exactly the suffix part** of Q_(π_j)(ψ); the prefix terms are nonnegative. No ordering is selected adaptively by v. The classical chain rule gives E_(q_R)KL(q_v||r_m)≤KL(q||r_n).

Here is the precise robust change of measure. If 0≤a≤1, then, term by term, √r_R=√q_R+(√r_R−√q_R) and (u+v)²≤2u²+2v² imply

    E_(r_R)a≤2E_(q_R)a+2Σ_v(√r_R(v)−√q_R(v))²
             ≤2E_(q_R)a+2KL(q_R||r_R).              (20)

The last bound follows from the affinity calculation: the squared square-root distance is 2(1−affinity)≤2(1−e^(−KL/2))≤KL. Marginal KL is at most full KL by the same chain rule. Thus (19)–(20) yield

    E_(r_R)a≤2A_m m Q*+(2β+2)KL(q||r_n).            (21)

Let s_R=rank B_R≤r. Under the product law on R,

    Pr[B_R X_R=0]≥δ^(s_R).                          (22)

To prove (22), choose s_R independent columns of B_R. Conditional on all other R-bits, exactly one configuration of those chosen bits realizes syndrome zero, because the other columns are in their span. The probability of that configuration is at least δ^(s_R). Average over the other independent bits. This also covers s_R=0, when the probability is one.

On the event in (22), a(v) is the zero-syndrome core defect g from §3. Therefore

    g≤δ^(−s_R) E_(r_R)a.

Combine this with the **arbitrary-q** gluing bound (13) and (21):

    G_q(f)≤H_B[2A_m m Q*+(2β+2)KL(q||r_n)],
    H_B=2(1+4r)² δ^(−(m+s_R)).                      (23)

Since m≤2k, s_R≤k, and L>1, H_B≤H_k and A_m≤A_k. Equations (3) and (23) prove (TP_k). Equation (1) proves (PH) on this class. I280's paid distance conversion d_n²≤8G_q+8D_n/c_A gives K_k. ∎

## 5. Scope, comparisons and exact remaining gap

The new mechanism is the witness core (12)–(17), combined with the bounded-test/Hellinger transport (20) and the fixed-order tree accounting (19). It handles arbitrary correlated q directly, without asserting that output entropy survives amplitude flattening. The phase core has at most 2k sites even when every parity support fills the block and the supports overlap arbitrarily. Inverse-channel and marginal-projector estimates are confined to this core and retain all their size costs.

Examples covered by the theorem include

    f(x)=α1 (−1)^(a·x)+α2 (−1)^(b·x)
                   +α12 (−1)^((a+b)·x)+θ0·x,

for arbitrary binary a,b, arbitrary real coefficients and arbitrary q. This is an arbitrary function of two parities up to a constant. It is not restricted to disjoint gates or product amplitudes. More generally, a function of k parities may have all 2^k phase values arbitrary. The existence of an affine part in (2) costs no parity rank.

The k=1 flat-amplitude case was already proved in I280, with much better constants. The site-separating case and the all-n amplitude bound are also spent. The present result's additional scope is multiple interacting/overlapping parity variables and robustness to every correlated amplitude law, and it proves the sufficient **tree** inequality on that class. No new-to-literature claim or substantiality nomination is made. The elementary finite-core estimates and changes of measure are standard lower operations; the assembled restricted theorem is author-level progress requiring independent review.

Every unrestricted phase can be represented with B=I_n and k=n. Using (3) then loses an exponentially growing constant. Neither the witness argument nor the selected syndrome lower bound provides a uniform bound as k grows. A completion would require a dimension-independent way of charging many phase degrees of freedom, avoiding both the inverse cost L^(O(k)) and the small-probability core/syndrome factors δ^(−O(k)), or an entirely different mechanism. Their growth in this proof is **not** a lower bound on the best possible constants.

The research explored Fourier/martingale and random-restriction routes before this reduction. A squared noisy tangent norm has no proved uniform comparison here with the simultaneous first-order input phase coefficients; higher-order cancellations cannot simply be discarded. Paying only a fixed last pair misses defects spread among many coordinates. These observations are unpaid-route diagnostics, not counterexamples. No random-phase, threshold-phase, or large-rank family was established to violate TP, PH or U. No numerical scan was run.

The user later authorized reading completed I281; it was not needed or read. Its reported Gram-entropy cat exclusions are not used, repeated, or credited to this proof. No live sibling work or I282 was read. The original full target is still open in this record. Detached hashes accompany the handoff; acceptance and the twelve-count ledger are the parent's responsibility.
