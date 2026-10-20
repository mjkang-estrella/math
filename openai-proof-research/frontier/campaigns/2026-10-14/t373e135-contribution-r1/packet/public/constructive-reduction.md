# A compatible recovery for the entire T373E135 scope

This is the constructive basis of a contribution comparison, conditional on the candidate's correctness and the stipulated Source373 operations. It is not a correctness verdict on the submitted stochastic proof. The frozen statement and all its quantifiers are retained. Write H(p)=∫p log p.

## 1. Paid inputs and the exact interface

For either branch, the actual Source373 strict-convexity proof, common-parameter diffeomorphisms and compact separation give the author's interface

 r(t,t,t)=0, ∇r(t,t,t)=0,
 r(t0,t1,t2) ≍ |t1−t0|²+|t2−t0|²,
 K(t)=D²_(t1,t2)r(t,t,t)>0 on Qbar.

The matrices are smooth, uniformly positive definite on the fixed compact cube. The full Hessian in coordinates (t0,h1=t1−t0,h2=t2−t0) has only the normal block K. These are compatible consequences of paid source operations, also operative in I220; they are not a new Hessian theorem. Choose a smooth compactly supported extension r̃ to all of R^(3d) agreeing with r on a neighborhood of Qbar³. Its Hessian is bounded and uniformly continuous. This extension is only an auxiliary calculation, never a physical Riesz competitor.

Set A(t)=K(t)⁻¹. Use the paid elementary covariance lift from the author's Section 2. In (z0,h1,h2) coordinates it is

 S(t) = [[βI, R_A(t)], [R_A(t)^T, A(t)]],
 R_A(t) = (−A11(t)/2, −A22(t)/2).

Choose one fixed β>sup ||R_A A⁻¹ R_A^T||. The Schur complement makes S positive definite. Under L(z,h1,h2)=(z,z+h1,z+h2), put C=LSL^T and D(z0,z1,z2)=(z1−z0,z2−z0). Then

 Cii(t)=βI for i=0,1,2,    D C(t) D^T=A(t).

All eigenvalue bounds can depend on the fixed data. No commutativity, constant A, restriction on A12, or finite-example argument enters.

## 2. Full correlated Gaussian profile, with explicitly known marginals

Sample T with density f, then U conditional on T=t as N(0,C(t)). Define

 Z_i=T+√s U_i, i=0,1,2;    Γ_s=Law(Z0,Z1,Z2).

For EVERY t, the conditional marginal law of U_i is N(0,βI), independently of i and t. Therefore all three marginals of Γ_s are EXACTLY

 g_s=f*G_(βsI).

This is the decisive compatibility observation. It uses the complete correlated Gaussian, including arbitrary normal cross-covariance; it does not conditionally multiply two kernels. The parameter dependence of C creates no marginal defect beyond the same scalar heat smoothing in each marginal. Since C is uniformly elliptic on Qbar, Γ_s has a positive density.

## 3. Exact marginal repair with squared displacement O(s²)

The specified f is a product ρ^⊗d, where ρ is the normalized one-dimensional flat bump on (−a,a). Its zero extension is smooth and

 I(ρ)=∫ |ρ′|²/ρ <∞,    I(f)=d I(ρ)<∞.

Exponential decay at the endpoints dominates the polynomial singularities of the score. No lower bound for ρ at the endpoints is used. Put ρ_v=ρ*G_(βv), so g_v=ρ_v^⊗d. Let F_v be its scalar CDF and X_v=F_v⁻¹ the scalar quantile. For v>0 and 0<u<1,

 ∂_v X_v(u)=−(β/2)(∂_x log ρ_v)(X_v(u)).                 (R1)

Indeed ∂_v F_v=(β/2)ρ_v′ and differentiate F_v(X_v(u))=u. Integration by parts in the convolution and conditional Jensen give

 (ρ_v′/ρ_v)(x)=E[(ρ′/ρ)(T) | T+√(βv)N=x],
 I(ρ_v)≤I(ρ).                                             (R2)

The integration by parts has zero boundary term because the bump is flat. For 0<δ<s, Cauchy–Schwarz in v, then (R1)–(R2), yield

 ∫_0^1 |X_s(u)−X_δ(u)|² du
 ≤ (β²/4)(s−δ)∫_δ^s I(ρ_v)dv
 ≤ (β²/4)(s−δ)² I(ρ).

As δ↓0 the quantiles converge pointwise to X_0 on (0,1), since ρ is positive inside its support. Fatou gives

 ∫_0^1 |X_s−X_0|²du ≤ (β²/4)s²I(ρ).                       (R3)

Let m_s=F_0⁻¹∘F_s and let M_s apply m_s in every spatial coordinate. It is a Borel bijection from R^d to Q with a Borel inverse, and M_s#g_s=ν. Applying it separately to the three particles gives

 P_s=(M_s,M_s,M_s)#Γ_s ∈ Π(ν,ν,ν),
 E∑_i |M_s(Z_i)−Z_i|² ≤ (3β²/4)s² I(f).                  (R4)

Every repaired triple lies in Q³. Scalar quantile coupling and product transport are ordinary operations; I35's actual Sections 3 and 3.1 already use scalar rearrangement and product tensorization, with their precise limitations. Here the target law really IS a product, so componentwise transport has the required multivariate law. We do not import I35's unproved general transverse-redistribution assertion.

This is a deterministic specialization of the actual multi-marginal shadow construction: [Eckstein–Nutz, 2208.14391v3](https://arxiv.org/abs/2208.14391v3), Definition 2.4 and Lemma 2.5; its transitive proof is [2110.06798v3](https://arxiv.org/abs/2110.06798v3), Definition 3.1, Lemma 3.2 and Section 4.1. Those statements concern arbitrary numbers of marginals. Their independent product kernel acts on an already correlated joint law; it does not factorize that law. The explicit quantile calculation above supplies the sharper marginal displacement needed here, rather than invoking a generic O(√s) smoothing estimate.

## 4. Repair has o(s) cost error and preserves the full normal law

Write Δ_i=M_s(Z_i)−Z_i and T^Δ=(T,T,T). Uniform Gaussian moment bounds give E|Z−T^Δ|²=O(s). Since ∇r̃(T^Δ)=0 and its Hessian is bounded,

 |r̃(Z+Δ)−r̃(Z)| ≤ L|Z−T^Δ||Δ|+(L/2)|Δ|².

Consequently (R4) gives

 |E r(P_s)−E r̃(Γ_s)| = O(s^(3/2))+O(s²)=o(s).             (R5)

Taylor expansion at T^Δ and uniform Gaussian moment bounds give

 E r̃(Γ_s) = (s/2)∫ f(t) tr(C(t)D²r̃(T^Δ))dt+o(s)
           = (s/2)∫ f tr(K A)=d s+o(s).                    (R6)

For a direct remainder justification use uniform continuity of D²r̃ on bounded sets, split |√sU|≤η and its complement, and use the bounded Hessian and uniformly bounded higher Gaussian moments on the complement. This works for any fixed d and any fixed compact positive matrix field.

Moreover E|DΔ/√s|²=O(s)→0. Thus the exact marginal repair leaves the ENTIRE 2d-dimensional normal profile, including its cross-covariance, unchanged to leading order. No pair-kernel covariance substitution has occurred. The repaired physical recovery, obtained only after applying Id,Y_k,W_k on Q, stays in three distinct compact components. Therefore α≥d and arbitrarily large fixed α cause no collision-integrability problem. The raw Gaussian variables never define the physical competitor.

## 5. Entropy coefficient without a flat-boundary diffusion estimate

Consider F_s(Z)=(x=Z0,w=DZ/√s), whose inverse determinant is s^d. Its density q_s is

 q_s(x,w)=s^(−d/2)∫_Q f(t) G_C(t)((x−t)/√s,
                         (x−t)/√s+w1,(x−t)/√s+w2)dt.

Uniform ellipticity and boundedness of f imply, by integrating the common shift,

 0<q_s(x,w)≤B exp(−b|w|²),                                (R7)

uniformly in x and 0<s≤1. Substitution t=x+√s v and dominated convergence give local uniform convergence on Q×R^(2d) to

 q_0(x,w)=f(x)G_A(x)(w).                                   (R8)

This Gaussian integration marginalizes S in its h coordinates, hence gives covariance A, not the conditional Schur complement of A. Gaussian tails and continuity of f,C justify uniform convergence on compact subsets. The same random-variable representation gives weak convergence and convergence of second moments: x=T+√sU0 and w=DU have uniformly integrable Gaussian moments, with E|w|²=∫f tr A exactly.

Here is the full entropy step. Comparison to a fixed positive Gaussian and convergence of second moments give liminf H(q_s)≥H(q_0) by lower semicontinuity of relative entropy. On every compact rectangle inside Q×R^(2d), (R8) and positivity give uniform convergence of log q_s. On its complement log q_s≤log B by (R7), so

 limsup H(q_s) ≤ ∫_J q_0 log q_0+(log B)(1−q_0(J)).

Exhaust Q×R^(2d) by rectangles with null boundary. The integral of |q_0 log q_0| is finite because ∫f|log f|<∞ and A,A⁻¹ are bounded. Hence H(q_s)→H(q_0). At each fixed s the entropies used here are well-defined: restricting the t integral to an inner ball of positive f mass yields a Gaussian lower bound with constants allowed to depend on s; finite second moments bound the negative log integral.

It follows that

 H(Γ_s)=d log(1/s)+H(f)−d log(2π)−d
                    +(1/2)∫f log det K+o(1).              (R9)

Also H(g_s)→H(f): Jensen for convolution gives H(g_s)≤H(f), and a Gaussian-reference lower semicontinuity argument with second moments gives the reverse limiting inequality.

Since the repair is a product Borel isomorphism, relative entropy is invariant, so EXACTLY

 KL(P_s|ν³)=KL(Γ_s|g_s³)=H(Γ_s)−3H(g_s).

Combining with (R9),

 KL(P_s|ν³)=d log(1/s)−2H(f)−d log(2π)−d
                       +(1/2)∫f log det K+o(1).           (R10)

Thus the entropy error is o(1), at the same s for which cost error is o(s). This is stronger than a merely leading-log estimate. No parameter-uniform remainder, positive-boundary-density assumption, or claim about fluctuations of the true minimizer is involved. The tangential variance β disappears on integrating the common shift; it contributes no spurious coefficient.

## 6. The full frozen conclusion, with its original coefficient

Apply the construction separately to A_k=K_k⁻¹ for k=1,2, with one large β if desired. Push to the physical ordered cells, give each branch weight 1/2, and average over six permutations. Exact latent marginals give exactly μ in every physical coordinate. The twelve ordered component cells are disjoint, with recovery mass 1/12 and μ³ reference mass 1/108. Therefore

 KL(π_s^rec|μ³)=log 9+(1/2)∑_k KL(P_s^k|ν³),
 ∫c_α dπ_s^rec=E+d s+o(s).

At s=ε this gives the recovery objective

 E+d ε log(1/ε)+[log9−d log(2π)−2H(f)
                   +(1/4)∑_k∫f log det K_k]ε+o(ε).

It gives the author's exact C_*, with matching separate recovery cost and entropy, for ALL the fixed-data quantifiers. No source geometry is changed or made smaller in this reduction.

The remaining clauses compose with paid operations as follows. A fixed positive s has finite entropy by (R9)'s fixed-time bounds and exact reference invariance; its physical cost is bounded on the separated cells. Thus there is a finite competitor for every ε>0. Compactness, lower semicontinuity and strict convexity give all-positive-ε existence and uniqueness. Permutation invariance plus the exact source contact certificate determines the sole symmetric zero-temperature plan: the outer Y_k marginal forces the branch measure to be ν/2. The recovery upper bound then gives weak convergence of minimizers to that plan.

For the matching lower coefficient use exactly the paid Laplace/relative-entropy operation written in author Section 8. The finite measures τ_ε=ε^(−d)e^(−R/ε)μ³ converge to a measure on the twelve contact graphs, whose ordered-k density in t is (2π)^d f(t)^3/(108√det K_k(t)). Forbidden component patterns have a strictly positive slack minimum and contribute exponentially little, including patterns with collisions. The symmetric optimizer has density f/12 on each graph. Joint relative-entropy lower semicontinuity gives the lower coefficient KL(π_0|τ)=C_*. This uses the full covariance determinant, not just normal dimension. Finally the two fixed-ratio concavity secants in author Section 9 recover KL=d log(1/ε)+C_*−d+o(1); subtracting εKL from the value gives cost E+dε+o(ε). There is no differentiation of an unspecified remainder.

## 7. What this establishes for contribution

The full correlated trim/subcoupling and multi-marginal completion possibility must be credited. Cardoso-Perelló–González-Sanz–Nutz's actual upper proof makes symmetric two-marginal subcouplings and quantizes a common residual. An arbitrary three-coordinate correlated trim need not leave identical residual measures; its extension cannot simply be declared proved by changing a subscript. Conversely that bookkeeping issue cannot justify an unpaid-operation claim. The explicit untrimmed correlated Gaussian plus exact multi-marginal shadow above is an alternative full-scope constructive completion. It closes the simultaneous constraints with o(ε) cost and o(1) entropy compatibility and no residual balancing conjecture.

The algebra, Gaussian profile, scalar heat quantiles, relative-entropy invariance/data processing, stationary finite-Fisher mechanism, source geometry, Laplace lower bound and secants are paid elementary or actual antecedent operations. Their composition here does not leave a new analytic operation requiring the submitted coupled singular-drift SDE or its parametrix entropy transfer. That is the positive basis for a TECHNICAL contribution disposition; absence of a matching headline theorem, failed independent noises, proof length and terminology play no role. An exact previously published T373E135 theorem has not been established by this review, so this is not a REDISCOVERY or priority claim.
