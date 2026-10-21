# PREFREEZE: an integrated norm refinement, not a nominee

Provenance: Codex / GPT-6 Astra / high / default service tier. The two Source324 manuscripts and every operative proof at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. All twenty canonical TeX/Bib objects were read before this note. Actual Kalton2004, GK2003, ANPPv3, KPv2 and Sari2026v2 proof windows, and original I88/r94 windows, precede this drafting. This is feasibility work; no theorem has been frozen or assigned a mathematical grade.

## 1. Exact data retained from the companion

Keep the companion's actual countable coordinate set D=E⊕∞U, E=c0, U=c0 of its finite row blocks; its norm unit ball B; all weights with eta=10^-3; finite coordinate sets I_gamma; grid widths d_j; positive scales rho_j and ell_j; and the concrete test classes T_h,V_h. In particular all operations use their original representing labels, chronological nonincreasing dyadic scales, strict total budget <ell_j/2, and tail factors. No equivalence of distinct presentations is asserted.

Keep the enumeration d=(L,C,p), p=1+1/k, of admissible test-list seminorms sigma_d. Lists, including repeated labels, are admitted precisely when sum |u_n(s)-u_n(t)|≤C||s-t|| for every pair in B. Original alpha_d=2^-d/C_d^2. Let s=sum_(d≥1)2^(-d/2)=1+sqrt(2), and beta_d=2^(-d/2)/(s C_d). Thus beta_d>0, sum beta_d C_d=1, and sqrt(alpha_d)=s beta_d.

On mass-zero finite molecules define

    N_1(m)=sum_d beta_d sigma_d(m).

This is an outer ell1 refinement of the actual molecule seminorm, not an external direct sum of independently constructed absorber spaces. It is explored to strengthen the linear obstruction while preserving the full global nonlinear construction.

## 2. Completion, all tests, and a canonical injection

The source point-increment estimate sigma_d(delta_x-delta_y)≤C_d||x-y|| gives N_1(delta_x-delta_y)≤||x-y||. Every finite molecule is a finite sum of such differences, so N_1 is finite, subadditive and homogeneous. Its kernel is exactly the old kernel N, since every coefficient beta_d and alpha_d is positive. Let Z_1 be the Banach completion of M_0(B)/N in N_1.

Write A_d for the completion of M_0(B)/ker(sigma_d) in its seminorm quotient. The linear map

    J_1 m=(beta_d [m]_d)_d in (⊕ A_d)_ell1

is isometric for N_1. Its extension identifies Z_1 with the closed span of these actual vectors, so

    ||z||_1=sum_d beta_d sigma_d(z)

holds exactly after completion. Each coordinate seminorm is beta_d^-1-Lipschitz. This is a linear realization; it avoids treating the nonlinear tuple (sigma_d(z)) as a linear operator.

The original norm satisfies

    ||m||_Z=(sum_d alpha_d sigma_d(m)^2)^(1/2)
             ≤s sum_d beta_d sigma_d(m)=s N_1(m).

Hence the identity on molecules extends to a bounded linear j:Z_1→Z, ||j||≤s. For each d, continuity on both completions gives sigma_d(jz)=sigma_d(z). If jz=0, all these seminorms vanish, so the exact ell1 formula gives z=0. Thus j is injective and has dense range. No lower norm bound, closed range, surjectivity, or linear isomorphism is asserted.

Every test in a fixed source class L is uniformly bounded on Z_1: choose d_L=(L,C_L,2) with C_L bounding its Lipschitz constants. Singleton admissibility gives |u(z)|≤beta_(d_L)^-1||z||_1. For a fixed d, all admissible list evaluation maps have norm≤beta_d^-1 into ell_p. Uniform boundedness of those maps and density retain the exact list formula on Z_1. Pointwise convergence in a fixed class converges against each fixed z by finite-molecule approximation, with error at most 2 beta_(d_L)^-1||z-m||_1. Thus all three source support-selection branches retain their hypotheses. More economically, whenever a weakly null sequence z_i in Z_1 has scalar detectors, jz_i is weakly null in Z and the source compatible-detector proposition applies directly to it; pairings are unchanged. This avoids any assertion of weak convergence uniform over moving tests.

## 3. The entire global absorption map survives

Let zeta_1(s)=[delta_s-delta_0] in Z_1. It is 1-Lipschitz and zeta_1(0)=0. For d_0=(T_1,C_0,2), with integer C_0≥4+12eta, define Q_1 on finite molecules by the actual c0-valued correction sum sum a_s h(s). Every coordinate f_gamma is a singleton test for d_0, so

    ||Q_1m||_U≤sigma_(d_0)(m)≤beta_(d_0)^-1 N_1(m).

It descends and extends into the complete space U, not just ell_infinity. Here Q_1 denotes this new-space correction, not the baseline manuscript's graph operator with the same notation. Let q_1=||Q_1||≤beta_(d_0)^-1. Then Q_1 zeta_1=h, Q j=Q_1, and j zeta_1=zeta. Define K_1(0)=0 and K_1(x)=||x|| zeta_1(x/||x||). The source two-point normalization estimate gives Lip(K_1)≤3, with jK_1=K and Q_1K_1=g-P exactly.

The SAME state-dependent shift g is already globally onto, with lower constant c_g=1/5-24/1000=22/125 and upper constant 5+24/1000=628/125. Its finite-row terminal scalar/Brouwer proof is retained in full: no new uniformity in weights is presumed.

Consequently the source general absorption lemma applies on the newly completed space:

    F_1(b,t)=b+K_1(t,Q_1b),
    (t_d,u_d)=g^-1(Q_1d),
    F_1^-1(d)=(d-K_1(t_d,u_d),t_d).

Both inverse identities hold because Q_1(d-K_1(t_d,u_d))=u_d. They require neither surjectivity of Q_1 nor a Lipschitz right inverse for it. All-pair constants are

    Lip(F_1)≤1+3 max(1,q_1),
    Lip(F_1^-1)≤max(1+3q_1/c_g,q_1/c_g).

Separable B and the point estimate make Z_1 separable. Positive homogeneity is inherited from K_1 and g, but smoothness and complex linear structures are not added. We also have the exact commuting identity

    j F_1(b,t)=F(jb,t).

This is a compatible dense linear refinement of the same nonlinear construction, not a claim that the old and new completed norms are equivalent.

## 4. Fixed-class detection for EVERY normalized weakly null sequence

Let (z_i) be weakly null in Z_1 with ||z_i||_1≥r>0; boundedness supplies ||z_i||_1≤M. Suppose sigma_d(z_i)→0 for every fixed d. Their linear images J_1z_i in the ell1 sum above are weakly null and coordinatewise norm null. Choose increasing indices i_k and disjoint consecutive coordinate intervals I_k such that the restriction w_k of J_1z_(i_k) to I_k satisfies

    ||J_1z_(i_k)-w_k||<epsilon_k,  ||w_k||≥r-epsilon_k,

where epsilon_k>0, sup epsilon_k<r/4. To construct this, make the finite head small using coordinatewise norm convergence, then choose a finite tail cutoff for that fixed vector. The w_k have disjoint supports. For every finite scalar family (a_k),

    ||sum a_k J_1z_(i_k)||
      ≥sum |a_k| ||w_k||-sum |a_k| epsilon_k
      ≥(r/2)sum |a_k|,

and the reverse estimate is M sum |a_k|. This is an ell1 basic subsequence, impossible for a weakly null sequence: on its closed span the functional taking each J_1z_(i_k) to 1 is bounded by the displayed lower estimate and extends by Hahn–Banach. Therefore some d=(L,C,p) has sigma_d(z_i)≥a>0 on a subsequence.

Choose p'=1+1/k'<p with the SAME L,C. B_0=beta_(d')^-1 M bounds sigma_(d')(z_i). A list for d evaluating to at least a/2 has one term F_i satisfying

    |F_i(z_i)|≥delta=[(a/2)^p/B_0^(p')]^(1/(p-p'))>0.

This is the source interpolation calculation, now available without bounded signed sums because outer ell1 excludes escape already under weak nullity. Apply source prop:compatible-detectors to jz_i. Obtain a subsequence, fixed class L_1, common signed Lipschitz bound C_1, and tests v_i with |v_i(z_i)|≥delta_1>0. No change to the source's nested-cylinder/repeated-label proof is required.

## 5. What the compatible tests actually imply

For every listed exponent q>1, d_q=(L_1,C_1,q) defines a bounded linear map

    T_q:Z_1→ell_q, T_q z=(v_i(z))_i,
    ||T_q||≤beta_(d_q)^-1.

Finite admissible lists and monotone convergence prove membership, including for the completed vectors. The constants depend on q and may diverge as q decreases to 1.

For a finite set H of n selected indices and independent real signs, convexity and symmetry give, for each k in H,

    E |sum_(i in H) epsilon_i v_k(z_i)|^q ≥ |v_k(z_k)|^q.

Indeed condition on the other signs and average the kth sign: (|y+a|^q+|y-a|^q)/2≥|a|^q. Hence

    E ||sum_(i in H) epsilon_i z_i||_1^q
        ≥ beta_(d_q)^q n delta_1^q.                  (A)

This recovers exclusion of c0: its basis images have bounded signed sums. It also excludes a linear embedding of ell_t for EACH 1<t<infinity: its basis is weakly null, and signed sums of n images have norm≤||T|| n^(1/t); choose listed q<t in (A). Then beta_(d_q)^q delta_1^q n≤||T||^q n^(q/t), a contradiction for sufficiently large n. This includes t=2; it is not a claim about the Hilbert-domain free space of the other manuscript.

More generally a seminormalized weakly null sequence satisfying an upper Rademacher type-t estimate cannot exist here for any t>1. Choose 1<q<t and use Jensen/Lyapunov to bound the left of (A) by a constant times n^(q/t). This assertion is conditional on the explicit sequence estimate and requires no unproved claim that all reflexive spaces have nontrivial type.

The no-c0 and absorption conclusions imply the same-space metric universality already paid by the source plus Aharoni. The extra ell_t exclusion follows by the displayed norm modification, the standard ell1 gliding hump, the ORIGINAL full selector, and a change of exponent in the source random-sign argument. These calculations are not submitted as a substantial theorem. They introduce no newly solved compatibility mechanism inside the difficult source selector. No inference of Schur, reflexivity, duality, AP, BAP, cotype, or intrinsic label recovery follows.

## 6. Why this is still PREFREEZE

The mathematically serious residual tested next is whether the correction can be lifted into a Schur completion with global Lipschitz constants. The construction above removes escape among norm coordinates but still yields only ell_q-valued detector maps for q>1. Weakly null unit vectors in ell_q show why that output alone is insufficient. The exact endpoint attempt and its strongest primary comparisons are recorded separately. No reduced version of old S88 (the coupled AP/no-BAP target), Q88, a classification target, or a previously frozen scope is being proposed. All old targets stay unchanged.
