# Integrated tuple calculation — PREFREEZE, no nominee

This is a working reduction through stipulated Source202 operations, not a frozen author-proof submission, independent grade, acceptance, or priority claim. It retains the ordinary commutator relation and does not solve or weaken G104/TD. Before this calculation: all eight Source202 sections and its root/bibliography, I104 §§3–6, I108 §§4–5, I110 §§2–5 (with truncation recovery), BBY's complete author paper, HY's complete author paper, and Klug's printed141–148 were read. Primary transitive inputs not read are listed separately.

## 1. Precise counting convention

Fix a prime p and a finite group J with O_p(J)=1. Put m=|J| and D_J=|J|/|Z(J)|. Write C_1,...,C_r for all conjugacy classes of J, including the identity class. For a vector b=(b_1,...,b_r) of nonnegative integers, N=sum b_i>0, let U_J(b) count simultaneous J-conjugacy classes of ordered tuples

    (x,y,u_1,...,u_N),  [x,y]u_1...u_N=1,
    <x,y,u_1,...,u_N>=J,

with exactly b_i puncture entries in C_i. There is no quotient by permutations of positions. The present calculation assumes at least one active C_i is p-singular. Other active classes may be p-regular, including identity. An empty tuple set counts as zero. Put s=v_p(N).

The source states its tuple theorem for N=p^s and every active class p-singular. Its full construction allows the following broader compatible parameters, by the detailed substitutions below. No new index, differential, descent, or connectedness lemma is introduced.

## 2. Separate label count N from divisor index p^s

For the asymptotic comparison assume s>=1. Use the source ordinary elliptic curve A/kappa, kappa=Fbar_p, and a point P of exact order p^s. Let

    F'=kappa(A^N),  sigma(t_i)=t_(i+1)-P  (indices modulo N).

The Nth power of sigma is identity since NP=0. Every smaller positive power moves an independent projection to a different projection, so sigma has exact order N. Set F_0=(F')^<sigma>. This is a cyclic Galois extension of degree N, not necessarily a p-power. Both fields have transcendence degree N over kappa.

On A_(F') use delta(z)=sigma(z)+P. Its Nth power is identity. The two disjoint invariant reduced divisors are

    B_(F')=sum_(i=1)^N[t_i],
    D_(F')=sum_(j=0)^(p^s-1)[jP].

Their degrees differ: deg B=N, deg D=p^s. Do not use N repetitions of the origin orbit, which would fail the source disjoint-section condition. The canonical linearization of O(D) and the source projective descent give E/F_0 and the two divisors, with D ample.

For any signed divisor Z of degree b on E, the full geometric cycle sum v belongs to A(F') by source lem:cycle-sum-rationality, including inseparable multiplicities. Source lem:constant-product-maps writes

    v=c+sum_(i=1)^N beta_i(t_i).

The descent equation sigma(v)+[b]P=v forces beta_i=beta for all i, by varying each factor independently. The N translation terms then sum to beta([N]P)=0, hence [b]P=0 and p^s divides b. The actual divisor D has degree p^s. Thus the index is exactly p^s. This uses the source proof with two parameters; no new period-index theorem is needed.

If F/F_0 is finite with [F:F_0]_p<=p^h, pushforward of divisors retains the same full residue-degree identity. Every divisor degree over F on E_F, or on a finite regular cover of it, is divisible by p^(s-h). If S=FF', then S/F is finite Galois of degree dividing N and

    [S:F']_p [F':F_0]_p = [S:F]_p [F:F_0]_p,
    [S:F']_p <= [F:F_0]_p <= p^h.

The N forms t_i^*eta are a basis of Omega_(F'/kappa). The source transitivity sequence therefore loses at most h independent directions after passage to S, just as before. It does not require the entire splitting degree to be a p-power.

## 3. All geometric compatibility steps

The source height-one kernel/cokernel and determinant formulas are unchanged. The tangent bundle has rank N+1, and an image of rank N+1-m_j constrained by c independent labels still loses at most h+m_j negative summands. The same tower recurrence gives

    nu(Z)/d >= sum_(i=1)^N(1-1/r_i) - (h+log_p d).

Both terms after multiplication by d are degrees of divisors over F, not merely over S. The absolute determinant and the reduced inverse image of B retain full inseparable residue degrees. Thus their difference is a multiple of p^(s-h). For every d<=m the same exact rounding holds once

    s>=max(1,h),  p^(s-h)>m(h+log_p m).                    (A)

It is uniform in N's prime-to-p factor and in the class multiplicities.

The mixed-characteristic lift uses a p^s-torsion lift of P, a product with N factors, and the degree-N cyclic field automorphism. Its residue action is faithful of degree N, so the degree sandwich and finite-etale ring descent in prop:mixed-lift still hold. The divisor D has p^s distinct sections. Its disjointness from the N generic labels is unchanged. The spherical-base construction and full field/residue degree equality use no assertion that N is a p-power. Roots of unity for |J| are still contained in the base. The proof of lem:residue-permutations compares the same cyclic Galois groups by its degree sandwich; a prime-to-p factor in N changes none of the inequalities.

The marked-cover classification allows a label to be unramified. Its inertia generator is then identity. Galois preserves all local conjugacy classes because the base fixes the relevant roots of unity; it preserves any prescribed multiset containing at least one singular class. In prop:small-orbit-descent, O_p(J)=1 implies p does not divide |Z(J)|. A Sylow subgroup of the central extension of the orbit stabilizer supplies the same descent datum. A Sylow orbit of size <p^h still gives [L:K_s]_p<p^h and the same bound for its full residue extension.

In the specialization proof replace the degree of the ample divisor by d_D=p^s while retaining N as the number of labels. The two leading section terms become j*m*d_D and j*d_D*sum_w m_w. Letting j grow still proves sum_w m_w=m. The selected-vanishing comparison cancels these same leading terms; no equality between deg D and number of labels was used. The genus sums still run over all N labels.

Put q_i=1/(r_i a_i), z_i=1/e_i and delta_i=1_(p divides a_i). The identical three comparisons give

    0 >= sum_i (|q_i-z_i|+delta_i q_i) >=0.

This calculation never used p|e_i for every i. It yields r_i a_i=e_i and p not dividing a_i for every label, including e_i=1. At the one (or more) singular label, p|e_i forces r_i>1, hence d=|I_w|>1. Equality of Euler characteristics gives the source finitely presented model. Connectedness forces a single valuation, so I_w is a nontrivial normal p-subgroup of J, a contradiction. Consequently every Sylow orbit has size divisible by p^h.

Thus the integrated source construction pays p^h|U_J(b) whenever (A) holds and the support contains at least one singular class. It supplies an explicit asymptotic reduction, not a new geometric estimate. In particular, stopping at the printed power-length/all-singular theorem statement would understate the actual input.

## 4. Classical mixed moments and removal of accessibility

Choose a finite p-adic field K containing the ordinary character values of every subgroup of J. Let O be its integers, e its absolute ramification index, and F_Q its residue field, Q=p^f. For H<=J and all J-classes C_i set

    W_(H,i)=sum_(g in H intersect C_i)g,
    lambda_(H,chi,i)=the central scalar of W_(H,i) on chi.

These are integral scalars. Let mu(H,J) be the Mobius function on the lattice of actual subgroups and M(b)=N!/prod_i b_i!. The source trace normalization, Klug's central convolution formula, and I108's complete mixed-moment operation give

    U_J(b)=M(b) F(b),
    F(b)=1/D_J sum_(H<=J) mu(H,J)|H|
                  sum_(chi in Irr(H)) prod_(i:b_i>0) lambda_(H,chi,i)^b_i.   (B)

This is the untwisted formula; all ordinary labels are retained. For a single fixed ordered word of class labels, F(b) is its generating simultaneous-orbit count, hence is itself a nonnegative integer (I110 §2.3). Indeed subgroup Mobius inversion enforces generation and the stabilizer of a generating tuple is exactly Z(J). Centrality of W_(H,i) makes every class-label ordering have the same count. No modular division by a multinomial is made.

Write omega_(H,chi,i) for the Teichmuller lift of the residue of lambda, with [0]=0. For a nonempty support I containing a singular class and an arbitrary vector rho_i modulo Q-1, set

    Theta(I,rho)=1/D_J sum_H mu(H,J)|H| sum_chi
                     prod_(i in I) omega_(H,chi,i)^<rho_i>,                 (C)

using positive representatives, also when rho_i=0. This convention makes a zero coordinate contribute zero. When Q=2 there is one residue and the representative is 1.

Choose any positive integers b_i representing rho_i on I (zero elsewhere), with no constraint on their total. Dilate by p^(kf). The total length has p-valuation tending to infinity; the support still contains a singular class. Section3 therefore gives U_J(p^(kf)b)->0 p-adically. Legendre's factorial formula gives

    v_p(M(p^(kf)b))=v_p(M(b)).

Unit powers converge to their Teichmuller parts along kf; nonunit powers converge to zero. Hence F(p^(kf)b)->Theta(I,rho). Equation (B) and the constant multinomial valuation force this limit to be zero. Thus every (C) in this exact untwisted scope vanishes. I108 needed accessible residues because it used only totals p^s; the compatible geometric parameter change above pays their removal. This is not the Galois-twisted moment identity: there is no condition chi^gamma=chi in (C).

## 5. Pay the strongest elementary local-unit rate

Normalize v_p(p)=1. Define

    k0=min{k>=0 : (p-1)p^k >= e}.

For every alpha in O with Teichmuller lift omega and every positive integer a with k=v_p(a),

    v_p(alpha^a-omega^a) >= k-k0+1/e.                    (D)

For a unit, alpha/omega=1+z has v_p(z)>=1/e. A pth-power step gives the lower bound min(pv,v+1) for the new error valuation. Until stage k0, the iterative lower bound is p^j/e; at k0 it is at least 1/(p-1), after which each step raises the bound by 1. For k>=k0 this gives k-k0+p^k0/e, hence (D); for k<k0 its right side is <=0 and (D) is automatic. For a nonunit, omega=0 and the valuation is at least p^k/e. For k>=k0 use p^u>=1+(p-1)u and p^k0/e>=1/(p-1); the other case is again immediate. Passing from p^k to a positive multiple does not lower the error valuation, by factoring A^u-B^u. This proves (D) also for p=2 and the boundary valuation 1/(p-1).

Set d=v_p(D_J), c=v_p(M(b)), and k=min_(i in I)v_p(b_i). Telescoping the integral products in (B), subtracting (C)=0, and dividing by D_J give

    v_p(F(b)) >= k-k0+1/e-d.

For each active i the exact integer identity

    b_i M(b)=N (N-1)!/((b_i-1)! prod_(j!=i)b_j!)

gives c+v_p(b_i)>=s=v_p(N). Hence

    v_p(U_J(b)) >= s-k0+1/e-d,
    v_p(U_J(b)) >= max(0, s-k0-d+1),                     (E)

where the last step uses that U_J(b) is a nonnegative integer and v_p(0)=infinity. This is uniform in all multiplicities and all lengths, under the stated one-singular-support hypothesis. No extrapolation from finite checks is used.

An optional explicit coefficient choice is K=Q_p(zeta_exp(J)), which contains all ordinary character values and the integral central scalars. If p^a is the p-part of exp(J), then a>=1 in the nonvacuous case. The p'-roots give an unramified extension; Phi_(p^a)(1+T) is Eisenstein over it, with degree e=p^(a-1)(p-1). Thus k0=a-1. Since O_p(J)=1 implies p not dividing |Z(J)|, d=v_p(|J|). Formula (E) reads

    v_p(U_J(b)) >= max(0, v_p(N)-a-v_p(|J|)+2).          (F)

The general-field version (E) does not need this optional cyclotomic normalization. The cyclotomic facts are classical; no separate efficient character-field algorithm is claimed.

## 6. Operation accounting and boundary

The paid chain is: source translated cyclic twist and index + source label-rank/genus rounding + source full-residue descent and exact specialization + classical central convolution and subgroup Mobius inversion + the already developed I108/I110 Teichmuller/multinomial mechanism + the elementary stronger binomial rate. All compatibility steps are recorded above rather than inferred from titles. The resulting parameter gain does not identify a new nonroutine operation after these strongest constructions. It is therefore retained as exploratory reduction, without nomination, self-grade, or a claim that it is absent from the literature.

For a coefficient-Galois refinement, the moment would instead sum over chi fixed by gamma_t. Neither changing N nor allowing tame labels changes the handle relation [x,y]U=1 to U y^t=xyx^-1, or inserts that fixed-label selector. Even full vanishing of every untwisted moment (C) retains only scalar spectral masses. It does not determine the cyclic action inside a scalar residue fiber. I110's A4 example and explicit projector calculation remain the operative old boundary. HY's minimal-field inverse bimodule morphisms would already supply a relevant Galois correspondence, but this computation constructs none. These missing comparisons are not findings or general impossibility statements, and the old full G104/TD scopes remain unchanged.
