# Route B: diagonalize before selection, then retain temporal structure

We use source083's local slope operator H_a^ε=∫_{ε<|t|<a}V_t dt/t, V_t=C_tS_t^x, |u|≤1, Lip(u)≤C_Lip, aC_Lip small. This is an intermediate local interface, not a replacement of the full unit-field target. Let P_w be the source's real vertical square partition Σ_w P_w²=Id. All statements below first use finite frequency inputs and positive cutoffs; density/strong limits give the indicated operators.

## The off-diagonal maximum is already paid

For every finite set of dyadic w and arbitrary signs, source red:composition-commutator gives

    ||[Σ_w σ_w P_w,V_t]||2→2 ≤ C|t|.

Random-sign orthogonality therefore yields

    Σ_w ||[P_w,V_t]f||2² ≤ C²t²||f||2².

The square-partition synthesis map (h_w)↦Σ_w P_wh_w is a contraction from L2(ℓ2) to L2. Hence

    R_t := V_t−Σ_w P_wV_tP_w = Σ_w P_w[P_w,V_t],
    ||R_t||2→2 ≤ C|t|.

The sums converge in L2: synthesis is bounded and the commutator sequence is square summable. The original diagonal sum also converges by boundedness of V_t and Σ||P_wf||2²=||f||2². Consequently

    D_a^ε := ∫_{ε<|t|<a} Σ_w P_wV_tP_w dt/t,
    ||sup_ε |H_a^εf−D_a^εf|||2
       ≤ ||∫_{|t|<a}|R_tf|dt/|t|||2 ≤ 2Ca||f||2.       (B0)

This integrates first and only then selects ε at the output. It never commutes P_w with a measurable cutoff mask. It is compatible with the r63 counterexample to[P,H^{ε(z)}]=O(a).

This is a technical consequence, not an unpaid new bridge: DPGTZK Theorem1.1 gives the stronger ℓ1 off-diagonal bound for small bi-Lipschitz changes, and its actual §2.5 proof of Corollary1.3 uses the same absolute-time integral and Lipschitz factor. We read that primary proof here and exclude(B0) from nomination.

What remains is the exact diagonal maximal estimate

    ||max_{1≤j≤N}|Σ_w P_w H_a^{ε_j}P_w f|||2 ≤ C||f||2,       (B)

uniformly for every N, all0<ε_j<a, every permitted u and all frequency collections. Infinite dyadic sums are taken in their strong L2 sense for each fixed ε_j. Equivalently, for every measurable disjoint partition E_1,...,E_N and |g|≤1_E, one needs a restricted estimate for

    Σ_{j,w} <H_a^{ε_j}P_w f, P_w(1_{E_j}g)>.

A constant in(B) independent of N and frequency range would, with(B0), solve the intended maximal reassembly and the full unit-field target. In the local rotation v_1≥c>0, reparametrize the variable inner cutoff εv_1(z) directly inside the supremum; there is no need to estimate a separate lower-endpoint error. The outer endpoint av_1(z) differs from a only inside the fixed annulus ca<|s|<a, whose absolute integral has bounded L2 norm by fixed-time composition and Minkowski. Localize to bounded-overlap squares as in the source. This pays the local-to-global step for the maximal question. It has not been proved. The elementary finite-N bound from the stipulated fixed-truncation theorem is C sqrt(N); it does not suffice as N→∞.

## Why a band maximum plus fixed-operator L2 is insufficient

Here is an exact obstruction to a generic inference, not a model of Hilbert time truncations. Take a nonzero Schwartz φ on R with Fourier support in(−1/10,1/10), and f_k(y)=exp(i2^{k+2}y)φ(y), k=1,...,K. Their spectra are disjoint. For each σ∈{−1,1}^K define A_σ to be the multiplier which equals σ_k on the kth spectrum and0 off their union. Every ||A_σ||2→2≤1. On each individual band,

    sup_σ|A_σ f_k|=|f_k|,

so the single-band maximal bound has constant1. For the combined input f=Σ_k f_k,

    sup_σ |Σ_k σ_k f_k(y)| ≥ (2/π)Σ_k |f_k(y)|
                              = (2/π)K|φ(y)|.

Indeed maximize the real projection onto angle θ and then average θ, using average|cos θ|=2/π. But ||f||2=sqrt(K)||φ||2. Thus the full maximum has norm ratio at least(2/π)sqrt(K)=(2/π)sqrt(log_2 N), where N=2^K. Exact band diagonalization, fixed L2 bounds and individual band maxima do not imply(B). Time-order structure of actual truncations must be used, rather than replacing the operator family by arbitrary bounded band-diagonal maps.

## A fresh mechanism examined: common cutoff through dual projection

For dyadic time length ℓ, the selected test in the dual diagonal form is

    g_{w,ℓ}=P_w(1_{r<ℓ}g),

where r(z) is the chosen cutoff. This is not the source's single common test g_w. Rewriting by self-adjointness instead places P_w on the analyzing packet-amplitude product:

    <b_s(u)Ψ_s, P_w(1_{r<ℓ_s}g)>
       = <P_w(b_s(u)Ψ_s),1_{r<ℓ_s}g>.

The source selector has |b_s'|≤C/d_s=Cℓ_s/w. For any fixed vertical P_w with Schwartz kernel, the exact elementary commutator estimate is

    ||[P_w,M_{b_s(u)}]||2→2
       ≤ Lip_y(b_s(u)) ∫|h||p_w(h)|dh ≤ Cℓ_s.            (B1)

Thus one can move a smooth selector past P_w at an individual-packet cost proportional to ℓ_s, avoiding the false measurable-mask commutator. If an enlarged P_w is1 on the packet spectrum, the main packet remains unchanged. For the square partition used in(B0), replace Ψ_s by P_wΨ_s; it remains a uniformly adapted packet. This is an actual interface worth pursuing, but(B1) alone cannot be summed over arbitrary tiles and all widths by counting terms. We have not proved the required global Bessel/Carleson estimate for that error family.

The residual main form still has all vertical widths simultaneously, common cutoff r, and scale-dependent tests. At fixed width r63's coefficient lemma controls the suffix cutoff by intersection with an interval. It is not a multiwidth theorem. Source conc:coefficient-carleson uses a reference box with one fixed W=mw; its polynomial-weight integral is proportional to rW. Source hier:complex-transition-motion has velocities1/l_T and(s_R−s_T)/W; its small phase motion uses |v|/W≤CB/(m sqrt(G)) at a cell size proportional to w. For widths w_1,...,w_K those cell sizes differ. A common cell based on the largest width can incur w_max/w_min in the smallest-width motion bound. Taking the smallest cells avoids that factor but does not by itself supply the required uniform weighted path packing or exceptional-set measure. No claim of impossibility is made.

A concrete sufficient missing target is a selected, multiwidth restricted estimate with the source's summable disparity gain:

    |Σ_w <D_{w,r} f,g>|
      ≤ C sqrt(|F||E|)/(1+|log(|F|/|E|)|)^3,             (B2)

for all finite width families, all measurable r:(R²)→(0,a), |f|≤1_F, |g|≤1_E and local horizontal supports, with D_{w,r}f(z)=[P_w H_a^ε P_wf](z)|_{ε=r(z)}. Constants must be independent of the width ratio, N and the number of time scales. The existing restricted-to-strong summation would then pay the L2 bound. This asks for the actual projected hard-cutoff operators, so it does not silently omit the further smooth-model/hard-cutoff error. If proved only for source smooth dyadic models, one must additionally bound their maximal hard-cutoff difference; source red:scale-truncation supplies only fixed-endpoint L1 control. The resulting positive line-average supremum is another unpaid estimate.

No(B), (B2), global(B1) summation, or complete selected hierarchy has been established in this round. These are quantified remaining obligations, not assumptions hidden inside a claimed theorem.
