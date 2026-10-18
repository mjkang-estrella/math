# Separate attempt: weight particle densities and retain the total field

Myeongjin Kang; original prose CC BY 4.0. This supplement was developed after `screen-362.md` was saved and after the parent suggested avoiding the shell-field decomposition. The original split-field failure does not eliminate this distinct route. No global theorem is claimed.

Keep the initial-label partition f=Σ_j f_j, a_j=||f0,j||∞, but do NOT split the Maxwell fields. The source's total cone and spatial field budgets remain valid, and dominate all shell particle-energy contributions. The transport equation for each f_j still has the total force. There is no cross-work defect introduced into the field budget by this arrangement.

The actual `direct.tex` single-bin proof can be weighted before any unsupported bootstrap assertion. For N_j=∫bin f_j dv and shell hit measure M_j it gives

    N_j≤C a_j p³ν²,
    ∫N_j²≤C min(a_j² I h φ²p⁶ν⁴,
                         a_j p³ν² M_j/(h²φ²)).                 (A)

Here the variables, geometry and bin cutoff are those of the source. In its near/far table, the near T_r,T_perp bounds gain a_j; their far bounds still use M_j. The near S_g,S_b bounds gain a_j, while their far bounds gain sqrt(a_j) relative to the displayed sqrt(p M_j) factors. All field budgets G_phi,F_phi are TOTAL-field quantities, unchanged.

CONDITIONALLY on the source stable-cell occupation estimate M_j≤C h k1 R²/p (obtained simply by bounding the shell occupation by the total occupation on that same admissible cell), balancing h and h^−1 for T_perp yields an a_j^(1/2) gain. Balancing h^(1/2) and h^(−1/2) for S_g,S_b yields an a_j^(3/4) gain. In detail their balanced bounds are the three rows of `dir:balanced` multiplied respectively by

    a_j^(1/2),       a_j^(3/4),       a_j^(3/4).                (B)

The powers follow by multiplying the two constants and taking a square root: a_j times 1 for T_perp, and a_j times a_j^(1/2) for the field terms. These statements are conditional bin calculations, not a proof that the stable cells exist uniformly for infinite momentum support.

For any fixed k>0 and β>0, the positive weights genuinely remove the need for a moving cutoff in polynomial momentum sums. On a normalized growth interval q(V)≤Λ q0,

    Σ_j a_j^β Σ_{dyadic p≤CΛ2^j} p^k
       ≤ C_k Λ^k Σ_j a_j^β 2^(kj) <∞.                         (C)

Schwartz decay implies the last series is finite for every fixed k,β; no uniformity in arbitrarily growing k is asserted. A logarithmic angular factor can similarly be paid by log(2+Λ)+j when the angular range is controlled by the SOURCE cap p. With a global absolute displacement bound

    D(t)=sup_{s≤t,z in supp f0}|V(s;z)−v0|,

one instead has q(V)≤q0+D and the sharper corresponding bound

    Σ_j a_j^β Σ_{p≤C(2^j+D)} p^k
       ≤ C_k[(1+D)^k Σ_j a_j^β+Σ_j a_j^β2^(kj)].              (D)

Both are direct geometric-series estimates. They avoid the Λ^(3/2) moving-tail argument in the earlier screen. The initial-shell mass m_j can also replace the total label-mass bound in some places, but no mass refinement is needed to prove (A)–(D).

The remaining debt is not summability of these polynomial weights. It is the coupled local-in-time bootstrap, all receiver scales, and signed narrow-angle selection:

1. In `occupation.tex` 202–252 the stable length is λ=[C1 P/min(p,w)(M/ω+sqrt(A log(2+P)/ω))]^−2. Stability for BOTH the source and receiver comes from the assumed signed increment bound with this SAME P; its stopping argument gives |ΔV|≤ε min(p,w)ω. Replacing global current P by Λ, 1+D, or a shell cap is a new assertion. Polynomial summation (C) does not establish it. Absolute displacement D alone gives |ΔV(s,t)|≤2D, with no small factor as t−s→0, so it cannot supply this cell length.
2. High initial q0≫D does give q≥q0−D and hence |u(s)−u(t)|≤C|V(s)−V(t)|/q0≤CD/q0. This can make selected high-source bins stable on longer intervals. It does not uniformly handle the near-parallel angular scale ω≈1/min(p,w) when BOTH source and receiver have high momentum, nor does it control the absolute force along all those receivers. A joint classification by receiver q0, source q0 and angle is still needed.
3. The source `direct.tex` explicitly uses w≤P at lines 308 and 377, uses O(log P) receiver-angle bins at 369, and bounds PL by P²log P/w at 399. When only the source-density weights decay, a receiver of arbitrarily large initial momentum does not carry a corresponding small prefactor in its characteristic equation. One cannot replace these receiver-angle counts by log(2+Λ) without another argument. The full-force estimate itself has an extra sqrt(w).
4. `selection.tex` imposes p≤P and parameterizes p=P^(1−α), w=P^z with the resulting nonnegative exponent constraints. Its selected-bin gain and the cancellation of sqrt(w) depend on those constraints. Equations (A)–(D) do not prove that the exponent alternatives survive p or w above an effective Λ/D scale or that the weighted signed selection closes after summing the initial shells.

A promising formulation would establish a uniform local increment envelope based on B=1+D or normalized growth, with explicit separate source/receiver scales, and then close it using the weighted source density while retaining the total cone flux. Applying the compact theorem independently to the shell currents would not prove this envelope, because the acceleration in every shell is generated by the total field. No such envelope or final nonlinear closure has been established here. Thus the density-only alternative remains open and is a more credible remaining route than the failed split-field energy estimate. It is not refuted by that estimate's convergent doubling series.

## Final check: polynomial label growth instead of a uniform ratio

The parent's final suggested relaxation is genuinely sufficient at the moment level. If for each finite T one could prove finite constants C_T,k_T, independent of initial cutoffs, with

    q(V(t;z))≤C_T q0(z)^(k_T),     0≤t≤T,                    (E)

then volume preservation would give sup_{t≤T}M_θ(t)≤C_T^θ M_{k_T θ}(0)<∞ for every fixed θ. Thus an evolved moment greater than 3 would be available for the primary continuation interface (subject still to the full field-class localization discussed above). Polynomial label growth is enough; a uniform q/q0 ratio is stronger than necessary. With smooth bounded field derivatives on finite slabs, the usual differentiated characteristic transport would then give Schwartz persistence, but that derivative continuation also must be supplied rather than assumed.

The weighted source sums become

    Σ_j a_j^β Σ_{p≤C_T2^(k_T j)}p^γ
        ≤C C_T^γ Σ_j a_j^β2^(γ k_T j),     γ,β>0.              (F)

This is finite for every FIXED k_T. It does not by itself bound k_T along a maximal solution.

There is a concrete receiver-adapted strategy worth distinguishing from the already failed uniform-cap substitution: if a version of the signed estimate could be proved with P comparable to the current RECEIVER scale w, treating all higher-source scales using their initial-shell weights and total cone budgets, then the 1/log w doubling-time estimate would allow log q(t) to grow exponentially in time from log q0. That would yield the polynomial form (E). This strategy explicitly includes high-q0 receiver labels, irrespective of their tiny mass.

The actual selected-bin statement currently read does NOT permit that substitution. Its p≤P hypothesis excludes precisely those higher-source scales, and its source stability assumes the same increment envelope for those sources. Establishing their weighted contribution with constants compatible with an evolving growth exponent is the missing joint bootstrap, not an application of `sel:exponents`.

There is also a quantitative caution within this proposed route. The weighted sums in (F) can grow very quickly with k. For the lognormal Schwartz example a_j is exp(−c j²+O(j)); completing the square in

    Σ_j exp(−β c j²+γ k(log 2)j+O(j))

gives growth exp(C k²+O(k)) for fixed positive β,γ. Thus a putative closure using these unrefined constants may lead only to a differential majorant of the scale k'≲k exp(Ck²), whose reciprocal has finite integral at infinity. Such a majorant supplies no global-in-time upper bound on k. This is not a lower bound on actual growth or a proof that better bookkeeping cannot work. It explains why initial finiteness of every moment cannot be substituted for uniform evolved bounds even after switching from Λ to a polynomial exponent.

Outcome of this additional check: polynomial label growth would suffice and suggests a more suitable receiver-adapted target estimate, but no proof that the source common-P selection admits it has been obtained. The full Schwartz-data theorem remains open in this packet. Neither the earlier convergent series nor the moment-constant caution eliminates the density-only route.
