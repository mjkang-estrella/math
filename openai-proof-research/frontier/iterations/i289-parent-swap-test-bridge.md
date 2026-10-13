# Parent supplement to I289: a product-test bound for measurement recursions

2026-10-13. **A proved auxiliary estimate shared with the live I289 author; not an independent review or acceptance.** The author had already reported a candidate product-test route. This note records the parent's separate derivation and its proposed scope extension. The final I289 theorem, constants, literature comparison and latitude conversion remain the author's responsibility.

## Exact ensemble inequality

For a pure state psi on n finite-dimensional sites, let

    A_n(psi) = <psi tensor psi, (product_j Sym_j)(psi tensor psi)>,
    F_n(psi) = 1 - A_n(psi),
    Sym_j = (I + Swap_j)/2.

Put H=product_{j>=2} Sym_j and rho=Tr_1 P_psi. Since H Swap_tail=H and the full swap fixes psi tensor psi,

    A_n(psi) = Tr[H(rho tensor rho)].

Indeed the two terms from Sym_1 have equal expectations: replace Swap_1 by Swap_all Swap_tail, move Swap_all onto the identical pure copies, and use H Swap_tail=H. No product assumption on psi is used.

Let rho=sum_i p_i sigma_i be any finite pure-state ensemble, sigma_i=P_chi_i. Then the exact quadratic identity is

    sum_i p_i A_{n-1}(chi_i) - A_n(psi)
      = (1/2) sum_{i,j} p_i p_j Tr[H((sigma_i-sigma_j) tensor (sigma_i-sigma_j))].

Since ||H||<=1 and ||sigma_i-sigma_j||_1^2=4(1-Tr(sigma_i sigma_j)), its right side is at most

    2(1-Tr rho^2) = 2(1-Tr rho_1^2).

Thus every such ensemble obeys

    F_n(psi) <= sum_i p_i F_{n-1}(chi_i) + 2(1-Tr rho_1^2).       (E)

For a qubit first site the last term is 4 det rho_1. This does not assert positivity of the quadratic identity's right side; only its upper bound is needed. Zero-probability branches can be omitted.

## Entanglement-breaking channel recursion

Let Phi be a finite-dimensional entanglement-breaking channel and mu its minimum output entropy, in nats. Assume the quantitative one-site inequality

    S(Phi(rho))-mu >= c(1-Tr rho^2),  c>0,                       (L)

for every input density matrix. Refine a finite measure-and-prepare representation to rank-one POVM effects. Applied to the first site of a pure state, it produces a pure-state ensemble on the remaining sites. Shor's strong-subadditivity argument gives

    S(Phi^{tensor n}(P_psi))
      >= S(Phi(rho_1)) + sum_i p_i S(Phi^{tensor(n-1)}(P_chi_i)).

For D_n=S(Phi^{tensor n}(P_psi))-n mu, this yields

    D_n >= c(1-Tr rho_1^2) + sum_i p_i D_{n-1}(chi_i).

Iterate this and (E) along the same measurement tree. F_1=0 for every pure one-site state, and the terminal entropy deficits are nonnegative. Consequently

    F_n(psi) <= (2/c) D_n(psi).                                  (T)

This estimate is independent of n. It is a product-test bound, not by itself a distance estimate to the channel's particular minimizing product family. A product-test soundness theorem and an additional minimizer-selection argument are needed for that conclusion.

## GAD one-site calculation

Use the project's convention: t=1-gamma, d=1-2nu, input Bloch vector r with third coordinate z, and output Bloch vector (sqrt(t) r_x, sqrt(t) r_y, t z+gamma d). Its maximal output length R_* obeys R_*^2=t+gamma d^2, attained on pure inputs with z=d. Direct expansion gives

    R_*^2 - |r_out|^2 = t(1-|r|^2) + t gamma (z-d)^2.

Writing G(u)=h((1+sqrt(u))/2), one has -G'(u)=atanh(sqrt(u))/(2 sqrt(u))>=1/2, with the continuous value at zero. Therefore

    S(Phi(rho))-mu >= 2t det rho + (t gamma/2)(z-d)^2
                       >= t(1-Tr rho^2).

Whenever this GAD channel is entanglement breaking, (T) consequently gives

    F_n(psi) <= 2 D_n(psi)/(1-gamma).

For interior parameters its Choi partial-transpose middle block is positive exactly when t<=gamma^2 nu(1-nu). This identifies a proposed scope extension to the entire interior entanglement-breaking region. In the unital case a fully explicit measure-and-prepare decomposition is

    A_s = s Dephase_X + s Dephase_Y + s^2 Dephase_Z
                  + (1-2s-s^2) Depolarize_0,

valid for 0<s<=sqrt(2)-1. Thus the swap-test argument need not be restricted to the initial s<=1/3 decomposition through a transpose channel.

## Source and review boundary

The entropy recursion is the classical argument in [Shor, arXiv:quant-ph/0201149v3](https://arxiv.org/html/quant-ph/0201149), Theorem 1, especially equations (5) and (7)--(14). The parent read the representation and full Theorem 1 proof in the served HTML, lines 39--81. That additivity theorem is credited, not a new claim.

The GAD parameter comparison was checked against [Khatri--Sharma--Wilde, arXiv:1903.07747v2](https://arxiv.org/html/1903.07747v2), Section IV, equations (104)--(107), served HTML lines 506--533. The Choi PPT block gives the equivalent condition above; the source's convention may interchange nu and 1-nu, which leaves the condition unchanged.

No full external text is retained in this note. No new independent proof/contribution gate is claimed. In particular, (T) alone is not labeled the full I289 distance theorem, nor a solution outside the entanglement-breaking region.
