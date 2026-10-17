# Frozen target RF: zero-field radial spin fluctuations

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

For every fixed S in {1/2,1,3/2,...}, consider on the periodic cubic
lattice Lambda_L=(Z/LZ)^3, with even L>=4, the quantum Hamiltonian

    H_L = sum_{unordered nearest-neighbor bonds xy}
                (S^2 - S_x dot S_y).

Let V=L^3, and let J_L be the nonnegative total-spin label, so that
J_L(J_L+1)=sum_{a=1}^3(sum_x S_x^a)^2. Its probability distribution is
the spectral distribution in the normalized zero-field Gibbs state
exp(-beta H_L). Put D_L=SV-J_L.

For each representative k of (Z/LZ)^3 in [-L/2,L/2)^3 define

    epsilon_L(k) = 2S sum_{a=1}^3 (1-cos(2 pi k_a/L)),
    mu_(beta,L) = sum_{k != 0} (exp(beta epsilon_L(k))-1)^(-1),
    a_(beta,L) = beta/L^2,
    Y_(beta,L) = a_(beta,L) (D_L - mu_(beta,L)).

For EVERY sequence beta -> infinity and even L satisfying

    beta^(501/1000) <= L <= beta^(51/100),

the variables Y_(beta,L) converge in distribution to

    W_S = sum_{k in Z^3\{0}} (E_k-1)/(4 pi^2 S |k|^2),

where the E_k are mutually independent mean-one exponential variables.
The series is understood as its L^2 limit over increasing centered
integer boxes. In addition, for every real lambda>=0,

    E exp(-lambda Y_(beta,L))
        -> product_{k in Z^3\{0}}
            exp(lambda/(4 pi^2 S |k|^2)) /
            (1+lambda/(4 pi^2 S |k|^2)).

The limit has positive variance and is not Gaussian. These are one
target, not separate nominations. The centering is the stated finite
ideal-mode sum; no assertion that it equals the interacting expectation,
no convergence of all moments, no fixed-temperature law, no beta~L^2
occupation theorem, no optimized window, and no nonperiodic-boundary
extension is part of RF.

No prior target in this round was frozen. This full claim is the first
freeze. It must be proved or left unresolved without substituting a
single-spin, selected-sequence, positive-field, ideal-gas or conditional
version. Proof and contribution reviews remain independent and pending.
