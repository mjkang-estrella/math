# I318 — sharp model dimension for exact inner averaging

2026-10-13. Parent derivation, **unreviewed supporting extension** of Q315. This is not an additional acceptance or a claimed literature-first theorem. Fourteen findings remain accepted toward twenty. The complete hierarchy direction can contribute at most one new finding.

## Statement

Let r>=1 and let Phi be an r-by-r analytic inner matrix function on the disk, with Phi(0)=0. Boundary values are unitary almost everywhere. Suppose its exact averaging channel is depolarizing:

    integral Phi(zeta) B Phi(zeta)* dm(zeta) = tr(B) I_r/r

for every complex r-by-r matrix B, with normalized circle measure m. If K_Phi=H²(C^r) minus Phi H²(C^r) is finite-dimensional, then

    dim K_Phi >= r(r²+1)/2,
    dim K_(z Phi) >= (r³+3r)/2.

Equality is attained by the Q315 polynomial

    Phi(z)=z diag(z^(ri)) U_r diag(z^j),  0<=i,j<r,

where U_r is the normalized Fourier matrix. More generally, even without finite-dimensionality, the same inequality holds for the dimension interpreted in the extended nonnegative integers. Equality in the first inequality forces Phi to be a polynomial of degree r² with all first r² coefficient matrices mutually orthogonal in Hilbert–Schmidt inner product, each of squared Hilbert–Schmidt norm 1/r. In particular, the Q315 model dimension is optimal within this exact-averaging, zero-constant inner-model class. No optimality is asserted among all numerical contractions or all constructions of the amplification hierarchy.

## Proof: a coefficient frame with a sharp occupancy cap

Write Phi(z)=sum_(k>=1) F_k z^k and a_k=||F_k||_HS². Expanding the channel on each matrix unit and using Parseval gives

    sum_k vec(F_k) vec(F_k)* = I_(r²)/r.              (1)

This is simply the matrix of coefficient correlations: its entry indexed by (i,a),(j,b) is sum_k (F_k)_(i,a) conjugate((F_k)_(j,b)), which the channel identity sets equal to delta_ij delta_ab/r. One can use finite partial sums and monotone limits; no unjustified exchange of conditionally convergent series is needed. The vectorization convention does not affect the identity matrix on the right.

Every positive rank-one summand of (1) is bounded above by I/r. Consequently

    0<=a_k<=1/r,                 sum_(k>=1) a_k=r.   (2)

This is stronger than merely requiring at least r² nonzero coefficients: it bounds the weight that can occupy each delay.

## Proof: exact state-dimension identity

The Hardy multiplication operator M_Phi is an isometry. Therefore P=I-M_Phi M_Phi* is the orthogonal projection onto K_Phi. For the standard orthonormal vector monomials z^n e_j, its diagonal sum at fixed n is

    sum_j <P z^n e_j,z^n e_j>
      = r-sum_(k=1)^n ||F_k||_HS²
      = sum_(k>n) a_k.

Here Parseval and innerness give sum_k a_k=r, and the displayed partial sum follows directly by projecting Phi* z^n e_j to the nonnegative Hardy coefficients. All quantities are nonnegative. Summing over n>=0 and applying monotone convergence gives, with infinity allowed,

    dim K_Phi = tr P = sum_(k>=1) k a_k.           (3)

For z Phi the additional zero shift increases this by sum_k a_k=r. Equivalently K_(z Phi)=C^r orthogonal-sum z K_Phi.

## Proof: optimal filling of the delay slots

Put N=r² and b_k=1/r for 1<=k<=N, b_k=0 otherwise. Both a and b have mass r. Since a_k<=b_k within the first N slots, the following identity in nonnegative terms holds (also when the left side is infinite):

    sum_k k a_k - (1/r) sum_(k=1)^N k
      = sum_(k<=N) (N-k)(1/r-a_k)
        + sum_(k>N) (k-N)a_k >= 0.              (4)

Thus (3) is at least N(N+1)/(2r)=r(r²+1)/2. For equality, all a_k=1/r for k<N and all a_k=0 for k>N. Total mass also forces a_N=1/r. There are then exactly r² vectors vec(F_k), and (1) says their square coefficient matrix divided by its scale is unitary. They are mutually orthogonal with squared norm 1/r, as asserted. This conclusion concerns coefficients, not an unsupported classification of all equality functions.

For the explicit Q315 polynomial, its (i,j) entry is (U_r)_(i,j) z^(1+ri+j). The exponents are exactly 1,...,r², each assigned to one matrix unit, with coefficient magnitude 1/sqrt(r). Thus (1) holds, all first N slots saturate (2), and equality holds in (3)-(4). Products of the scalar delay matrices with U_r are unitary on the circle, so the candidate is inner. This proves both attainability and the exact lower bound.

## Scope and prior-work obligations

The parent has not independently reviewed this proof or established a contribution verdict. Q315's live I316 and I317 reviews do not cover this new lower bound and must not be represented as doing so. A later review must receive the full original Q315 proof, the completed qualitative I314 objections, and this added claim.

The channel-to-coefficient-frame identity and its rank/weight bounds are standard Choi/Parseval calculations; the trace identity is standard Hardy-model dimension bookkeeping; the filling argument is elementary. Classical private-channel and unitary-design lower bounds must be credited. The proposed extra content is the sharp delay-weighted model-dimension lower bound and matching analytic inner polynomial, not the old r² Kraus-count lower bound. Whether that combination merits contribution credit is unresolved. There is no new dependence on the stipulated OpenAI complete upper bound. This limitation remains explicit.

The parent read Boykin–Roychowdhury, *Optimal Encryption of Quantum Bits*, [arXiv:quant-ph/0003059v2](https://arxiv.org/html/quant-ph/0003059v2), Section 5 Lemma 5.1 and all of Section 6, Lemmas 6.1–6.2 and Theorem 6.3 with proofs (web extraction lines 80–189), on 2026-10-13. Its coefficient-frame equation and diagonal-weight cap explicitly pay the old dimension/rank mechanism in (1)–(2); they concern probability-weighted unitaries in dimension 2^n. The present Fourier coefficients need not be scalar multiples of unitaries. The displayed self-contained matrix-unit argument therefore gives the needed extension to general r and arbitrary coefficient operators, while not claiming the underlying frame mechanism is new. The analytic delay-weighted Hardy trace in (3), rather than the old rank count, is what supplies the cubic state cost. That bridge still requires an independent contribution assessment. No full external body or section was retained; the source's raw response was not hashed. Ambainis–Mosca–Tapp–de Wolf, *Private Quantum Channels*, arXiv:quant-ph/0003101, remains a search lead only and its full proof is not claimed read.
