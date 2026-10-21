# PREFREEZE calculation: exact grid quotient and fixed codimension

Status: a source/classical integrated reduction, not a theorem nominee, frozen claim, or contribution grade. The two pinned manuscripts and the operative completed W5 original were read before this extended calculation. Only the one-sided member of Source359 is used here. Write d=n-1 for projective dimension, reserving D for the source assembly's well-depth constant.

## Source interface

In one-sided §3, Lemma grid:polynomials supplies n-1 forms H_1,...,H_d of degree N in n variables, with N^d transverse projective common zeros. The form p of degree N is nonzero on every common projective zero: this follows from the global lower bound on Q=(H,p). Choose a lift v at every zero with p(v)=1. The good subset G loses o(N^d) rows and equidistributes. Its lifts have |v|=N^{O(1/N)} uniformly. All of these are supplied operations, not new claims.

For fixed h>=0 and k>=1, the phase lemma uses the span V of evaluations of degrees h,h+N,...,h+(k-1)N. The source bounds its dimension by the sum of the dimensions of the polynomial spaces, imposing a very small limiting rank fraction. The algebraic relations permit the following exact stronger reduction.

## Exact finite-degree count

Set r=h+(k-1)N. Multiplication by p^(k-1-j) turns a homogeneous form of degree h+jN into one of degree r with exactly the same values on the chosen lifts. Thus V is precisely the degree-r evaluation image; summing independent polynomial-space dimensions overcounts it.

Let S=C[s_1,...,s_n] and A=S/(H_1,...,H_d). The homogeneous ideal has height d. Polynomial local rings are Cohen–Macaulay, so the H_i form a regular sequence. Its quotient has dimension one and is Cohen–Macaulay. It has no embedded prime at the irrelevant maximal ideal. Away from the origin, transverse projective intersection makes the cone reduced; hence A is reduced and the homogeneous ideal is saturated. Consequently the kernel of evaluation on one nonzero lift of every projective point is exactly the corresponding degree of this ideal. The full evaluation image has dimension dim A_r.

For completeness the last reducedness step can be seen without a saturation assertion as a black box: a Cohen–Macaulay complete intersection is unmixed. Its minimal primes here are the lines over the transverse points, where the ring is generically reduced. A nilpotent would have a nonzero annihilator-associated submodule supported on an embedded prime, contradicting unmixedness. A homogeneous form vanishing on the chosen lift then vanishes on its entire line by homogeneity.

The regular-sequence exact sequences give

    Hilb_A(t) = (1-t^N)^d/(1-t)^(d+1)
              = (1+t+...+t^(N-1))^d/(1-t).

Thus the full rank is the following integer, including at small N:

    H_{d,N}(r) = #{(a_1,...,a_d) in {0,...,N-1}^d : sum a_i <= r}
               = sum_{j=0}^d (-1)^j binom(d,j) binom(r-jN+d,d),

where the final binomial is zero when r-jN<0. The first formula follows directly by coefficients; the second is inclusion–exclusion. Deleting B_N=o(N^d) bad rows changes the rank by between zero and B_N. Therefore

    rank(V|G)/N^d -> F_d(k-1),
    F_d(x) = (1/d!) sum_{j=0}^d (-1)^j binom(d,j)(x-j)_+^d.

This is just the volume of {u in [0,1]^d : sum u_i <= x}. It is strictly below one for k<=d, with F_d(d-1)=1-1/d!, and equals one for k>=d+1. More strongly, if k>=d+1 then r>=d(N-1), so the full evaluation map is surjective at every N and remains surjective on G. The phase projection is then exactly the identity, not merely asymptotically close to it. No choice of independent phases repairs that projection method at such k.

## The source phase proof works for any fixed positive codimension fraction

Suppose rank(V)/M <= rho+o(1) with rho<1, where M=N^d and |G|/M->1. Fix beta>0 smaller than 1-rho. Eventually Q=I-Pi on C^G satisfies

    0 <= Q_ii <= 1,   sum_i Q_ii >= beta M.

For fixed coefficient degree h, repeat the source compactness/zero-set argument with a smaller exceptional fraction: choose t_h>0 so every norm-one polynomial P has |P(v_i)|>=t_h outside at most beta M/2 good indices. Then, for independent uniform phases b_i,

    E[M^-1 ||Q (b_i P(v_i))||^2]
       = M^-1 sum_i Q_ii |P(v_i)|^2 >= beta t_h^2/2.

Choose a fixed orthonormal basis of the degree-h coefficient space. Its evaluations on the lifts are bounded uniformly in N. Exactly the source independent-phase calculation bounds the variance of each Gram entry by C_h M^-2 sum_{i!=j}|Pi_ij|^2 <= C_h/M. The coefficient-space dimension is fixed. Hence there is one choice of phases for which the entire Gram matrix is >= beta t_h^2/4 times the identity. A permissible separation constant is delta_h=sqrt(beta)t_h/2. Nothing requires a universal lower bound as h grows; h is fixed at each test and the source diagonal schedule revisits all tests.

Combining with the exact count, this pays the phase step for every fixed n>=k+1 (and n>=2), instead of the source's sufficient factorial inequality. At n=k+1 the residual fraction is 1/k!; it is small but positive for the fixed k. There is no claimed optimal dimension for a Liouville domain.

## Integrated geometric compatibility and its limit

The remaining §3 criterion and §§4–8 construction must still be paid. With D denoting the assembly well-depth constant, the source uses

    m0=D/2, p0=2D,
    p1=C_s B_* + C_w D gamma B_* <= D/4,
    m0>p1, 0.99 k>p0+p1+1.

D is first chosen sufficiently large relative to the dimension-independent geometric constants; k is then chosen, and n afterward. The root-of-unity tail remains exp(-0.99 k c). Disk radii, slope, and sphere derivative bounds remain exp(m0 c), at least exp(-p1 c), and at most exp(p0 c), respectively. A smaller fixed delta_h increases the finite thresholds at that test. Arbitrarily large c and grid degrees N, and the source's depth/clock schedule, absorb those fixed thresholds. No change to curvature, well preservation, disk localization, completeness, or diagonal revisit operations is needed for this algebraic improvement.

This is a useful exact reduction of the existing proof parameters, but it consists of the classical complete-intersection Hilbert count and the already supplied phase Gram argument with adjusted constants. It does not supply the required distinct nonroutine operation. In particular it supplies neither a specific low-dimensional example nor a two-sided curvature bound.

To cross the exact saturation at k>=n with this geometric exponent budget requires a different analytic test space or a new way to prevent cancellation after the present evaluation image becomes all of C^G. Alternatively a genuinely different geometric realization would have to lower the required truncation length. Merely optimizing the source factorial estimate, changing the numerical phase fraction, or dropping the disk hypotheses does not pay that obligation.

## Primary scope

The algebra used here is classical. The operative regular-sequence/Koszul interfaces were read in Stacks tags 00NQ, 02JN, 00N6, 062F, and 07D2; their own transitive depth/dimension prerequisites were not exhaustively followed. The finite count and the probabilistic Gram calculation are derived explicitly above. No new-to-literature or exhaustive history claim is made.
