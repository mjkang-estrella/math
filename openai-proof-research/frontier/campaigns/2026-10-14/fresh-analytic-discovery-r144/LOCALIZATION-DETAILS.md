# Further feasibility calculations and the remaining compatibility problem

This follows DERIVATION.md chronologically. No statement freeze or full author-proof nomination has occurred. The source and its operative proofs are stipulated true. The question is which operations extend to exterior stability, not whether the source is correct.

## Polynomial buffers, with the dimension-four sum retained

The first note used w(s)=L+log s. This handles the logarithmic radial interpolation but is not by itself a buffer for the source's polynomial rough collars as s→∞ with R fixed. A stronger choice is

    w(s)=L+s^β,     β=1/50,     s≥R,

and the actual smooth cutoff uses w(ρ). Here the source's rough-neighborhood exponent is β0=.01<β and its defect exponent is α=.04. At the main scale w(R)/L→1 because L≥c√R. On dyadic shells s_j=2^jR,

    w(s_j)/L ≤ C 2^(βj),
    K(w(s_j)) ≤ C [w(s_j)/L] K(L) ≤ C [w(s_j)/L] K(R).

For sufficiently large R, w(s)≪s uniformly. All fixed multiples can be absorbed in constants fixed before R grows. Conditional on the fourth-moment collar bound (3) of DERIVATION, the normalized radial curvature/cutoff sum is bounded by

    C (L/R)^(n−3) Σ_{j≥0} 2^[(3−n)+β(n−1−θ)]j.           (9)

For n=4 the exponent is −1+.02(3−.02)=−.9404. It is still more negative for n=5,6,7. Thus (9) is O(K(R)^(-(n−3)/2)). The main discarded energy fraction remains O(K(R)^(-(n−1)/2)). This fixes the buffer issue without changing the old dimensions or requiring any divergence rate for K.

For rough collar bookkeeping the extra fourth-moment term is multiplied by s^γ, γ=2α+7β0=.15, to count its expanded neighborhoods. The radial weight for these errors is s^−4 w^(1−θ), giving

    C K(w)s^(k−4+γ)w^(n−4−θ).

After normalization this is bounded by

    C R^(3−n+γ)L^(n−5)
      Σ 2^[(3−n+γ)+β(n−3−θ)]j
    = C (L/R)^(n−3) R^γ/L² × (a convergent series).

Since L²=R²/K(R) and K(R)≤1+CR, the prefactor tends to zero (γ<1). Therefore the extra cylinder term is also harmless for the rough-collar scalar bookkeeping, if the localized fourth-moment and net estimates hold. This does not construct that estimate.

## Fourth powers give additive transfer at zero weights

For every ε>0 there is C_ε<∞ such that

    (a+b)^4 ≤ (1+ε)a^4+C_ε b^4       (a,b≥0).               (10)

For example use convexity of t↦t^4 with weights 1/(1+t),t/(1+t), taking t>0 with (1+t)^3=1+ε. No smoothness or PDE enters.

Let 0≤ζ≤1 be ℓ^−1-Lipschitz, and let z,y lie in a region where the cutoff length is comparable to ℓ. Then

    ζ(z)^4 ≤ (1+ε)ζ(y)^4+C_ε |z−y|^4/ℓ^4.                (11)

The inequality remains valid when ζ(y)=0. This is the correct replacement for dividing by a receiving cutoff value. It pays a fourth-order additive error; a direct estimate of ζ² alone would generally pay only second order.

For an exponentially decaying kernel K_c(z,y)=exp(−c|z−y|), and a surface/ambient measure whose unit-ball masses are uniformly bounded and whose annular masses grow polynomially, (11) gives a weighted convolution estimate. If χ_s(z)/χ_s(y)≤exp(|z−y|/s) and s≥4/c, then

    ∫ K_c(z,y)χ_s(z)²ζ(z)^4 dμ(z)
      ≤ C χ_s(y)² ζ(y)^4 + C_ε ℓ^−4 χ_s(y)².              (12)

Indeed sum unit annuli, using exp(−c r+2r/s)≤exp(−cr/2) and the finite fourth moment of that exponential. The constants depend on c and the polynomial mass bound, not on s or ℓ. In applying this to a collar one still has to localize the additive term: (12) alone charges all y. If ζ is constant away from a collar, changes between z and y require a segment to encounter that collar. Terms with |z−y|≥cℓ can be retained as an exponentially small leakage tail; short pairs are charged to a fixed enlargement of the collar. That geometric split is part of a complete weighted comparison, not an implicit global volume bound.

The source L11 has precisely such a positive-kernel structure. The fourth-power calculation removes the algebraic zero-denominator obstruction noted in DERIVATION. It does not independently re-prove L11 for the variable cutoff, cap correction, bad-net weights and all collars simultaneously.

For a genuine positive contact branch, source/foot distance ≤d, d_hat(y)≤d_hat(z), and source multiplicity is at most one. In the growth proof the multiplier P_*(d) is eventually exponentially decaying. Thus sup_{d≥t_min} d^4 P_*(d)<∞. If the receiving curvature is bounded and the area distortion is bounded on the applicable branch, (11) bounds the cutoff-mismatch part of its transferred charge by C ℓ^−4 times receiving area. This proves the algebraic payment once those geometric hypotheses hold. For long contacts crossing multiple collars, retain the exponential tail rather than asserting comparable cutoff scales. Artificial cap branches have no receiving foot and must be treated through their separate Laplacian contribution.

## Why a squared cutoff is natural in the physical amplitude

Take a physical test with cutoff factor ζ²; its square carries ζ⁴. At a purely scalar level,

    |∇(ζ²)|² ≤4 ζ²/ℓ²,
    ζ² E/ℓ² ≤ ε ζ⁴ E²+C_ε ℓ^−4.                         (13)

The latter is ordinary Young applied to ζ²E and ℓ^−2. It is exactly the power needed in the final growth closure, where f(d)²≤C_f E. Likewise, in a curvature test, ζ²a²/ℓ² is absorbed into εζ⁴a⁴+C_εℓ^−4. Terms of the type ζ³/ℓ admit εζ⁴+C_εℓ^−4 by (10)/Young. These comparisons explain why a fourth-order remainder is plausible even when differentiation initially gives inverse-square terms. They do not control the geometry of every lifted branch.

The exact quadratic-form identity makes physical admissibility concrete. For any smooth multiplier a and compactly supported F,

    Q(aF)=∫a²(|∇F|²+VF²)+∫|∇a|²F²
           +2∫aF∇a·∇F,       V=3v²−1.                  (14)

Equivalently Q(aF)=∫a² F(−Δ+V)F+∫|∇a|²F² when the integration is legitimate. One must apply stability to the actual aF supported outside C_a, rather than replace Q(F) by a weighted integral after the fact. In the source square-root construction, multiplication of every branch by the same physical ζ² commutes with the square root and scales the variance by ζ⁴. This exact observation preserves its nonnegative variance. It still leaves normal averaging and the movement of base weights; different base cutoffs do not have this property.

On a fixed normal segment of length P, (10) in both directions compares ζ(Φ(z,t))⁴ with ζ(z)⁴, up to a small relative loss and C_ε P⁴/ℓ⁴. Exponential profile tails have finite fourth moments and hence suggest the same payment on long segments. In the real proof the normal map need not be injective and the admissible cap depends on curvature. Finiteness of all inverse branches, their area factors, and the mixed cutoff costs must be verified before this suggestion is used as an integral estimate.

## Local regularity: an available operation, not a new conjecture

The actual Florit-Simon v1 theorem sheetstabconj (Theorem2.12, main.tex711–720) is explicitly for a stable solution on B_R with bounded normalized energy and small ε/R, conditional on stable entire classification. Source375 supplies that classification. Its cited proof is FSS's local regularity argument; FSS AllenCahn.tex1136–1193 contains the blowup/curvature proof, and2617–2623 explains the local-ball version. Those bodies were read here. Thus the mere transition from an entire-stable corollary to a stable-ball estimate is already paid by the compatible primary theorem. It is not a remaining positive conjecture.

Capping the available reach by distance to C_a keeps the density window in such a ball. The delayed monotonicity argument depends on slab confinement and the equation; it does not require global stability. The remaining work is to verify every use of differentiated reach, local mean-curvature estimates and the global weight/gluing machinery with this cap. The full transitive WW transition-layer proof was not freshly read, so this packet cannot claim a complete author-proof dependency audit.

## Remaining research obligation, after these compatible operations

The task is not blocked by the old dimension-four fixed-core arithmetic or by the existence of a local stable-ball theorem. It is the simultaneous localization of the actual growth and radial constructions that has not been finished:

1. Establish an exterior weighted fourth-moment/net estimate with fourth-order collar loss, using the physical ζ² multiplier, bounded positive-foot multiplicity, kernel leakage control, and capped-reach errors, with one consistent choice of cutoffs and thresholds.
2. Establish the corresponding clean logarithmic graph regions and radial switching inequality with the same exclusion; prove its additional errors satisfy (9) and the rough-collar estimate, uniformly before the outer limit.
3. Complete the final area transfer after deleting the growing cylinder and rough collar, keeping the same numerical margin. Formula (2) pays only the cylinder energy deletion, not this whole geometric transfer.

The original positive route is feasible-looking, but the simultaneous estimates are not present as a proved lemma in this packet. A list of compatible scalar inequalities does not constitute that lemma. No full-scope theorem, partial-dimension theorem, conditional theorem, or ancillary result is nominated. No claim is made that the remaining operation is impossible, novel to the literature, or necessarily substantial. If it can be obtained by a routine localization of the credited proof, completing the old conjecture would still require a separate contribution assessment.
