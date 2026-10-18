# Regularized normalization of the bounded response

Author support for the unchanged all-deficit target; not a global rounding theorem or an independent review. This note uses the preceding bounded-response-construction.md. No scalar-alpha calibration is assumed.

Write |A|²=sum_r ||A_r||F² and c(A)=sum_rs ||[A_r,A_s]||F². Tensor indices all range over the same Euclidean space. Suppose C_r are symmetric, B_C=sum C_r²<=I, its full symmetrization S obeys |S-C|²=e, and at most r eigenvalues of B_C are below gamma>0. Here e,c(C),r=O(delta) and gamma is a fixed positive absolute constant. All constants below depend only on gamma.

## Symmetrization without losing a bounded Gram

Let B_S be the Gram of any one-mode flattening of the fully symmetric S. Set P=min(I,2 B_S^(-1/2)), with value1 at zero, and A=P tensor P tensor P applied to S. Then A is fully symmetric. Each P is a contraction. Telescoping the three mode actions gives

 |S-A|² <=9 sum_i (sqrt(lambda_i(B_S))-2)_+² <=9e.

The final inequality is the singular-value perturbation inequality comparing the flattening of S with the corresponding flattening of C, whose operator norm is at most1. Consequently |A-C|²<=16e. Moreover the flattening of A is P flat(S)(P tensor P), so B_A<=4I.

For later estimates the elementary family product inequality is useful. If sum U_r*U_r and sum U_r U_r* are both <=K_U I, and the analogous bounds hold for V, then

 sum_rs ||U_r V_s||F² <= K_U |V|²,
 sum_rs ||V_s U_r||F² <= K_U |V|².

Apply this to the expansion of commutator differences. If both A and C have two-sided Gram bounds K_A,K_C, then

 sqrt(c(A)) <= sqrt(c(C))+2(sqrt(K_A)+sqrt(K_C)) |A-C|.

Thus c(A)<=2c(C)+72|A-C|². Singular-value perturbation also gives

 #{lambda(B_A)<gamma/4} <= r+4|A-C|²/gamma.             (1)

Indeed every additional singular value drops from at least sqrt(gamma) to less than sqrt(gamma)/2. These estimates do not require e to be absolutely small.

## Normalize above a fixed floor

Put b=gamma/4, g(t)=max(t,b)^(-1/6), P=g(B_A), and p=b^(-1/6). The original gamma can be decreased to at most1. Then ||P||op<=p; g is Lipschitz on[0,4], with constant at most b^(-7/6)/6. Define the fully symmetric tensor U=P tensor P tensor P applied to A.

Let V_r=P³ A_r, which need not be symmetric. Full symmetry of A identifies differences of two mode actions with commutators:

 |(P in mode1-P in mode2) A|²=sum_r ||[P,A_r]||F²,

and similarly for any two modes. Moving the two other P factors to the output mode, using their commuting mode actions, gives

 |U-V| <=2p² (sum_r ||[P,A_r]||F²)^(1/2).             (2)

All these are tensor Frobenius identities; no eigenbasis derivative is involved.

Let K=||B_A||op<=4. Since

 [B_A,A_r]=sum_s (A_s[A_s,A_r]+[A_s,A_r]A_s),

row and column Cauchy-Schwarz give

 sum_r ||[B_A,A_r]||F² <=4K c(A).

In a B_A eigenbasis, scalar divided differences therefore yield

 sum_r ||[P,A_r]||F² <=4K Lip(g)² c(A).               (3)

Both flattenings U and V have operator norm at most sqrt(K)p³. The row Gram of V is P³ B_A P³=P^6 B_A. Consequently (2)-(3), and

 ||UU* - VV*||F <= (||U||op+||V||op)|U-V|,

show that ||B_U-P^6 B_A||F²<=C_b c(A). The eigenvalues of P^6 B_A are lambda/max(lambda,b), equal to1 for lambda>=b and between0 and1 otherwise. From(1),

 ||B_U-I||F² <= C_b c(A)+2r+8|A-C|²/gamma.           (4)

Also B_U<=Kp^6 I. Thus the normalization does not generate a dimension-dependent Gram bound.

For completeness commutators remain paid. With R=P³,

 [V_r,V_s]=R²[A_r,A_s]+R[A_r,R]A_s-R[A_s,R]A_r.

The product inequality bounds the sum of squares of the last two terms by a constant times sum_r ||[A_r,R]||F². The identity [A_r,P³]=[A_r,P]P²+P[A_r,P]P+P²[A_r,P] and(3) control this by C_b c(A). Hence c(V)<=C_b c(A). The V family has both row and column Grams at most Kp^6 I: for the column Gram use sum A_r P^6 A_r<=p^6 B_A. U is symmetric and has the same bound. The commutator-difference estimate applied to U,V and(2) now proves

 c(U)<=C_b c(A).                                    (5)

Combining all estimates yields a fully symmetric cubic U with

 B_U<=C_gamma I,
 ||B_U-I||F²+c(U)<=C_gamma (e+c(C)+r).

For the bounded response of the retained source remainder this right side is O(delta), for every deficit. Every transformation is finite dimensional, so these normalization steps add no integrability hypotheses.

## Exact remaining obligations

A dimension-independent global rounding theorem for fully symmetric cubics with bounded B and residual ||B-I||F²+c is still required. The absolute-small-residual theorem alone does not supply it when delta is intermediate or large. Arithmetic r69 is investigating this separate statement; no conclusion is imported here.

Even such rounding must be transferred back through the response to actual independent exponential factors. The present estimates only normalize a constant coefficient tensor. They do not invert the bounded response f, control q on unbounded spectral tails, or establish a transport recovery theorem. Parent's bounded-B inverse-commutator lemma is a possible additional interface, not used in this note. There is no new nomination or scope change.
