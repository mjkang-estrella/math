# Full discrepancy retention: concrete prefreeze exploration

No theorem was frozen and no author-proof nominee is claimed. This is a feasibility calculation for a distinct operation, not a restricted replacement for any archived target.

## Operation being tested

For d>0 and positive rational epsilon, seek integers n=n(d,epsilon) and c=c(d,epsilon)>0 with the following property. For every epsilon-lc complex normal quasi-projective X of dimension d, K_X Q-Cartier, every projective contraction f:X->Z with -K_X ample over Z, and every closed z, find an open U containing z and B>=0 rational such that n(K_X+B) is integral Cartier and linearly trivial on X_U and

    A_(X,B)(E) >= c A_X(E)

for EVERY primitive prime divisor E over X_U. The index and c must be uniform over the full class; neither a supplied resolution nor a bound for its discrepancies is part of the input. This retains all discrepancy scales, not merely A_(X,B)>=delta. The dimension-zero-base case has stronger bounded-family mechanisms; the unresolved part is the unrestricted relative one. This question is not asserted new to the literature.

## Complete-system formulation, including all higher valuations

Work on an affine neighbourhood of z. For an integer m for which the system is nonzero, represent a section s of f_*O_X(-mK_X) by the effective Q-Cartier divisor

    Delta_s = div(s)-mK_X.

Choose finitely many module generators and principalize their fractional ratios on p:Y->X. Include the exceptional and canonical supports. The complete pulled-back system is F_m+|L_m|, where F_m>=0 is a rational fixed divisor and the residual system is generated. This does not assume mK_X Cartier. The defining minimum is

    ord_E(F_m) = min_s ord_E(Delta_s)

on every higher model, using pullback of F_m after principalization. Localizing the base does not change this minimum at a valuation whose image centre contains z: inverted functions are units there.

On a log-smooth determination, include all primes E_j in the fixed and exceptional supports. Put a_j=A_X(E_j)>0 and f_j=coeff_(E_j)(F_m). Define

    r_m = min(1, min_(f_j>0) [1-f_j/(m a_j)]).

This is equivalently inf_E [A_X(E)-ord_E(F_m)/m]/A_X(E), with all primitive primes tested. To see this, on the reduced snc support S,

    A_X(v)=A_(Y,S)(v)+sum_j a_j v(E_j),

and F_m is monomial. The residual term is nonnegative. Hence an inequality verified on these finitely many generators extends to all higher divisors. This argument also applies when the log pullback boundary has negative coefficients; a_j, not the boundary coefficient, is the positive quantity used.

Take a general residual member H transverse to S and put B=Delta_s/m. Include H in the reduced support. At a new component of H, the discrepancy ratio is 1-1/m. On every higher prime the same snc decomposition therefore gives

    A_(X,B)(E) >= min(r_m,1-1/m) A_X(E).                 (1)

Conversely every degree-m complement satisfies ord_E(Delta_s)>=ord_E(F_m). A complement with retained fraction c forces r_m>=c. Thus, after harmlessly making m>=2, the full operation is exactly a uniform positive bound for r_m at one uniform degree, allowing the neighbourhood to depend on the example. This is a finite resolution test for each example, but not yet a uniform bound over examples.

K pays positivity of r_N for each example after shrinking. Its discrepancy lattice gives A_X(E)-ord_E(F_N)/N>=1/N. That inequality alone does not bound r_N away from zero, because its denominator A_X(E) is unbounded in the class of all primes.

## An actual integrated buffer construction

Assume dim Z>0. Apply C to (X,0). Choose once a positive rational t with 2t<min(tau(d,epsilon),1). After shrinking, take D=div(g)>=0 through z such that (X,2t f*D) is lc. Averaging its discrepancy function with A_X shows that (X,t f*D) is epsilon/2-lc, with the stronger inequality

    A_(X,t f*D)(E) >= A_X(E)/2.

At a prime of X, lc gives 2t mult_P(f*D)<=1. Hence the coefficients of t f*D lie in the FIXED FINITE RATIONAL set

    J={t j : j integer, 0<=j<=floor(1/(2t))}.

X is Fano type, and -(K_X+t f*D) remains ample over Z because the added divisor is pulled back from the base (and is principal on this neighbourhood). K cor:finite-coefficients applies over C to this exact pair. It gives a klt complement Lambda>=t f*D with index N=N(d,epsilon/2,J). All its prime discrepancies are at least delta=1/N. Set

    Omega=Lambda-t f*D >=0,
    M=lcm(N,denominator(t)), increased to be at least 2.

Then M(K_X+Omega) is integral Cartier and linearly trivial: subtracting M t div(f*g) subtracts an INTEGRAL PRINCIPAL divisor. For every primitive E over the chosen neighbourhood,

    A_(X,Omega)(E) >= delta+t ord_E(f*D)
                       >= delta+t ord_E(m_z O_X).       (2)

The latter inequality is the inclusion of the chosen equation in m_z. It also holds outside the fibre, where the point ideal is the unit ideal. This is one actual complement with one uniform index and a vertical discrepancy buffer, not a separate complement selected for each valuation. It closes all coefficient, field, effectivity, positivity and linear-triviality interfaces. It is a routine composition of the paid operations and is NOT nominated.

Since Omega occurs in the complete degree-M system,

    A_X(E)-ord_E(F_M)/M >= delta+t ord_E(m_z O_X).       (3)

By replacing M with a uniform multiple supplied by bounded general epsilon-lc Fano fibres, its general-fibre system can also be made free. Birkar's fixed/moving-part mechanism then makes F_M vertical. This uses only the boundary-zero ample setting of the tested operation. It gives no uniform control of the coefficients of the resulting vertical fixed divisor on exceptional models.

## The precise remaining regime

Suppose this fixed-degree construction fails to give a uniform retained fraction. For a sequence of examples choose a fixed-part witness E_i with

    r_i=(A_i-ord_(E_i)(F_M)/M)/A_i ->0,
    A_i=A_(X_i)(E_i),  q_i=ord_(E_i)(m_(z_i)O_(X_i)).

Equation (3) gives the concrete necessary conditions

    A_i >= delta/r_i -> infinity,
    q_i/A_i <= r_i/t ->0,
    ord_(E_i)(F_M)/(M A_i) ->1.                         (4)

Thus a fixed upper bound for A_i on the relevant fixed-part primes would finish the construction, but that bound is not supplied. More sharply, it would suffice to bound A_i by C(1+q_i) on those primes for a uniform C. Equation (3) would then give r_i>=min(delta,t)/C. Such a comparison is needed ONLY on dangerous fixed-part primes, not on all valuations.

An unrestricted reverse comparison is false even in a smooth local chart: for the monomial divisorial valuation with primitive weights (p,1) on (x,t), A=p+1 while ord(t)=1. Here the anti-canonical system is free and F_M=0, so this example does NOT disprove the desired operation or its fixed-part-specific comparison. It only prevents replacing the missing comparison by a general valuation inequality.

Write w_i=ord_(E_i)/A_i. Then A_X(w_i)=1 and w_i(m_z)->0. This is the opposite of the base-concentration regime used in K's bounded-axes contradiction. The source proof cannot be invoked by relabelling this sequence. The higher-dimensional base also permits fixed components whose image is a proper positive-dimensional subvariety through z; the one point ideal can have value zero there. Generic slicing preserves finite complete systems as in C-H, but gives no uniform reverse discrepancy estimate on the new exceptional primes.

## Attempts to remove that regime

1. **Powers and averaging.** Products of sections imply F_(km)<=kF_m, but powers alone give equality for the generated product subsystem. Averaging arbitrarily many general members of the SAME complete degree-m system leaves F_m/m unchanged. The moving coefficient can be reduced, but the ratio in (4) remains. The full degree-km system might improve the fixed part; a uniform improvement is exactly additional work, not a consequence of the product construction.

2. **The strongest primary fibrewise method.** Birkar's Section 8 separates the vertical fixed part from a free general-fibre system. Subtracting a fibre boundary kills non-klt centres and gives an absolute discrepancy gain proportional to fibre order. Chen extends this using hyperplane lifting and isolated non-klt centres. Equations (2)--(4) already retain that gain. Their strictness and connectedness arguments do not divide it by A_X(E), and the bad regime has unbounded A_X(E) with negligible normalized base order. Applying the same method a second time does not give the required reverse comparison.

3. **Threshold rescaling and the canonical character.** For a witness to near failure, the fixed system has lc scaling lambda_i>1 with lambda_i->1. On a resolution this produces an exact lc place for the scaled fixed system; a general residual member works once its coefficient lambda_i/M is less than one. However the scaled boundary is Q-linearly equivalent to -lambda_i K_X, not -K_X. Hence K_X+scaled_boundary is (1-lambda_i)K_X relatively, generally nontrivial. This is precisely the identity needed by the paid cone argument.

   More explicitly, on the positive anti-canonical cone, for a section of degree M and a Gauss valuation of radial weight q, the discrepancy contribution from scaling its divisor by lambda_i/M has radial term (1-lambda_i)q. A pure positive radial valuation already makes that term negative. The scaled pair is therefore not an lc cone pair of the kind used in K or C-D/E/F. It cannot be repaired merely by normalizing the witness. Adding an effective boundary worsens the radial sign. C-H's padding starts with an exact degree-b lc complement; applying it after arbitrary rational rescaling would require a different construction and potentially unbounded b, whereas its pinning theorem fixes the dimension d+b. No bounded replacement is constructed here.

4. **Exact versus approximate slice transfer.** C-F transfers a sign only after w(f_j)=0 and exact lc equality are established. In (4), small normalized discrepancy and near saturation are not exact equalities. C-E's rational perturbation depends on the individual germ and a pre-existing exact common slice; its all-functions estimates do not supply a uniform conversion of these near-lc systems into a canonical-character-matched slice. This is not a criticism of that theorem; its hypotheses are simply different.

The outstanding operation can therefore be stated without a named black box: uniformly improve the fixed part of a bounded relative anti-canonical system so that its multiplicity at EVERY prime stays a fixed fraction below M A_X, including the regime (4), while preserving the same bounded integral index and the original neighbourhood. Equivalently, construct a bounded effective correction that restores exact canonical-character lc data from the rescaled systems without losing the original discrepancy comparison. Neither operation was closed. No weaker absolute-gap or vertical-buffer assertion is offered as a nominee.
