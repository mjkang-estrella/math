# Nonvacuity, strongest reduction, and remaining applications

The frozen theorem concerns every probability law on the entire normalized univalent half-plane class satisfying exact inverse-square affine covariance. It adds no image boundedness, boundary smoothness, finite number of critical points, or separation assumption. Exact covariance is the defining structural hypothesis, not a conclusion being inferred for arbitrary conformal maps.

There are genuine examples throughout the exponent interval. For 3/2<alpha<=2 and a real, use the branch arg(z-a) in (0,pi) and define

    H_(alpha,a)(z)
       =[(z-a)^alpha-(i-a)^alpha]/[alpha(i-a)^(alpha-1)].

The power is injective on H: equality forces equal moduli and arguments differing by 2pi/alpha, which is at least pi; two arguments in (0,pi) cannot differ by that amount. The normalization is H(i)=0, H'(i)=1. Rebasing sends a to (a-x)/y. With

    Z_alpha=integral_R (1+a^2)^(-(alpha-1)) da < infinity,
    dmu_alpha(a)=Z_alpha^(-1)(1+a^2)^(-(alpha-1)) da,

the inverse-square derivative weight cancels the numerator density. Substitution a=x+yb gives the multiplier y^(1-2(alpha-1))=y^(-(2alpha-3)). Thus this is an exact law with beta=2alpha-3. Choosing 15/8<=alpha<=2 realizes the entire frozen interval [3/4,1]. At alpha=2 the normalization constant is pi and this is the critical law in Claim B.

For these power laws, q=-(alpha-1)iy/(z-a) and k=alpha/2. The two q-dependent terms in k^2 J_k cancel pointwise:

    (2k-1) Re q + |q|^2=0,
    J_k=(alpha-2)/alpha=(beta-1)/(beta+3).

In particular J_k has no positive part for these examples, and the mean identity is attained with a negative constant. The quantitative proof does not assume that all laws have this special form, or restrict to powers. The exponent 1/4 in the squared compact error is not claimed optimal; this example does not certify optimality.

The closed proposed bridge in the author proof has two separate parts. Component persistence, with a proof of infinite-fiber consistency, Borel selection and affine equivariance, strengthens the source's rank comparison to a gain at least c J_+^3. Exact weighted transport then bounds E J_+^4 by the scaling deficit. The determinant-Laplacian identity converts expected absolute Jacobian control into a local L2 estimate for F''', avoiding a division by F'' that would be invalid near the affine model. Projection of F''(i) onto its coefficient circle provides one Borel model choice for every compact and derivative order.

The following attempted inferences were insufficient and are not used:

* Positive pairwise rank gains without a quantitative lower bound yield no specified rate.
* Classification at beta=1 plus compactness supplies only an unspecified modulus.
* The strict first-power source does not remove inverse-square endpoint losses.
* The source eigenmeasure cancellation C(2/rho)^n does not vanish at rho=2. It does not produce a critical affine law.
* Dividing the determinant relation by the pre-Schwarzian would lose the affine model and near-zero regions. The identity used in the proof avoids that loss.

The critical operator's finite-scale growth, i135 E_gamma/W2, and the other frozen old targets remain outside this theorem. A rate for approximate covariance is also outside it. No application to those problems is asserted. No new family was selected. The exact-law theorem is submitted for the parent's independent correctness and separate substantial-contribution reviews; its status is not an acceptance or self-grade.
