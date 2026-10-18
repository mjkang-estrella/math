# Cross-scale gain: a one-step estimate and two norm obstructions

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

Pre-freeze author work; no full nonuniqueness claim. All measures below are velocity measures, and the collision normalization is exactly that of `same-width-gain.md`. The formulas are consequences of the incoming-pair sphere law, not new assumptions about the source solutions.

## 1. A fixed wider Gaussian product does not close

Take one input delta_0 on R^3 and the other G_1(vbar) tensor delta_0(v3). For r=|vbar|>0 the gain has density

    P(delta_0,G_1 tensor delta_0)(vbar,z)
       =2/(sqrt(pi) r) exp(-(r^2+z^2)^2/r^2).             (1)

Indeed, Carleman's plane equation is vbar dot qbar=r^2+z^2. Integrating G_1 on that line gives (1). Alternatively (1) follows by direct integration of the incoming-pair sphere measures, so both singular inputs are legitimate. The transverse marginal is

    2/(sqrt(pi) sqrt(r)) integral_R exp(-(r+u^2)^2)du,

after z=sqrt(r)u. It is asymptotic to a strictly positive constant times r^(-1/2). Thus this gain cannot be dominated by G_1 tensor any finite axial measure. By taking positive transverse widths tending to zero, the same fact excludes a width-ratio-uniform extension of the fixed broader-Gaussian product norm. It does not exclude scale mixtures or bounds exploiting position/velocity correlations.

## 2. A one-step positive scale-mixture bound does hold

Let 0<d<=D, and let nu,mu be nonnegative axial measures. Set

    M_D^half(nu)=integral exp(a^2/(2D^2))nu(da),
    V_d(y)=(G_{sqrt(2)d}*|.|^(-1))(y),
    K_dD(y)=exp(-|y|^2/(2D^2)) V_d(y).

Then

    P(G_d tensor nu,G_D tensor mu)(y,z)
      <= [8/(sqrt(2pi)D)] K_dD(y) exp(-z^2/(2D^2))
             M_D^half(nu) M_D^half(mu).                 (2)

Proof. Condition on axial inputs a,b. Split each transverse Gaussian exponent in half. The product of normalization factors is 4. Conservation of energy about zero gives

    |pbar|^2+|qbar|^2 >= |y|^2+z^2-a^2-b^2.

Since d<=D, the removed half-exponent is at least the left side divided by 2D^2. In the remaining Carleman integral, integrate G_{sqrt(2)D}(qbar) on its line; discard its nonpositive Gaussian line-offset exponent. This gives at most 1/[sqrt(2pi)D|y-pbar|]. The leading Carleman factor 2 and the splitting factor 4 prove (2).

K_dD is a positive mixture of centered transverse Gaussian densities, up to its total mass. This follows without a representation theorem: use

    1/|y|=pi^(-1/2) integral_0^infinity u^(-1/2) exp(-u|y|^2)du.

Convolving a centered Gaussian with each centered Gaussian in this integral gives another centered Gaussian; multiplication by exp(-|y|^2/(2D^2)) again gives a positive multiple of a centered Gaussian. Tonelli justifies all these operations. The resulting widths lie below sqrt(2)D; no common positive lower width is claimed independently of d.

Moreover

    Z_dD=integral K_dD(y)dy <= C D.                     (3)

To prove (3), interchange the convolution and spatial integral. For each translation p, the integral of exp(-|y|^2/(2D^2))/|y-p| is bounded by C D uniformly in p. For example, split |y-p|<=D, where the integral is at most 2pi D, and its complement, where it is at most D^(-1) integral exp(-|y|^2/(2D^2))dy=2pi D. Integrate the transverse Gaussian probability in p.

Thus (2) has a product majorant with a positive transverse Gaussian scale mixture and an axial Gaussian; its total mass is at most C D times the two displayed input moments. Its axial moment with weight exp(z^2/(4D^2)) obeys the same O(D) bound. This proves the proposed one-step operation, including arbitrary axial measures satisfying the stated moments.

## 3. Why this is not yet an iterative class

The output of (2) has axial width comparable to D while its transverse mixture contains narrower widths. It therefore need not satisfy the componentwise moment condition exp(z^2/(transverse width)^2) used by the repeated-gain lemma. One cannot silently replace that condition by arbitrary independent axial laws and still expect a ratio-uniform mixture majorant.

An exact limiting obstruction is provided by two axial atoms at +R e3 and -R e3, R>0. Their output is R times area measure on the unit sphere mapped to the sphere of radius R. Its transverse marginal has density

    2/sqrt(R^2-|y|^2) 1_{|y|<R}.                       (4)

Every positive centered Gaussian scale mixture has a radially nonincreasing transverse density. No finite such density dominates (4): as radii approach R, (4) diverges, forcing a nonincreasing majorant to be infinite at every smaller radius. Equivalently, the mass of (4) in an outer annulus of width delta is of order sqrt(R delta), while an integrable nonincreasing radial majorant of mass M assigns that annulus at most C M delta/R. Uniform finite M is impossible as delta decreases. Approximating the axial atoms by arbitrarily narrow transverse Gaussians gives the corresponding failure of any uniform bound over the enlarged input class.

This obstruction concerns an excessively large, decoupled envelope class. It does not show that the actual packets develop such separated axial atoms at the relevant transverse widths; their joint age/position/velocity structure may rule this out. Nor does it refute the full provisional L2 nonuniqueness direction.

## 4. A separate spatial summation defect

The parent localized single-scale envelope uses fixed eps>0, h_s=1+alpha t/s,

    A_s=(K/s)h_s^(2eps-1), D_s=d_s h_s^eps,
    L_y=sqrt(beta) D_s(s+alpha t)/alpha.

At a fixed t>0 on the sigma-axis, dist(0,E_s) is comparable to s, while L_y is comparable to s^(a-eps). Hence the transverse spatial factor tends to one as s->0. The axial factor equals one at z=sigma t. The axial evolution contains its positive freely compressed initial term, whose mass is fixed. Consequently the sum of these upper envelopes diverges there: A_s is comparable to s^(-2eps), and even eps=0 would give a nonsummable constant per scale. This is a defect of that upper bound, not a divergent actual solution.

The exact free packet instead has the extra factor min(1,[s/(t d_s)]^2) from its transverse spatial mask. Recovering an appropriate nonlinear version of this dilution, simultaneously with a usable mixed-width gain norm, remains necessary. The same-width calculation alone does not supply it.

## Authorship and limits

The parent proposed testing positive transverse width mixtures after author-checking (1). Bound (2), its exact input moments and the failure of the enlarged decoupled class were then derived here. The spatial summation defect was independently noticed on both author sides. These are collaboration records, not independent proof or contribution gates. The overall provisional direction remains unfrozen; global continuation and source branching for any changed packet remain unproved.

## 5. Moving transverse centers do not preserve the source sheet estimate

Parent author assistance supplied the following additional obstruction, checked here. Let c=G_delta(vbar-b) tensor delta_U, where U stays bounded and 0<delta<<|b|<<1. For the source weight H, at output v=(b,U) the Carleman planes are vertical. Their transverse line integral of the singular factor is comparable to |n_hat dot b|^(1-q), where n=vbar-pbar. Averaging the transverse Gaussian gives

    P(c,H)(b,U) comparable to delta^(-1)|b|^(1-q),
    H(b,U) comparable to |b|^(-q).

The angular integral is finite because 1<q<2; the radial average of 1/|n| is comparable to 1/delta. Smooth Gaussian/polynomial factors in H change only fixed constants in this bounded region. Therefore P(c,H)/H grows at least like |b|/delta.

This is also an essential-supremum obstruction, not merely an isolated point: restrict incoming n to a transverse annulus of radius delta and directions with |cos(theta)| bounded above and below by positive constants. For |vbar-b|<=c delta and |v3-U|<=c delta|b|, the same lower bound follows on a positive-volume output set by integrating a bounded axial interval in the plane. The source's centered-sheet constant consequently cannot be extended uniformly merely by assuming that b tends to zero. An added transverse affine flow needs a new hot weight or a spatially correlated estimate. This does not rule out either of those alternatives.
