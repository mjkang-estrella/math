# The actual source hierarchy has an unavoidable central peak

Author deduction from the exact source block parameters and section preparation. This obstructs the UNCHANGED source lattice construction for the full frozen thin-covering target; it is not an impossibility theorem for other lattices.

## 1. Exact folded entropy asymptotic

The source defines h=sqrt((9/4)log b), f(t)=h gamma_1(ht)+h gamma_1(h(t-1)), a=P(|X|<=h), and mu=a^(-1) integral_0^1 f log f. Under the source folding map from X conditioned on |X|<=h, put Z=|X|. At its image t,

 log f(t)=log h-(1/2)log(2pi)-Z^2/2 + log(1+exp(h Z-h^2/2)).

The formula also holds at X=0, a null event. The last expectation tends to zero: on Z<=h/4 it is <=exp(-h^2/4); on Z>h/4 it is <=log2+h^2/2, and the conditional probability is <=2 exp(-h^2/32)/a. Also E[Z^2 | Z<=h] ->1. Consequently

 mu=log h-(1/2)log(2pi)-1/2+o(1),

with an absolute error as b->infinity. In particular, for all sufficiently large b,

 mu<=log h-(1/2)log(2pi)-2/5.

This uses a sharper asymptotic than the source's printed mu=log h+O(1), derived directly from its definitions, without numerical sampling.

## 2. Zero is not an eligible retained atom, but is in the lattice

The source chooses log p_b<=b mu_b-3b^.56 and L_b=Z^b+p_b^(-1)C_b. Regardless of the chosen line C_b or any inter-block shears, zero belongs to every L_b. Hence its single normalized block Gaussian weight obeys

 log[(h_b^b/p_b) gamma_b(0)] >= (2/5)b+3b^.56.

For the source full vertical lattice ML, with D=sum_i b_i+T, its covolume is D_v=product_i h_i^b_i/p_i. Thus

 D_v gamma_D(0) >= exp[(2/5)sum_i b_i -(T/2)log(2pi)].

The terminal dimension T is bounded by a fixed constant determined by the fixed cutoff B. Taking B sufficiently large is permitted in the source, and fixes it BEFORE n. For b_1=ceil((loglog n)^2) and n sufficiently large,

 D_v gamma_D(0) >= exp(b_1/3).

Source eligible-atom cap only concerns SELECTED patterns; it cannot bound this unselected zero lattice point. A fixed cutoff not enlarged to the asymptotic threshold changes only a bounded collection of final block factors; the large first block still gives exp(c b_1) after absorbing fixed constants.

## 3. Horizontal averaging forces actual essential maximum

Use the source affine body K and final lattice Gamma={(h+Zl,Ml): h in Lambda_h,l in L}. Put rho=vol_n(K)/(D_h D_v)=C_*n log n. For a vertical target y, the contribution from l=0 alone is

 m_0(x,y)=sum_(h in Lambda_h)1_(K_y)(x-h).

Its normalized horizontal torus average is exactly vol_m(K_y)/D_h. The source section lower bound gives, for every |y|<=R,

 E_x m_0(x,y) >= (1/2)rho D_v gamma_D(y).

Take |y|<1 (R>=1), so gamma_D(y)>=exp(-1/2)gamma_D(0). For every such y the mean exceeds (rho/4)D_v gamma_D(0) since exp(-1/2)/2>1/4. Thus the horizontal set on which m_0 exceeds that threshold has positive measure. Measurability and Fubini give a positive full-dimensional set of such points: the integral of a positive measurable fiber measure over the vertical unit ball is positive. This proves

 ess sup_(x,y) m_K,Gamma(x,y) >= (rho/4)D_v gamma_D(0)
 >= (rho/4)exp(b_1/3).

No choice of horizontal shear Z removes the l=0 contribution. This is an actual overlap count for the source K, not merely a Gaussian proxy. The body normalization places 0 in K, so (1+1/n)K contains K; the completion dilation cannot lower the bound. Rescaling back to the source final lattice preserves multiplicity. Since b_1 diverges, this construction cannot establish a dimension-independent C in the frozen target.

## Consequence and remaining task

A two-sided estimate for RETAINED Boolean branches does not repair this issue. One needs a different vertical lattice with uniformly bounded normalized periodized section mass, a non-product/fiber construction eliminating the zero-atom spike, or an entirely different lattice selection. A lattice always contains zero, so translating the center of the body only moves the high-overlap target and does not remove the supremum. This obstruction is separate from the cube completion counterexample and from Lund's arbitrary-subset hashing barrier.
