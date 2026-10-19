# Signed moments and slowly vanishing fields: preselection calculations

No target was frozen. These are compatibility calculations, not nominated findings, author contribution ratings, or correctness gates. The source pin is fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Every source operation below is stipulated, including its all-length intermediate formula. See source-register.json for exact raw paths, blobs and hashes.

## 268: strongest available reduction for odd rings

The periodic manuscript's `prop:transfer` gives one compact self-adjoint X_b with Z_k(b)=sum_i lambda_i(b)^k for EVERY integer k>=4, not only even k. Its proof groups absolutely convergent chronological bond histories, reverses the spatial enumeration without reversing the time products, and handles the rotation seam explicitly. The kernel is signed; Perron positivity is not an available premise. The main gap theorem and `prop:bootstrap` use even spatial powers as probabilities. Its exact coupled cancellation also gives S(n,2b)>=S(n,b)^2 T(2n,b).

Aizenman–Nachtergaele, [cond-mat/9310009v1](https://arxiv.org/pdf/cond-mat/9310009v1), §2.2 equations (2.10)–(2.12), already supplies the chronological Poisson expansion for bounded local self-adjoint bond terms. Its special positive loop formula for the singlet model has a bipartite restriction and is not an odd-ring gap theorem for the bilinear spin-one Hamiltonian. The source supplies the stronger signed transfer contract itself. This distinction is why the following comparison uses signed moments, not a positive-kernel shortcut.

Here is the complete prefreeze algebra. At fixed b let A_k=sum_i |lambda_i|^k. Suppose an even n has S(n,b)=A_(2n)/A_n^2>=1-epsilon>1/2. The normalized n-th powers have a unique largest weight p_0>=S(n,b)>=1-epsilon. Hence there is a unique eigenvalue of largest absolute value a>0, and the ratio sum_(i!=0)|lambda_i/a|^n <=epsilon/(1-epsilon)<1. Since EVERY sufficiently large odd moment is the positive physical partition function, that unique leading eigenvalue is +a: otherwise its signed odd moments would eventually be negative. The tail divided by a^k tends to zero by dominated convergence using its summable n-th powers.

For every integer k>=n the fraction of A_k outside the leading weight is at most epsilon. Indeed if r_i=|lambda_i|/a<1 then sum r_i^k<=sum r_i^n; the fraction is sum r_i^k/(1+sum r_i^k). Consequently

    (1-2 epsilon) A_k <= Z_k(b) <= A_k.                 (1)

For even k the lower factor is unnecessary. This is a single dominant-weight estimate for the SAME spatial list, not an independent positivity assumption at each odd length.

Apply the source dyadic pair at n=n_j=2304*2^j, b=b_j=784*2^j, u=u_j=(1/5)*20^(-2^j). It gives S(n,b), T(2n,b)>=1-u and S(n,2b)>=(1-u)^3>=1-3u. In particular the preceding argument applies at both b and 2b. For every integer n<=L<=2n, absolute-moment norm monotonicity gives

    A_L(b)<=A_n(b)^(L/n),
    A_L(2b)>=A_(2n)(2b)^(L/(2n)).

Together with (1) at temperature 2b,

    T(L,b) >= (1-6u) [T(2n,b) S(n,b)^2]^(L/(2n))
           >= (1-6u)(1-u)^3 >= 1-9u.                 (2)

Thus the physical Gibbs weight of the ground eigenvector exceeds 1/2 and is unique. For its next eigenvector, exp(-b gamma_L)<=9u/(1-9u). Since u<=1/100,

    9u/(1-9u) <= (180/91)*20^(-2^j)
                 < 2*20^(-2^j) <=10^(-2^j).

This obtains gamma_L>log(10)/784 for ALL integer L>=2304, relative to the stipulated all-k transfer and even bootstrap. Non-scalarity is the same product-vector argument for odd lengths. Finitely many smaller lengths have a gap above their full ground sectors simply by finite dimensionality; this calculation asserts no simplicity there.

This calculation preceded selection. No odd-ring target was frozen or submitted. After reading the stronger all-k source operation, the apparent parity obstacle is removed by dominant-weight concentration and the source's own interpolation. There is no identified unpaid operation in this parameter extension. I39's actual disordered-bond question is different: changing bonds changes the common spatial operator/list, so this argument does not solve its relative-form or local-kernel compatibility problem. Its source265 positive replacement is not dismissed; it still has the one-sided domination and local-kernel issues recorded there. No disorder or thermodynamic uniqueness theorem is claimed here.

### Late companion comparison, still before any freeze

After the displayed feasibility calculation, the boundary-field companion's COMPLETE `sections/periodic.tex` and `sections/conclusion.tex` were read. They are stronger antecedents than its boundary-gap headline. `per:concentration` already proves positivity of the unique leading spatial eigenvalue by exactly the odd-partition-function contradiction, together with quantitative residual ratios, rotation invariance and temperature-doubling leading-eigenvalue comparisons. `co:signed` already bounds the signed residual at EVERY integer length beyond a concentrated even moment. `co:purity` carries this across two temperatures on a full dyadic interval before the physical-gap endgame. The extra boundary vector and rotation pairing make its interface stronger than the unweighted trace sign calculation above. Its fixed same-field odd-chain Hamiltonian is not asserted identical to the periodic ring. Nevertheless the operative sign/tail/interval mechanism is already explicitly paid. This late read removes any possible suggestion that the positivity operation itself was discovered here. It occurred after feasibility, before sealing, and before any freeze (none ever occurred).

## 271: fixed-temperature fields with arbitrary slow Vh divergence

The spherical companion's complete `08-global-spin.tex` proves more than a spherical headline. At each fixed finite beta above its threshold, writing V=L^3 and m=p'(0+)>0, it gives J/V->m in probability, 0<=J/V<=S, and, from its actual pressure proof, for every fixed epsilon>0,

    P_0(J/V>m+epsilon) <= exp(-c_epsilon V)

for all sufficiently large even L (a fixed prefactor can be absorbed). The transfer from a component tail to the J-tail uses a positive fraction of magnetic levels. No rate is supplied or required for the lower radial tail. On each spin-J representation, the magnetic levels r=-J,...,J have equal zero-field weights. All these are source operations already present in the same proof.

The compatible reduction works for EVERY positive h_L->0 with t_L=beta V h_L->infinity, at fixed beta. Set a_L=beta h_L. The exact tilted radial weight is

    w_a(J)=(2J+1)^(-1) sum_(r=-J)^J exp(a r).

It obeys 1<=w_a(J)<=exp(aJ). For fixed 0<epsilon<m, the event J/V>=m-epsilon/4 has probability tending to one. On that event a fixed positive fraction, depending only on epsilon,S, of magnetic levels has r/V>=m-epsilon/2. Hence the tilted normalizer is at least c_epsilon exp(t_L(m-epsilon/2)) eventually. The total tilted weight of J/V<=m-epsilon is at most exp(t_L(m-epsilon)); its normalized probability tends to zero with no rate assumption on the original lower tail. The upper tail is at most exp(t_L S-c_epsilon V), because the normalizer is at least one. It tends to zero since t_L/V=beta h_L->0. Thus J/V->m also under the tilted state.

A tempting crude union bound introduces a factor V and would wrongly require t_L>>log V. The exact geometric sum avoids it. Conditional on J, for the event r<=J-epsilon V,

    P_a(r<=J-epsilon V | J)
       <= exp(-a epsilon V)/(1-exp(-a(2J+1))).          (3)

This follows by summing exp(-a k), k=J-r, and canceling the common factor 1-exp(-a). On J/V>=m/2 the denominator tends to one; (3) tends to zero even for arbitrarily slow t_L divergence. Therefore M^3/V->m in probability and all bounded moments. Casimir and boundedness then give

    <(M^1/V)^2+(M^2/V)^2>
      =<J(J+1)/V^2-(M^3/V)^2> ->0.

No joint measurement of noncommuting components is asserted. Cauchy–Schwarz in the state and uniformly bounded component norms supply deterministic limiting polynomial expectations if wanted. Rotation treats any fixed field direction. The case t_L tending to a fixed finite t is the simpler bounded exponential tilt of the already supplied sphere law.

The complete-graph primary [Bjornberg–Frohlich–Ueltschi 1811.12834v1](https://arxiv.org/pdf/1811.12834v1), Theorem2.1 and §4, uses exactly the angular-momentum multiplicity/character representation, the geometric sum (4.6), and asymptotic concentration of the radial label to obtain sinh(hm)/(hm). Its complete-graph multiplicity saddle point is not transplanted to the lattice: source271 already supplies the lattice concentration and exponential upper tail. The displayed reduction verifies their compatibility with an unbounded but subvolume tilt. It leaves no identified new concentration mechanism, so no vanishing-field target is frozen. This does not solve r19's varying-beta, finite-volume radial fluctuation problem or alter that archive.

