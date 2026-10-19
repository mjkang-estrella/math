# Sextic orders: paired local feasibility

All work here preceded selection. No target was frozen, no full all-order theorem is claimed, and no nominee or contribution rating is supplied. The proposed direction was full volume-weighted equidistribution for invertible-ideal packets of arbitrary orders in primitive totally real sextic fields, with order discriminant tending to infinity, including growth of conductor in a fixed field. This is an exploratory direction, not a frozen statement. Neither a maximal-order, bounded-conductor nor subsequence substitute was adopted.

## The actual paid operations

The pinned sextic source015 `thm:main` concerns maximal orders. Its arithmetic section supplies `prop:packet-volume`, the ideal/vector unfolding, the primitive-field trace-slice estimate, and the paired primal/dual tube count. The pair consists of d in I and ell in the trace dual of I; z=d ell lies in the codifferent and has the prescribed trace. Maximal-order ideal divisors bound its multiplicity. The assembly uses the full interval version of that estimate in its root-activity argument. Single-vector nonescape alone is not the whole interface.

The prime-degree companion's `lem:local-moment` already works with arbitrary normalized local lattices L with R_max L=R_max, retaining their unit-membership weights. Its exact shell mass is Z_S/q, and its fractional moment/tail estimates retain that q^{-1}. These are actual proof operations, not just the prime-degree headline. The quartic arbitrary-order companion has much more than ordinary counting: `lem:fourier-shell-estimates`, `prop:additive-equidistribution`, `lem:add-profile-bounds`, and `lem:add-nonscalar` give conductor-uniform quadratic Fourier shells, finite global profile expansion and a shrinking affine-trace-plane estimate. In the nonscalar proof, large field discriminant forces a denominator; small field discriminant with a large order index splits between boundary decay in the original sum and inverse-order congruences. The latter uses Smith normal form, inversion on finite algebra units and a nonzero adjugate polynomial. Its scalar series is evaluated with its exact trace marginal. These are stronger compatible reductions than an unspecified appeal to Fourier analysis.

## Two diagnoses that do not constitute a new theorem

For a split prime p, put R=Z_p+p Z_p^6 inside E=Q_p^6. Every unit tuple u in (Z_p^*)^6 gives the integral invertible principal ideal p u R, of index p^6 in R. Indeed p u R is contained in p Z_p^6, and multiplication by p u has determinant of valuation six. Two such ideals agree exactly when u/v lies in R^*. Reduction modulo p identifies the quotient of unit tuples by R^* with (F_p^*)^6/F_p^*, so there are (p-1)^5 distinct ideals of this norm. Thus the maximal-order bound d_R(p^6)<=tau_6(p^6)=462 cannot hold uniformly in p for arbitrary R. This concerns RAW coefficients, not the normalized packet law. The prime-degree companion's weighted shell identity is precisely a stronger available repair; the example is not evidence against equidistribution.

The ordinary trace-lattice geometry DOES extend to arbitrary global orders. Let R be an order in a primitive totally real sextic field and D_R its discriminant. Its trace dual R^vee has covolume D_R^{-1/2}. Since 1 is primitive in R, the trace map R^vee->Z is onto; the trace-zero slice has covolume sqrt(6) D_R^{-1/2}. For alpha in R outside Q, primitivity gives Q(alpha)=K and

    disc(Z[alpha])=[R:Z[alpha]]^2 D_R >= D_R.

The discriminant is the product of thirty conjugate differences. Subtracting the scalar mean does not change them. Consequently every nonzero projected vector from R in 1-perp has length at least c D_R^{1/30}. Fixed-dimensional lattice transference yields fundamental cells for the dual trace slice of diameter at most C D_R^{-1/30}, exactly the source's form with the order discriminant. The constants are absolute in dimension six. Conductor growth is not a failure of this geometric step.

## Strongest local paired reduction

Here is an exact calculation, with no Gorenstein hypothesis. Let E be any degree-n finite etale Q_p-algebra and R any Z_p-order in E. Put

    R^vee={y in E: Tr_E/Qp(yR) subset Z_p},
    W=E direct-sum E,
    B((x,y),(x',y'))=Tr(xy'+x'y),
    L=R direct-sum R^vee.

Trace duality makes L self-dual for B. In dual Z_p-bases, Q_1(x,y)=Tr(xy) is a sum of n hyperbolic products. Simultaneous multiplication rho(a)(x,y)=(ax,ay) is self-adjoint. The product map Psi(x,y)=xy satisfies Tr(a Psi)=B(rho(a)(x,y),(x,y))/2 over Q_p, also at p=2; integrality follows directly from the product form. The stabilizer order {a:rho(a)L subset L} is exactly R: preservation of R gives a=a1 in R, and a in R preserves R^vee by trace duality. Non-principality of R^vee does not obstruct this construction.

In fact one can bypass generic quadratic Gauss phases. Let psi have conductor Z_p and take Haar probability independently on R and R^vee. For A in E, integrate in y first:

    gamma_R(A)= integral_R integral_R^vee psi(Tr(Axy)) dy dx
              = vol_R{x in R: Ax in R}
              = [R : R intersection A^{-1}R]^{-1}.

For noninvertible A, interpret A^{-1}R as its inverse IMAGE, not multiplication by an inverse. The annihilator of R^vee is R, so the middle equality is exact. The subgroup has finite index because A is a continuous Q_p-linear map. Averaging an additional u in Z_p^* does not change this expression, since uR=R. For scalar A with v_p(A)=-k<0 this equals p^{-nk}; for integral scalar A it is one. There are no small-prime phase exceptions in this particular product model. This is classical character orthogonality on dual lattices, not a new stationary-phase theorem.

The quartic abstract local model has rank two over a degree-three etale algebra. The model above has rank two over degree six when used here. Merely changing those degree constants in its Smith/congruence argument would be a parameter transfer, not evidence of substantiality. The strongest compatible source operation must be checked before claiming a codifferent or bad-prime obstruction; that check removes both proposed local obstructions.

## What is still missing in this round

The local identity is not the global tube estimate. One still has to unfold the SAME invertible-order-ideal packet with its regulator, class and sign weights; relate each discrete primal/dual fiber to the local law without losing conductor factors; and bound its affine-trace thin slabs uniformly throughout the full required time interval. Neither two independent single-vector counts nor replacement by the product of marginal packet measures does this.

The quartic companion already demonstrates a strong template for the global multiplicity step. `lem:ext-comparison` factors equal product fibers over Q or Q_p; `lem:ext-density` disintegrates the local law with the exact discriminant/Euler factor; `lem:ext-global-cosets` bounds global pairs in one coset assignment by 32; the following local-majorant proof sums finitely many assignments. Those operations were inspected, including the comparison and global-coset proofs. Its exterior-square representation and cubic resolvent differ from the present primal/dual product. The whole disintegration proof was not freshly read, and no completed adapted global equality or estimate is supplied here. The local calculation suggests compatibility, rather than proving that a new difficult operation is necessarily unpaid.

Actual historical I145 already gives full local-type single-vector cusp moments and identifies the sextic maximal-order versus quartic arbitrary-order distinction. I148's retained snippets concern character-weighted sparse cosets, and r51's complete `working015.md` develops correlated two-copy packets, a different problem. Its repeated-root contraction obstruction and relative-unit/class relation are not claimed solved by this one-packet product model. No same-family history rating is adopted.

[ELMV, published Annals 173 (2011), §§5.3–5.5](https://annals.math.princeton.edu/wp-content/uploads/annals-v173-n2-p05-p.pdf) supplies the actual adelic packet double-coset proof and local-homothety interpretation. Equality of multiplier orders alone is not silently substituted for a fixed local lattice type. [Wieser–Yang, 2201.05380v1, Theorem1.7 and Lemma4.9](https://arxiv.org/pdf/2201.05380v1) is a further actual primary comparison: the local proof uses Hilbert90, norm-one groups and maximal-order valuation intervals for a quadratic extension of a base field. Its uniformity in the base field does not give the present sextic arbitrary-order product estimate. The authors' Remark1.12 explicitly locates the maximal-type use at that lemma; a suggested extension is not an available theorem. Only the stated primary passages were read, not their full analytic proof chains.

No full candidate was completed. No local model, raw-coefficient obstruction, rank/degree variant or conditional global bridge is promoted. These calculations are not a proof of impossibility or an exhaustive literature claim.
