# Prefreeze calculation: q replicas close the missing moment

NOT FROZEN. This records the feasibility calculation before extended author proof; primary entropy comparison and constants still to be checked.

Fix q,ell; N=qh. Table alpha ranges over weak ell-compositions of q; prescribed counts t_alpha have sum h and sum alpha_u t_alpha=s_u. Define exchangeable P on [ell]^q by P(word)=t_alpha/(h*multinomial(q;alpha)). Its one-coordinate marginal is pi=s/N. For a fixed hypermatching, D_t=h!/prod t_alpha! * prod multinomial(q;alpha)^t_alpha color partitions realize t. Hence p_t=D_t/(N!/prod s_u!). Log p_t=hH(P)-NH(pi)+O_(q,ell)(logN), uniformly to boundary.

For the qth trace of A=TT*, take q colored vertex partitions Z_1,...,Z_q and their joint vertex type Gamma on [ell]^q. Each adjacent pair has marginal R_i. The probability that a uniform hypermatching has prescribed t at both partitions is a sum over joint block tables with exchangeable laws Q_i on ([ell]^2)^q. Each Q_i has tuple marginals P,P and coordinate marginal R_i, so I(Q_i)>=I(R_i). The type count exponent is hH(Q_i)-NH(R_i).

After the q kernels and outer trace sum, the full exponential coefficient is
 H(Gamma)+qH(pi)-sum_i H(R_i)+(1/q)sum_i H(Q_i)-2H(P)
 = -TC(Gamma)+sum_i I(R_i)-(1/q)sum_i I(Q_i).
For each tree obtained by deleting one edge of the q-cycle, chain rule/conditioning gives TC>=sum_tree I(R_i). Averaging gives TC>=(q-1)/q sum_i I(R_i). Thus exponent<=0 for EVERY joint type and every compatible block table. There are polynomially many types since q,ell fixed. This yields a uniform polynomial qth trace moment, even for rare tables. It replaces the failed fourth moment; no claim of mathematical novelty yet.

Expected compatible end: orbit indicators of fixed d vertices lie in hyperedge-product span P_d, via pair co-membership indicators and expansions (any nonzero monomial uses at most d distinct hyperedges intersecting those vertices). A remaining completely outside hyperedge kills the sign representation for N>qd. Source's tableau count gives dimension c_d N^(d/2). Schatten compression and qth moment then give ||T(I-Pi_d)||^(2q)<=poly(N)/(c_d N^(d/2)). Choose d/2>momentExponent+2qK. Exact containment has numerator prod_alpha (t_alpha)_(m_alpha) (alpha!)^(m_alpha), denominator prod_u(s_u)_(a_u); degree at most d in all block-type counts.

No extended theorem proof or new statement freeze has occurred at this point. The main risks being checked are normalized trace factors, arbitrary zero type entries/unbalanced cells, orbit span degree, and compatibility with known primary table/spectral arguments.
