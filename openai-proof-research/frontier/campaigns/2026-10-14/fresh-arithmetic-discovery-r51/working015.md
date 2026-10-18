# Joint torus packets: two attempted mechanisms

This is author exploration, not independent review. The full working question is in scope-status.md. The source pin is fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. We accept its theorems as stipulated.

## Source interface and historical distinction

The prime-degree paper's thm:main treats every fixed prime n>=5, all full lattice local types and multiplier-order discriminants tending to infinity. Its adelic proposition identifies the measure as a torus Haar pushforward. Here only maximal-order ideals are used. Both coordinates of our pair have exactly that marginal. For a compact K with marginal mass at least 1-epsilon, lambda(K squared)>=1-2epsilon. Thus joint tightness costs no new estimate. Diagonal A invariance also follows directly.

The quartic companion thm:main concerns primitive fields and invertible ideals of arbitrary orders; the sextic thm:main concerns primitive fields and maximal orders only. Neither inspected main statement asserts joint mixing. The sextic product rule is a statement about different root directions within one augmented state, not independence of copies of a packet.

I145 and I148 concern polynomial-index class-group cosets, including local types. Their full C145 remains parked. Their internal torus-versus-ambient-Hecke warning is also relevant here: at a split prime there are n torus-stable index-p neighbors but (p^n-1)/(p-1) ambient neighbors. A prescribed ideal translate is not an ambient Hecke average. The present full working question selects a correlated pair from the entire packet rather than selecting a coset subpacket. This distinction is not evidence of literature novelty.

## Route A: lift the source entropy and conditioning argument

For any joint subsequential limit lambda, the source ball estimate gives only

  lambda(xB(r) times yB(r)) <= min(m_n(xB(r)),m_n(yB(r))).

Even using the exact Haar marginals instead of source r^n, the exponent obtained this way is dim(SL_n)=n^2-1, not twice that dimension. The diagonal Haar measure has exactly these marginals and this local exponent. It is invariant under diagonal A, and its entropy for (a,a) is the one-copy Haar entropy. Consequently no positive-entropy statement inherited separately from the two marginals excludes it. This is an exact logical obstruction, not a purported arithmetic realization with escaping shift classes.

The attempted use of the sextic product theorem fails at its contraction hypothesis. In G times G let U_alpha^(1) and U_alpha^(2) be the corresponding one-dimensional root groups. Every (a,a) acts on both by the same scalar alpha(a). Fixing one requires alpha(a)=1; strictly contracting the other requires |alpha(a)|<1. These cannot hold simultaneously. The source argument can distinguish different roots, but cannot split the two occurrences of the same root. The joint coarse root group is U_alpha times U_alpha, within which a diagonal line remains possible. Adding intermediate resolution or more conditioning does not itself supply the missing contraction. An independent action of A times A is precisely what the joint packet lacks.

This is a complete obstruction to that proposed direct application, not a proof that every adaptation of the source is impossible.

## Route B: unfold a pair of lattice vectors

The source's single-vector identity is packets.tex prop:unfolding. At maximal order, Q=sqrt(D), P(a)=1, and its denominator is h_K vol(F)=sqrt(D) kappa_K. We retain that exact normalization.

Let J be a nonzero fractional ideal and choose nonnegative compactly supported Borel functions f,g away from zero. Write E_f for the sum of f over nonzero lattice vectors. For alpha in I and beta in JI put

  a=(alpha)I^(-1), b=(beta)(JI)^(-1).

Both a,b are integral nonzero ideals, and [b]=[J]^(-1)[a]. Conversely every pair of integral ideals with this class relation occurs. Choose tau_ab with (tau_ab)=J b a^(-1). Once alpha is chosen, all beta are alpha tau_ab epsilon, epsilon in O_K^units. Define z_ab,epsilon=N(J)^(-1/n) sigma(tau_ab epsilon), coordinatewise. Its absolute coordinate product is N(b)/N(a).

For x>0 let V_{f,g;z}(x) be the sum over all signs of the logarithmic integral of f(v)g(v z) on the coordinate-product fiber |product v_j|=x, with the same deleted-logarithm normalization as source eq:product-fiber. Then Tonelli and the same unit unfolding give the exact extended-integral identity

  integral E_f(L_1) E_g(L_2) d lambda
  = 1/(sqrt(D) kappa_K)
    sum_{a,b integral; [b]=[J]^(-1)[a]}
    sum_{epsilon in O_K^units}
      V_{f,g;z_ab,epsilon}(N(a)/sqrt(D)).                 (1)

Proof: start with the class average and integral over F of the sum over alpha,beta. Partition by a,b. Alpha runs over one free unit orbit; beta/alpha runs over tau_ab times all units. Unfold only the common alpha unit orbit against F. The relative unit epsilon remains a separate sum. Translation of deleted logarithms has Jacobian one and gives (1). Changing tau_ab permutes epsilon. Signs are included in C and in V; no second independent sign average is introduced. Nonnegative integrands justify every interchange, even if the integral is infinite.

Two independent scalar source counts do not bound (1) sharply: they discard both the class relation and the relative-unit/archimedean ratio z. In particular the coordinate product N(b)/N(a) alone does not determine V: it does not determine whether the two boxes overlap after coordinatewise dilation. Even in a fixed field a nontrivial unit has norm one but arbitrarily large powers in some embedding; these can move a fixed compact box disjoint from itself. The relative-unit sum and class condition are actual data, not harmless constants uniform in K.

The ordinary norm sum in the source has one ideal and one (n-1)-dimensional fiber. Here the same real parameter drives both vectors; introducing a second independent fiber would replace the desired joint measure by its product marginals. No such replacement is justified. Formula (1) does not itself give a measure-determining family of tests for the joint space, so even a bound for these Siegel products would still need a geometric covering or approximation argument.

## Closest primary operation

Khayutin, Joint Equidistribution of CM Points, arXiv1710.04557v3, Conjecture1.1 and Theorem1.3, treats a related class-translate mixing operation in quadratic CM packets. The theorem assumes two fixed split primes and absence of an exceptional zero. Sections1.5–1.7 explain the extra cross-correlation with Hecke correspondences: a two-ideal invariant leads to a short shifted convolution and a two-variable sieve. This is not supplied by marginal equidistribution. Its quadratic additive norm relation is not derived by (1) in prime degree n>=5. We do not import that theorem outside its group or hypotheses.

Khayutin, Arithmetic of Double Torus Quotients, arXiv1510.08481v2, Theorem1.1, gives a lower entropy bound for maximal-order packets with 2-transitive Galois action, conditional on a probability weak limit. This is a one-packet entropy theorem. It does not provide the new joint correlation estimate in our unrestricted prime-degree scope. Only the stated introductory ranges were read, not its whole invariant-theory proof.

A finite-idele shift of large minimal ideal norm rules out certain exact low-complexity coincidences, but exact nonincidence does not imply a uniform bound on neighborhoods of fixed Hecke correspondences. No such quantitative passage was proved here. In particular the working question was not declared solved by algebraic joining classification; that classification was not independently verified in the needed setting during this round.

## Disposition

Two concrete proof routes were attempted beyond marginal transfer. Route A has the explicit repeated-root obstruction. Route B reaches the exact correlated identity (1), whose class/relative-unit estimate remains unpaid. No full candidate, no technical partial nomination, and no count change. A useful continuation would need a uniform cross-correlation estimate retaining these data, rather than another invocation of marginal entropy or a one-variable ideal count.
