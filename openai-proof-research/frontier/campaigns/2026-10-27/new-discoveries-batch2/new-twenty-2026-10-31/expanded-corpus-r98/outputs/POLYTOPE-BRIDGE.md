# 358320: routine source-construction consequence, zero-credit recommendation

Source 2305.05011 §2.2, Definitions 2.7–2.8 and Conjecture 2.1 were read, including theorem proofs. The actual claim is existence of a *good* positive epsilon (all n! points extreme), not mere existence of a convex hull, and not epsilon=1 for every n.

Put epsilon=1/n. Let P be any permutation matrix and expose with X -> <P,X>. A tour Q has transformed point (1+epsilon)Q; a non-tour has Q+epsilon J/n. Distinct permutations agree in at most n-2 positions. For a non-tour P, its own functional value is n+epsilon. Every other non-tour has value at most n-2+epsilon; every tour has value at most (n-2)(1+epsilon). The cross gap is 2-(n-3)/n=(n+3)/n>0. For a tour P its own value is n(1+epsilon); any other tour has gap at least 2(1+epsilon), and any non-tour has value at most n-2+epsilon. Thus every named point is uniquely exposed, and epsilon is good for every n>=4.

All ingredients are the source's printed Q_t/Q_nt definitions and the classical exposing-functional criterion. This is an immediate finite vertex stability/exposure argument, not a new significant campaign solution. No Lean packet or credit claimed. outputs/polytope.json enumerates the permutation/tour counts through n=8 and the exact symbolic gap; it is not a separate LP feasibility search or a formal certificate.
