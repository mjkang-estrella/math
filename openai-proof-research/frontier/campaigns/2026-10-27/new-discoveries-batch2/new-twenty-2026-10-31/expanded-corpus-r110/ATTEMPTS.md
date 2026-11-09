# Mathematical attempts and decisive gaps

## 340354: the classical parity collapse

Write q=2^n and extend inversion by inv(0)=0. For n at least 2, inv fixes precisely 0 and 1: x=x^{-1} for nonzero x implies x^2=1, hence x=1 in characteristic 2. Its remaining q-2 points form (q-2)/2=2^(n-1)-1 transpositions, an odd number. A nontrivial translation on the additive field has q/2 transpositions and therefore even sign for n at least 2. For n at least 3 every invertible linear transformation on F2^n has even sign: Gaussian elimination expresses it in elementary transvections and coordinate swaps; these each interchange 2^(n-2) pairs. Equivalently, coordinate swaps themselves are products of transvections. Frobenius is an invertible F2-linear transformation.

The source round x -> (x+b)^(-2^k) factors as translation, inversion and a Frobenius power, hence is odd for n at least 3. When n is even and at least 4, the n-round composition is even. A single cycle on q points is odd. Thus the composition cannot be a single cycle. For n=2, the only irreducible quadratic and all four b were checked directly; no full cycle. One can also use that Frobenius is inversion in F4: the two rounds compose to x -> x^2+b+b^2, whose square is the identity. This is a routine application of classical permutation parity. No claim of mathematical significance or novelty, and no Lean credit.

## 339514: exact diagnostic scope

A placement word has one symbol L,R,C for each of a pairs and b singletons. Pair column choices are {left,center}, {center,right}, {left,right}; singleton choices are left,right,center. The path is recovered from total column heights. Labels are assigned upwards in each column; pair labels use decreasing ranks. Input pides is checked directly from consecutive ranks. The image uses the reversed placement word with the pair/singleton block sizes swapped. The image need not have the desired pides except under the conjecture's fixed-point hypothesis. Filtering it anyway caused the initial false failures, which the corrected script removes.

The correction term is evaluated from the actual English Ferrers diagram, using the source's arm/leg inequalities and its 0/0=0 convention. Coprime ranks use 3y-nx. This is a concrete search beyond ten rows but still has two semantic limitations: the source prints a conflicting output pair inequality, and Phi is not implemented. The diagnostic cannot establish part (b) or the unrestricted part (a).

A potential proof route is a pairwise placement interaction identity for tdinv together with a column-height formula for dinvcorr. Such an identity must also handle the noncoprime rank perturbation. No identity covering that scope was proved here.

## 358215: why the numerical optimum is not a proof

Fix any orientation of the 15 Petersen edges and its 10 by 15 incidence matrix B. Rank(B)=9, so the flow space in one coordinate has dimension 6. Every two-dimensional flow is represented by a 6 by 2 matrix of coefficients in a numerical nullspace basis. For every edge e, constrain squared norm at least 1 and at most t, and minimize t. The conjectured value corresponds to t=7/3 after scaling. The search uses analytic constraint gradients and 100 starts, returning that value repeatedly, as well as worse local optima. Kirchhoff residual and best vectors are saved in outputs/flow-best.json.

A complete lower bound needs a global argument on all feasible coefficient matrices, not merely the successful local optimizations. The source gives the matching upper bound explicitly. Applying its chordless-cycle lower bound only gives the relevant wheel bound; it does not give sqrt(7/3). No rational witness beating the conjecture was found, and no exact global nonexistence certificate was generated.

## 375504: source proof supersedes the finite lead

The original v1 conjectures containment in the span of outer products of indicators of intersections of receiver-side components. The current Theorem 2 gives H as a positive combination of height-component indicators, with coefficient kappa(a,Omega) equal to the reciprocal sum of beta^(a-h(v)) over v in Omega, plus a constant-component term. Its proof groups spacetime storage balances by height component, obtains a weighted Cauchy–Schwarz lower bound, constructs all attaining transport variables from zero-sum incidence equations, verifies the Bellman/DARE identity, establishes stability by leaf elimination, and proves that each height component is an intersection of receiver-side components. The last step is exactly the required V_L bridge. This is a source-owned complete answer, not a new corollary candidate.

## Other finite versus infinite distinctions

The loopy-cycle tie and torsion denominator discrepancy are already printed in their own sources. Small cages do not refute a sufficiently-large-girth statement. Finite Ulam tails do not prove that even-coordinate elements terminate. Four Möbius values cannot establish an asymptotic exponential law. A coloring of a finite tropical-distance graph supplies neither a global coloring nor a lower bound of 2^n in every dimension. Finite modular point counts do not certify an all-prime modular correspondence. These distinctions are preserved in results.json instead of reporting artificial counterexamples.
