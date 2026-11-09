# Dormant formal plan, expanded-corpus-r533

NOT DISPATCHED. No Lean, compiler, checker or formal API was run in this lane. File name is the one TASK requires; the
Sol-only wording is historical. Every route needs specific imports only, since a whole-library import is not usable here.

## Route A, 347063 (Zeckendorf games): cheapest and most self-contained
Literal needed: inductive positions as finitely supported maps Nat -> Nat, the move relation, the two priority functions as
actual deterministic step functions, moves counted to the terminal position, source Definition 1.1 fidelity, starting at n
copies of F_1 (NOT the corpus wording, which root must adjudicate). Statement (a): exists C, for all n>=2,
|SS(n) - phi^2 n| <= C (log n)^2. Statement (b): exists C, for all n>=2, |CS(n) - c n| <= C sqrt(n) log n, c defined as a tsum.
Needed infrastructure, all elementary: uniqueness of Zeckendorf representation (Mathlib has Nat.zeckendorf), Fibonacci gcd and
Cassini, tsum convergence of 1/F_{2j} and its value bounds, the potential identity with psi in Real for (a).
Main cost is (b): Lemma R case analysis by strong descent on q with exact priority evaluation, Lemma C chip balance, the
endgame enumeration, and the assembly of a game trace over levels. Estimate: large but finite, comparable to the 382297 packet.
Part (a) alone is short. Reals and tsum are now feasible with specific imports.

## Route B, 352303 (biharmonic index of trees)
Literal needed: SimpleGraph tree on Fintype V, Laplacian as a real symmetric matrix, its eigenvalues via
Matrix.IsHermitian.eigenvalues with the zero eigenvalue removed, BH = n times the sum of inverse squares, path and star graphs on Fin n,
both equality clauses up to graph isomorphism.
Bridges: incidence factorization and rank n-1 for trees; nonzero spectra of BB^T and B^TB; trace of inverse square; the X = B M^{-1}
construction; inner products from cut sizes; the combinatorial N(T); the pendant-path decomposition, which needs a rooted-tree or
leaf-move data structure on arbitrary trees and an isomorphism invariance argument for the finite maximizer. The transformation is the
expensive part. The spectral bridge is moderate with Mathlib's Matrix and SimpleGraph.

## Route C, 381964 (curvature flow on K_{n+1}), cheap but author recommends exclusion
Literal needed: the flow vector field restricted to the non-lazy Markov manifold on Fin (n+1), its Frechet derivative at (J-I)/n, the
tangent space, and the characteristic polynomial or generalized eigenspaces with exact multiplicities, plus eigenvalues negative for
the stability clause as defined in the source. The source definition of F should be taken from equation (9) with the Q(x) Schur-complement
reduction to S_2 empty on K_{n+1}; the bridge from Definition 1.4 to (9) is the first paper's formula (66), not proved in the source read.

No route is proposed for dispatch by this lane. Root alone decides.
