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

