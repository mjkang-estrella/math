# claude-projection-packing-full-r1: unresolved, zero nominations

Target: Deregowska–Lewandowska arXiv:2610.06141v1 Conjecture 1.1. For every nonzero real V ⊂ l_inf^N with
λ(V) < 4/3, d(V, l_inf^dim V) <= λ/(4−3λ). Primary and closest bodies were re-read from frozen copies
(hashes identical to r215). The source's quantitative Zippin/Bernau range is eps < 17^(-8) (bbox-verified).

Rigorous but non-credit pieces (details in discovery.md):
* **A.** A *fractional* column allocation (Σ_i w_ij <= 1, each agent row value >= 1−eps) already
  gives the distance bound. This is strictly weaker than the source's (11). LP dual: for every μ,
  Σ_j max_k μ_k|p_kj| >= 1−eps. Classical in spirit (Dor's lemma); no novelty claimed.
* **A′.** A λ-free geometric criterion: peak vectors with Σ_i (2|x^(i)_j|−1)_+ <= 1. It holds *exactly* on the
  source's Prop 3.2 obstruction space (where the integral geometric property fails), hence on every W_n.
* **B.** First-order rigidity: for non-degenerate cut perturbations of the cube, λ and d both equal
  1+ηc*+O(η²). So small-eps counterexamples would need clustered coordinate functionals.

Failed or refuted: two explicit allocation rules (numerically, c ≈ 37 and 1.07); extreme-point
stability, contraction induction and rank routes all stop at the same μ-weighted max bound.
Numerics (float, small dimensions, support only): 2-dim spaces with N <= 7 show d ≈ λ. The worst
fractional loss coefficient is ≈ 0.69 < 1, including with Auerbach-selected agents.

Missing lemma: Auerbach fractional packing (discovery.md §6), which is stronger than the source.
Bourgain 1982 was read from the free publisher scan: proportional subspaces only, so it neither covers nor
refutes the target. Zippin, Dor, GKL and Bernau bodies were not obtained, and the live registry was not
checked: these gaps remain. No Lean, manuscript, shared, git, count, MathDB, browser or external actions.
Counts remain 9/39, next 40.
