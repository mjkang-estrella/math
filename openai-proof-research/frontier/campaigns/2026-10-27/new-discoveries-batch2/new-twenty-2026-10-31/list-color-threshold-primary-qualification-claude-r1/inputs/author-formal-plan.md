# DORMANT formal plan, MathDB 353552 (NO dispatch; no Lean was run in this lane)

Prepared for a possible later formal lane if root decides to route this candidate. This is a plan only.
Uses specific imports only: a whole-library `import Mathlib` is excluded by the address-space and real-memory limits.

## Literal endpoint

Definitions, over colour type Nat and vertex type Fin 2 + Fin l for K_{2,l}:
- `IsProperListColoring L f`: f v is in L v for all v, and f (inl i) differs from f (inr j) for all adjacent pairs.
  To reduce fidelity risk, state it for the actual `SimpleGraph` completeBipartiteGraph (Fin 2) (Fin l), and prove the adjacency bridge.
- `countL G L`: number of proper L-colourings, as a Fintype card over a finite Pi type of list choices.
- `P G m`: count for the constant assignment Finset.range m. Prove the formula m(m-1)^l + m(m-1)(m-2)^l for K_{2,l}, as a bridge from the actual count, not as a definition.
- `P_l G m` = sInf of `countL G L` over m-assignments L (a set of naturals, so sInf is attained when nonempty).
- `tau G` = sInf { k | chi(G) <= k and for all m >= k, P_l G m = P G m }. Use `G.chromaticNumber` or prove chi(K_{2,l}) = 2 for l >= 1 as a bridge. Show nonemptiness from Theorem 1.

Target theorem: exists c C > 0 and l0, for all l >= l0, c * sqrt l <= tau (K_{2,l}) and tau (K_{2,l}) <= C * sqrt l.
Only propext, Classical.choice, Quot.sound; no sorry, added axioms, unsafe or native_decide.

## Modules

1. `Count`: N(L) = sum over a in A, b in B, of prod_i card (L_i \ {a,b}). Finset/Pi bookkeeping; the only combinatorial bridge. Cost medium.
2. `Reduce`: lists inside U (replacement monotonicity, induction on the number of outside colours); p = 0.
3. `Weights`: over reals, for m >= 3: the exact factorization (E1), (E2) with s_x and c_ab. Prove by Finset.prod over i with a three-case split.
4. `CaseOne`: p = 1. Two Bernoulli inequalities, both from `one_add_mul_le_pow` (natural exponents; for (1-a)^v >= 1 - av apply it at -a, which is >= -2).
5. `CaseTwo`: p >= 2. AM-GM twice over Finsets (`Real.geom_mean_le_arith_mean_weighted` with uniform weights), then the joint-miss bound F <= n/4 by a_i b_i <= (p-e_i)^2/4, sum over i.
   Real exponents appear as q^(n) with n = l - v/p: use `Real.rpow`. To avoid analysis-heavy steps, note the only needed real-exponent facts are monotonicity, `Real.one_add_mul_self_le_rpow_one_add`-type Bernoulli and the bound H >= 0.
6. `HBound`: H >= 0 under a <= 1/3, a^2 l <= 1/2. Uses ln bounds or, better, exp/log-free versions: (1-x) q^t <= exp(a^2 t) needs `Real.add_one_le_exp` and `Real.log_le_sub_one_of_pos`. Elementary but the fiddliest module.
7. `Upper`: Theorem 1, the tau upper bound and ceiling arithmetic.
8. `Lower`: the lower bound for the literal Theta. Source Theorem 4 must be reproved, not assumed. Simplest route: for the source's balanced assignment on l lists (z_ij within 1 of l/4), compute N exactly and show N < P for (m-1)^2 <= c l with a crude constant; no sharp constant needed. The exact formula for l = 4t is source Lemma 9; general l needs the balanced z_ij or the source's Lemma 10 induction. Cost medium.
9. `Literal`: assemble Theta, sqrt arithmetic, bridges, axiom audit, controls (for example the constant assignment reaches equality; a wrong constant in the threshold is rejected by a negative control).

Theorem 3 (exact constant) is optional and needs limit arguments in `Lower` and `HBound`; the literal does not need it.

Feasibility: all exact finite combinatorics plus elementary real analysis. No machinery missing from mathlib. Expected import footprint: Finset big operators, Mathlib.Analysis.MeanInequalities, Mathlib.Analysis.SpecialFunctions.Log.Basic, Mathlib.Analysis.SpecialFunctions.Pow.Real, Mathlib.Combinatorics.SimpleGraph basics. Main risks: Pi-type bookkeeping in `Count`, real-exponent friction in `CaseTwo`, and the lower-bound general-l arithmetic.
