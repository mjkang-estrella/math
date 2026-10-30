# Odd primitive weight totals require at least m simple SOC constraints

Status: prospective source-question resolution; credit **0**. Mathematical argument and full literal Lean endpoint complete. Fresh strict replay PASS: 41 declarations, seven modules, standard-3 axiom subset only. Independent review and final packet acceptance pending. No priority claim.

## Exact target and exclusions

Jie Wang, *Weighted Geometric Mean, Minimum Mediated Set, and Optimal Simple Second-Order Cone Representation*, SIAM J. Optim. **34** (2024), 1490–1514, DOI 10.1137/22M1531257, Section 7, open problem (2), p. 1512 asks whether primitive positive weights with odd sum satisfy `L(s_1,...,s_m) >= m`. Definition 3.1, p. 1493 permits arbitrary input indices, including cycles and repeated indices. We do not add acyclicity, distinctness, or irredundancy assumptions.

The original MathDB 349081 cardinality conjecture was already resolved in this paper's Corollary 4.5. It receives **no credit**. Theorem 3.6's lower bound `L >= m-1` is also old. The prospective new result is the strictly stronger odd-total bound explicitly asked in Section 7.

## Theorem

Let `m >= 2`, let `s_j` be positive integers with gcd 1, and write `S = sum_j s_j`. If `S` is odd, every simple SOC representation in Definition 3.1 has at least `m` constraints. In fact the proof only uses positivity and oddness, not gcd 1.

The last sentence needs care: a nonprimitive odd vector still has odd primitive total, so it is consistent. An even rescaling does not satisfy the hypothesis and is not addressed.

## 1. Reachability and the equality case of the counting bound

For a representation with `n >= 1` constraints, let `I` be its `n` internal vertices (the output and `n-1` auxiliaries), `T` its `m` terminal vertices (the original variables), and `r` the output. Each internal vertex has two ordered child slots, one for each input of its constraint. They may initially repeat or point back to the same internal vertex.

Every terminal is reachable from `r`. Otherwise set every reachable variable equal to 1 and every unreachable variable equal to 0. Every reachable constraint has both inputs 1 and right side 1. Every unreachable constraint has right side 0 and nonnegative left side. All constraints hold, the output is 1, and a positive-weight terminal is 0, contradicting soundness of the representation.

Let `R` be the number of reachable internal vertices. There are `m+R` reachable vertices altogether. Every one except `r` is hit by a child slot of a reachable internal vertex. Hence

`m + R - 1 <= 2R`, so `m-1 <= R <= n`.

This also reproves the old size bound. Suppose `n=m-1`. Then `R=n`, all vertices are reachable, and the augmented map from the `2n` child slots plus one extra slot for `r` onto all `m+n=2n+1` vertices is a bijection. Consequently:

* every nonroot vertex occurs as an input exactly once;
* the root never occurs as an input;
* the child-slot map is injective.

These conclusions are proved from soundness and size, not imposed as restrictions.

## 2. Linear equations and balance flows

Let `A` be the internal adjacency matrix, with `A_ij` the number of child slots of internal vertex `i` equal to internal vertex `j`. Let `B_ij` count its terminal children. Set `M=2I-A`.

Every column of `A` has sum at most 1. Thus `M` is invertible. For example, `M^T z=0` gives `2 z_j` equal either to 0 or to one entry `z_i`; taking a maximum absolute entry forces `z=0`. This argument also covers self-loops.

For arbitrary terminal logarithms `u in R^m`, set `z=M^{-1} B u`. The positive values `exp(u_j)` at terminals and `exp(z_i)` at internal vertices satisfy every quadratic constraint with equality. Soundness therefore gives

`S z_r <= sum_j s_j u_j`.

Replacing `u` by `-u` gives the opposite inequality, so equality holds for every `u`. Equivalently, with the row vector `t^T = S e_r^T M^{-1}`,

`t^T B = s^T`, and `t^T M = S e_r^T`.

The unique-input conclusions now identify these equations term by term:

* if a child of `i` is terminal `j`, then `t_i=s_j`, an integer;
* if a child of `i` is internal `j`, then `t_i=2t_j` (the root cannot be a child);
* `2t_r=S`.

No flow positivity assumption is needed.

## 3. A finite doubling obstruction forces integrality

Let `D={i in I : t_i is not an integer}`. A child of a vertex in `D` cannot be terminal, since terminal-child balance says its parent flow is the integer `s_j`. If it is an internal vertex `j`, then `t_i=2t_j` implies `j in D`: an integral `t_j` would make `t_i` integral.

Thus the two child slots of every vertex in `D` give an injective map `D x {0,1} -> D`, because the global child-slot map is injective. Finiteness yields `2|D| <= |D|`, hence `D` is empty. In particular `t_r` is an integer, and `S=2t_r` is even.

This contradicts oddness. Equality `n=m-1` is impossible; together with the lower bound, `n>=m`.

## Formal scope

`formal/FlowParity.lean` proves the integrality obstruction and even-total consequence without assuming an acyclic graph or positive flows. `formal/CircuitReach.lean` defines literal nonnegative-real constraint semantics and derives terminal reachability from soundness. `CircuitCount` derives the old lower bound and all equality-case input properties. `FlowExistence` constructs balance flows by a proved invertibility argument. `LogSemantics` derives the exact logarithmic equality from literal soundness at exponential assignments of both signs. `PotentialMatrix` proves the transpose/constraint bridges and existence of every terminal potential. `SourceParity` derives the terminal weights and evenness, then proves the full odd-total size bound for the literal existential `SourceRepresentation`. The endpoint `WGMParity.source_odd_total_bound` has only positive integer weights, a representation, and odd total as premises; no residual graph, linear-algebra, or flow hypotheses.

The successful fresh replay's complete 41 declaration types and axiom reports were read by the parent. Standard axioms only; no proof holes, added axioms, unsafe evaluation or native decision procedure. Exact small-configuration validation independently enumerates all 22,183 unordered input configurations for m=2,3,4 and n=m-1, including repetitions/self-loops/cycles initially. Only 1,3,30 configurations respectively reach every terminal, and every primitive total is even. This finite enumeration is uncredited supporting validation.

## Bounded novelty work so far

The actual published primary PDF was read at Definitions 3.1, Theorem 3.6, Corollary 4.5, and Section 7(2); rendered pages 1498, 1499, 1512 were viewed. Its SHA-256 is `088c131e9b3d55a366ec3010d48dd0431700f0cf85411907fdfe2c3774357fd6`.

OpenAlex and Semantic Scholar independently return the same three citing papers. The full 2024 Blanco–Martínez-Antón preprint and the full 2026 *Extremal Mediated Graphs* published body have been retrieved and the relevant structural/lower-bound sections read. Neither section supplies the parity result. The third citing article (Alzalg, 2026) has an accessible abstract about algebraic structures, but the full body has not yet been retrieved; this remains a recorded access limit. Author's current research page and targeted searches found no explicit resolution. This is an incomplete screen, not a novelty certification.

Primary and relevant successor source files and citation records are copied into `sources/` with hashes in `provenance.json`. No MathDB post specifically encoding Section 7(2) has yet been identified; attempted listing parameters `search` and `q` were ignored by the server and do not constitute a MathDB search.
