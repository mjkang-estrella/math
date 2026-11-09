# Lean formalization plan: MathDB 353203 (PD-TAR uniqueness for K_{s,t})

Nothing here has been compiled: this lane may not run Lean, lake or leanchecker. The draft sources in `lean-draft/PDTAR/{Defs,Core}.lean` are statement skeletons with `sorry`. Mathlib API names in them are best guesses and must be checked against the pinned toolchain.

## 1. Literal endpoint

```lean
theorem mathdb_353203 (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    TARUnique (completeBipartiteGraph (Fin s) (Fin t)) ↔ (s ≠ 2 ∧ t ≠ 2)
```

`TARUnique G` is defined verbatim from the source (§3.3):

> ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W), NoIsolated H → Nonempty (tar H ≃g tar G) → Nonempty (H ≃g G).

The definitions it relies on:

- **`IsPD`.** Use the source's literal round process: `obs G S 0 = S`, `obs 1 = N[S]`, `obs (i+2) = step (obs (i+1))`, and `IsPD G S := ∃ i, obs G S i = univ`. Do not define PD through forts; fort duality is a proved lemma (Lemma 0).
- **`tar G`.** A `SimpleGraph` on the subtype `{S : Finset V // IsPD G S}`, with `Adj S T := (symmDiff S T).card = 1`.
- **K_{s,t}.** Mathlib's `completeBipartiteGraph (Fin s) (Fin t)` on `Fin s ⊕ Fin t`.

Fidelity notes for the reviewer:

1. **Universe.** `W : Type` (universe 0) is enough: every finite graph is isomorphic to one on `Fin n`. One may state it with `W := Fin n` for all `n`, equivalently.
2. **Range.** s and t are positive. For s = 0 the graph has isolated vertices and lies outside the source's definition.
3. **Scope.** The conjecture is an "iff". A credited result would most naturally be the full iff; the new mathematics is the direction "s, t ≥ 3, (s,t) ≠ (3,3) ⇒ unique". Root decides whether a narrower endpoint suffices.

## 2. Module structure and size estimates

Sizes are rough Lean line counts, assuming Mathlib's `Finset` and `SimpleGraph` API.

| Module | Content | Finite or general | Est. size |
|---|---|---|---|
| `Defs` | `cnbhd`, `step`, `obs`, `IsPD`, `IsFort`, `tar`, `NoIsolated`, `TARUnique` | general | 80 |
| `Basic` | monotonicity of `obs` in S and i; stabilisation by round `card V + 1`; up-closure of PD | general | 150–250 |
| `FortDuality` | Lemma 0: `IsPD G S ↔ ∀ F, IsFort G F → (F ∩ N[S]).Nonempty`; fort facts F1–F3 | general | 200–300 |
| `KstFamily` | facts K1–K3 about K_{A,B} (PD of {a,b}, A\{x}; non-PD of A\{x,y} via the fort {x,y}) | general in s, t | 100–150 |
| `Core` | Lemmas 1–7 and the Core Theorem on `V` with `A B : Finset V` | general in s, t | 400–600 |
| `Reduction` | Theorem R for power domination (see §3) | general | 800–1500 |
| `SmallCases` | K₂ unique; K_{1,t} (t ≥ 3) unique; K_{2,t} and K_{1,2} not unique; K_{3,3} unique | mixed | 300–600 |
| `Endpoint` | assembly, transport along `Fin s ⊕ Fin t ≃` the partition | general | 100–200 |

**Total:** about 2,100–3,600 lines. The new mathematics (`Core`) is the smaller part. The dominant cost is the published reduction.

**Finite versus general.**

- Everything above is general: it is quantified over all s and t, or over all graphs.
- Only K₂, K_{1,2}/K₃ and K_{3,3} are concrete finite objects.
- Do not use `native_decide`. A kernel `decide` over all graphs on 6 vertices (2^15 graphs, each needing PD-family computations) is likely too slow.
- So prove K_{3,3} by the source's argument (Prop. `p:K33`: degrees, 3-regularity, bipartiteness), or by an extension of Lemmas 1–5. At (3,3), Lemma 5's structure forces the relabelled K_{3,3}. The remaining sub-case, with every cross-degree ≥ 2, still needs the source's argument.

## 3. The reduction (Theorem R)

Bong–Carlson–Curtis–Haas–Hogben, Graphs Combin. 39 (2023) no. 86, Thm 1.1 = survey Thm t:main. Only its power-domination instance is needed, where both graphs have no isolated vertices. The proof chain, with the survey's labels:

1. **`x-deg`.** Δ(tar G) = |V(G)|; the degree of S is at most n, with equality at V. This uses "every (n−1)-set is PD when there are no isolated vertices". For PD this is easy: V \ {v} dominates, since v has a neighbour.
2. **`c:X-Qt`.** The largest induced hypercube has dimension n − pd(G).
3. **`p:umindegreeTAR`.** δ(tar G) = n − upper-pd(G).
4. **`interval` (Lemma 2.1 of Bong et al.).** An induced Q_t in tar G is an interval [S, T] of the subset poset. This is **the riskiest lemma**: a combinatorial path-exchange argument using "each pair of hypercube vertices has 0 or 2 common neighbours". It needs Mathlib's hypercube / `SimpleGraph.boxProd` API, or a direct definition of "induced Q_t".
5. **`lem:ord_pres`** and **`t:irrel-isom`.** Minimal PD sets lie below φ(V). ν_R is an automorphism exactly when R is irrelevant.
6. **`isomorph-isometry-u`.** After composing with ν_{R′}, φ(V) = V and |φ(S)| = |S|. This is an induction on |S| over intervals [S, V].
7. **`isomorph-same-zfs`.** A size-preserving TAR isomorphism is induced by a vertex bijection ψ. It is built from the (n−1)-sets and then propagated downward by φ(S) = φ(S∪a) ∩ φ(S∪b).

### Possible shortcut for the special case

Because the PD family of K_{s,t} is explicit, one might avoid parts of steps 4–6. For example, one could identify V(K) inside tar K as the unique vertex of degree n whose neighbourhood consists of vertices of degree n − 1 + …, and then check the grading directly.

This still needs that φ preserves the rank function, and that is exactly steps 5–6. A general formalization of Theorem R (for PD only) is the safer plan. It is reusable for other MathDB TAR problems, and all of its steps are elementary.

## 4. Risky lemmas (ordered)

1. **Hypercube-interval lemma** (step 4 of §3). It is non-trivial path combinatorics, and the "0 or 2 common neighbours" property of Q_t must be proved.
2. **Rank preservation by induction** (steps 6–7). Careful bookkeeping with subtypes `{S // IsPD G S}` and `Finset.map` along `≃`.
3. **Fort duality with the simultaneous-round definition** (Lemma 0). Take the minimal round in which a fort vertex is observed, using `Nat.find`. Also prove that `obs` stabilises, for the ⇐ direction.
4. **A/B mirror symmetry.** State all Core lemmas for an arbitrary partition `A B : Finset V`, so that the mirror is just `(B, A)`. The fact that the K-family is symmetric is the definitional `KAB A B = KAB B A`.
5. **Transport** from `Fin s ⊕ Fin t` to the partition form, and composing the relabelling ψ from Theorem R into a `SimpleGraph.Iso`.
6. **K_{3,3}** (source argument): a 6-vertex case analysis. It is moderate, but needs care to avoid `decide` blow-up.

## 5. Axiom budget

Target `#print axioms mathdb_353203` ⊆ {propext, Classical.choice, Quot.sound}. No `native_decide`, `sorry` or `axiom`. Decidability instances (`DecidableRel G.Adj`, the `Finset.filter` predicates) can be classical.
