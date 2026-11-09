# Statement correspondence plan: MathDB 347138 (Bang-Jensen–Bessy–Yeo Conjecture 35)

The Lean draft is UNCOMPILED (Claude lane restriction: no Lean). Root or a Sol worker must compile it, remove every `sorry`, and run the strict replay.

| Source notion | Lean definition (`lean/NonSepBranching.lean`) | Fidelity notes |
|---|---|---|
| digraph D = (V, A), finite, no loops, no parallel arcs | `V : Type`, `[Fintype V]`, `E : V → V → Prop`, hypothesis `∀ v, ¬ E v v` | A Prop relation makes parallel arcs impossible. 2-cycles are allowed, as in the source. Quantifying over every finite type V covers "every digraph". |
| D on at least L vertices | `L ≤ Fintype.card V` | |
| strongly connected | `Strong E := ∀ u v, Relation.ReflTransGen E u v` | |
| D \ A' (arc deletion) | `del E F u v := E u v ∧ ¬ F u v` | |
| λ(D) ≥ 2 | `TwoArcStrong E := Strong E ∧ ∀ a b, E a b → Strong (del E (fun u v => u = a ∧ v = b))` | λ(D) ≥ k means D − X is strong for every arc set with \|X\| < k (Bang-Jensen–Gutin). For k = 2 this is exactly the definition. |
| α(D) = 2 | `IndepTwo E := (∃ u v, u ≠ v ∧ ¬Adj E u v) ∧ ∀ u v w, u≠v → v≠w → u≠w → Adj E u v ∨ Adj E v w ∨ Adj E u w`, where `Adj E u v := E u v ∨ E v u` | α = max size of a set of pairwise non-adjacent vertices; a non-adjacent pair exists and no independent triple, so α = 2. |
| out-branching B_s^+ | `OutBranching E s F`: `F ⊆ E`; `∀ u, ¬ F u s`; `∀ v ≠ s, ∃! u, F u v`; `∀ v, ReflTransGen F s v` | The source says "every vertex except s has exactly one entering arc, and s reaches every vertex". The root's in-arc condition is implied by acyclicity and is stated explicitly, which only makes the conjecture easier to satisfy, so the refutation is not weakened. Our proof never uses `root`. |
| non-separating | `NonSeparating E F := Strong (del E F)` | |
| Conjecture 35 | `Conjecture35 : Prop := ∃ L : ℕ, ∀ (V : Type) [Fintype V] (E : V → V → Prop), L ≤ Fintype.card V → (∀ v, ¬E v v) → TwoArcStrong E → IndepTwo E → ∀ s, ∃ F, OutBranching E s F ∧ NonSeparating E F` | Endpoint: `theorem not_conjecture35 : ¬ Conjecture35`. |

Remark on decidability: the conjecture quantifies over Prop relations without decidability, which matches the literal statement. The counterexample relation is decidable.

## Proof architecture (lemmas in the draft)

1. `Dm k`: vertex type `Fin (k+3) ⊕ Fin 4`, so m = k + 3 ≥ 3. The relation is given by four cases (A-A: i ≠ j; B-B: W1 table; A-B: the two entries; B-A: the two exits).
2. `card_Dm`: the card is k + 7, so k := L gives at least L vertices.
3. `irrefl_Dm`: no loops.
4. `indepTwo_Dm`: pigeonhole on sides; W1 is semicomplete (`decide`); the non-adjacent pair is (inl 0, inr 1).
5. `twoArcStrong_Dm`: needs strong connectivity after deleting any single arc. Plan:
   - (a) A is strongly connected after any single deletion, using a third vertex.
   - (b) Lift a finite check on the contracted digraph Q on `Fin 5` (vertex 4 = A; exits as two parallel 2→4 arcs). Deleting one W1 arc, entry or exit leaves Q strong; this is a `decide` with a Bool reachability.
   - Alternative: the cut criterion; Lemma 2 of PROOF.md lists all cuts.
   - This is the longest part.
6. Generic crossing lemmas (`last_cross`, `first_cross`) for `ReflTransGen` and a side predicate.
7. Main gluing: Steps 1–3 of PROOF.md, producing T := F restricted to B, with `∀ q, RTG T e q`; R_B := W1 − T, with `∀ q, RTG R_B e' q` and `∀ q, RTG R_B q p3`.
8. Finite lemma `w1_finite`: for every `S : Finset (Fin 4 × Fin 4)` with `S ⊆ W1arcs`, if e reaches all in S then the conditions fail in `W1arcs \ S`, for both e = 0 and e = 2.
   - This is a `decide` over 2^7 subsets with a Bool reachability.
   - Bridge from the Prop relation T: `S := W1arcs.filter (fun a => T a.1 a.2)` (classical), plus `ReflTransGen ↔ boolReach`.
9. `not_conjecture35`: given L, use k = L and s = inl 0.

Axioms expected: propext, Classical.choice, Quot.sound only (classical filter). Use plain `decide`, not `native_decide`.
