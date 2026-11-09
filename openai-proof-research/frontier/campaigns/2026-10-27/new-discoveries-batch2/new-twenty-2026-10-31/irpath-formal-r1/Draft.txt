/-
  UNCOMPILED DRAFT (Claude lane expanded-corpus-r209; this lane may not run Lean).
  Root / a Sol worker must compile, repair and audit it.

  Target: MathDB 350452 (Mynhardt–Roux, "Irredundance Graphs", arXiv:1812.03382 Conjecture 1/2,
  restated in Mynhardt–Roux arXiv:2104.09004 §"Open Problems" Conjecture 1):
    (i) the path P_n is not an IR-graph for each n ≥ 3, and
    (ii) the cycle C_n is not an IR-graph for each n ≥ 5.
  We prove the negation of the conjunction by exhibiting a 9-vertex graph G9 whose IR-graph is
  isomorphic to the path P_9.

  Definitions follow the source literally (arXiv:1812.03382v3 §1.1 and §2):
  * w is a D-private neighbour of v ∈ D iff w ∈ N[v] and w ∉ N[u] for every u ∈ D \ {v};
  * D is irredundant iff every v ∈ D has a D-private neighbour;
  * an IR(G)-set is an irredundant set of maximum cardinality;
  * the IR-graph has the IR(G)-sets as vertices, and D ~ D' iff there are u ∈ D, v ∈ D'
    with uv ∈ E(G) and D' = (D \ {u}) ∪ {v};
  * a graph H is an IR-graph iff H ≅ G(IR) for some (finite simple) graph G.

  Allowed axioms after compilation: propext, Classical.choice, Quot.sound.
  No sorry / admit / native_decide. Kernel `decide` on the finite checks is intended.
-/
import Mathlib

open Finset

namespace IRGraphPath

section General

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `w` is a `D`-private neighbour of `v`. -/
def IsPrivateNbr (G : SimpleGraph V) (D : Finset V) (v w : V) : Prop :=
  (w = v ∨ G.Adj v w) ∧ ∀ u ∈ D, u ≠ v → ¬ (w = u ∨ G.Adj u w)

/-- `D` is irredundant: every vertex of `D` has a `D`-private neighbour. -/
def Irredundant (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v ∈ D, ∃ w, IsPrivateNbr G D v w

/-- An `IR(G)`-set: an irredundant set of maximum cardinality. -/
def IsIRSet (G : SimpleGraph V) (D : Finset V) : Prop :=
  Irredundant G D ∧ ∀ D' : Finset V, Irredundant G D' → D'.card ≤ D.card

/-- The swap relation `D ~ D'`: `D' = (D \ {u}) ∪ {v}` with `u ∈ D`, `v ∈ D'`, `uv ∈ E(G)`. -/
def Swap (G : SimpleGraph V) (A B : Finset V) : Prop :=
  ∃ u ∈ A, ∃ v ∈ B, G.Adj u v ∧ B = insert v (A.erase u)

lemma IsIRSet.card_eq {G : SimpleGraph V} {A B : Finset V}
    (hA : IsIRSet G A) (hB : IsIRSet G B) : A.card = B.card :=
  le_antisymm (hB.2 A hA.1) (hA.2 B hB.1)

/-- On sets of equal cardinality the swap relation is symmetric. -/
lemma swap_symm {G : SimpleGraph V} {A B : Finset V} (hc : A.card = B.card)
    (h : Swap G A B) : Swap G B A := by
  obtain ⟨u, hu, v, -, huv, rfl⟩ := h
  have hvA : v ∉ A.erase u := by
    intro hv'
    have h1 : (insert v (A.erase u)).card = (A.erase u).card := Finset.card_insert_of_mem hv'
    have h2 : (A.erase u).card = A.card - 1 := Finset.card_erase_of_mem hu
    have h3 : 0 < A.card := Finset.card_pos.mpr ⟨u, hu⟩
    omega
  refine ⟨v, Finset.mem_insert_self _ _, u, hu, huv.symm, ?_⟩
  rw [Finset.erase_insert hvA, Finset.insert_erase hu]

/-- The swap relation is irreflexive. -/
lemma swap_irrefl {G : SimpleGraph V} (A : Finset V) : ¬ Swap G A A := by
  rintro ⟨u, hu, v, -, huv, hA⟩
  have hne : u ≠ v := G.ne_of_adj huv
  have : u ∈ insert v (A.erase u) := hA ▸ hu
  rcases Finset.mem_insert.mp this with h | h
  · exact hne h
  · exact (Finset.not_mem_erase u A) h

/-- The IR-graph `G(IR)` of `G`, with adjacency exactly the source's swap relation. -/
def IRGraph (G : SimpleGraph V) : SimpleGraph {D : Finset V // IsIRSet G D} where
  Adj A B := Swap G A.1 B.1
  symm := fun A B h => swap_symm (IsIRSet.card_eq A.2 B.2) h
  loopless := fun A h => swap_irrefl A.1 h

/-- Irredundance is hereditary. -/
lemma Irredundant.mono {G : SimpleGraph V} {D D' : Finset V} (h : Irredundant G D)
    (hsub : D' ⊆ D) : Irredundant G D' := by
  intro v hv
  obtain ⟨w, hw1, hw2⟩ := h v (hsub hv)
  exact ⟨w, hw1, fun u hu huv => hw2 u (hsub hu) huv⟩

end General

/-- `H` is an IR-graph: it is isomorphic to the IR-graph of some finite simple graph. -/
def IsIRGraph {W : Type} (H : SimpleGraph W) : Prop :=
  ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
    Nonempty (IRGraph G ≃g H)

/-! ### The 9-vertex counterexample

`G9` is the complete tripartite graph `K_{3,3,3}` on the parts `{0,1,2}`, `{3,4,5}`, `{6,7,8}`
with the seven edges `05, 08, 14, 23, 26, 37, 56` deleted (20 edges). -/

/-- Edge list of `G9` (each edge once, smaller endpoint first). -/
def edges9 : List (ℕ × ℕ) :=
  [(0,3),(0,4),(0,6),(0,7),(1,3),(1,5),(1,6),(1,7),(1,8),(2,4),
   (2,5),(2,7),(2,8),(3,6),(3,8),(4,6),(4,7),(4,8),(5,7),(5,8)]

def adj9 (a b : Fin 9) : Bool :=
  decide ((a.val, b.val) ∈ edges9) || decide ((b.val, a.val) ∈ edges9)

def G9 : SimpleGraph (Fin 9) where
  Adj a b := adj9 a b = true
  symm := by
    intro a b h
    revert a b
    decide
  loopless := by
    intro a
    revert a
    decide

instance : DecidableRel G9.Adj := fun a b => inferInstanceAs (Decidable (adj9 a b = true))

instance (D : Finset (Fin 9)) : Decidable (Irredundant G9 D) := by
  unfold Irredundant IsPrivateNbr; infer_instance

instance (A B : Finset (Fin 9)) : Decidable (Swap G9 A B) := by
  unfold Swap; infer_instance

/-- The nine IR-sets, listed in path order. -/
def walk : Fin 9 → Finset (Fin 9)
  | 0 => {0, 1, 2} | 1 => {0, 2, 7} | 2 => {0, 4, 7} | 3 => {4, 6, 7} | 4 => {6, 7, 8}
  | 5 => {1, 6, 8} | 6 => {1, 3, 8} | 7 => {3, 5, 8} | 8 => {3, 4, 5}

/-- Finite check (a): no 4-subset of `Fin 9` is irredundant in `G9` (126 subsets). -/
lemma no_irredundant_four :
    ∀ D ∈ (Finset.univ : Finset (Fin 9)).powersetCard 4, ¬ Irredundant G9 D := by
  decide

/-- Finite check (b): the irredundant 3-subsets are exactly the nine sets of `walk` (84 subsets). -/
lemma irredundant_three_iff :
    ∀ D ∈ (Finset.univ : Finset (Fin 9)).powersetCard 3,
      (Irredundant G9 D ↔ ∃ i : Fin 9, walk i = D) := by
  decide

lemma walk_card (i : Fin 9) : (walk i).card = 3 := by
  revert i; decide

lemma walk_injective : Function.Injective walk := by
  intro i j h
  revert i j
  decide

/-- Every irredundant set of `G9` has at most three vertices. -/
lemma irredundant_card_le {D : Finset (Fin 9)} (h : Irredundant G9 D) : D.card ≤ 3 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨D', hD'sub, hD'card⟩ := Finset.exists_subset_card_eq (show 4 ≤ D.card by omega)
  -- (in older Mathlib: `Finset.exists_smaller_set D 4 _`)
  exact no_irredundant_four D'
    (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hD'card⟩) (h.mono hD'sub)

lemma walk_irredundant (i : Fin 9) : Irredundant G9 (walk i) :=
  (irredundant_three_iff (walk i)
    (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, walk_card i⟩)).mpr ⟨i, rfl⟩

lemma isIRSet_iff (D : Finset (Fin 9)) : IsIRSet G9 D ↔ ∃ i : Fin 9, walk i = D := by
  constructor
  · rintro ⟨hirr, hmax⟩
    have hge : 3 ≤ D.card := by
      have := hmax (walk 0) (walk_irredundant 0)
      rwa [walk_card] at this
    have hcard : D.card = 3 := le_antisymm (irredundant_card_le hirr) hge
    exact (irredundant_three_iff D
      (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩)).mp hirr
  · rintro ⟨i, rfl⟩
    refine ⟨walk_irredundant i, fun D' hD' => ?_⟩
    rw [walk_card]
    exact irredundant_card_le hD'

/-- Finite check (c): swap-adjacency between the listed IR-sets is exactly path adjacency. -/
lemma swap_walk_iff :
    ∀ i j : Fin 9, Swap G9 (walk i) (walk j) ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  decide

/-- The vertex map `Fin 9 → G9(IR)`. -/
def toIR (i : Fin 9) : {D : Finset (Fin 9) // IsIRSet G9 D} :=
  ⟨walk i, (isIRSet_iff _).mpr ⟨i, rfl⟩⟩

lemma toIR_bijective : Function.Bijective toIR := by
  constructor
  · intro i j h
    exact walk_injective (congrArg Subtype.val h)
  · rintro ⟨D, hD⟩
    obtain ⟨i, rfl⟩ := (isIRSet_iff D).mp hD
    exact ⟨i, rfl⟩

/-- `P_9 ≃g G9(IR)`. -/
def pathIso : SimpleGraph.pathGraph 9 ≃g IRGraph G9 where
  toEquiv := Equiv.ofBijective toIR toIR_bijective
  map_rel_iff' := by
    intro i j
    show Swap G9 (walk i) (walk j) ↔ (SimpleGraph.pathGraph 9).Adj i j
    rw [SimpleGraph.pathGraph_adj, swap_walk_iff]

/-- `P_9` is an IR-graph. -/
theorem pathGraph_nine_isIRGraph : IsIRGraph (SimpleGraph.pathGraph 9) :=
  ⟨Fin 9, inferInstance, inferInstance, G9, ⟨pathIso.symm⟩⟩

/-- MathDB 350452 (Mynhardt–Roux non-IR conjecture for paths and cycles) is false. -/
theorem mynhardt_roux_paths_cycles_conjecture_false :
    ¬ ((∀ n : ℕ, 3 ≤ n → ¬ IsIRGraph (SimpleGraph.pathGraph n)) ∧
       (∀ n : ℕ, 5 ≤ n → ¬ IsIRGraph (SimpleGraph.cycleGraph n))) := by
  rintro ⟨hP, -⟩
  exact hP 9 (by norm_num) pathGraph_nine_isIRGraph

end IRGraphPath

/-
Notes for the compiling worker:
* `SimpleGraph.pathGraph_adj` : `(pathGraph n).Adj u v ↔ u.val + 1 = v.val ∨ v.val + 1 = u.val`
  (check the exact form/orientation at the pinned mathlib; adjust `swap_walk_iff` accordingly).
* `Finset.exists_subset_card_eq` may be named `Finset.exists_smaller_set` (older) at the pin.
* `Finset.not_mem_erase` may be `Finset.notMem_erase` at the pin.
* If kernel `decide` on `irredundant_three_iff` / `no_irredundant_four` is slow, replace the
  `Finset`-level decision by a `Bool` checker on bitmasks `Fin 512` with a proved soundness
  lemma (allowed: kernel decide with a proved-sound checker); the nine sets and witness vertices
  are in outputs/certificate-350452.json.
* The `map_rel_iff'` goal is stated as `(IRGraph G9).Adj (e i) (e j) ↔ (pathGraph 9).Adj i j`;
  after `Equiv.ofBijective_apply` it unfolds to `Swap G9 (walk i) (walk j)`; the `show` may need
  `simp only [Equiv.ofBijective_apply, toIR, IRGraph]` first.
-/
