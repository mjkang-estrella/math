/-
UNCOMPILED DRAFT. Not checked by Lean in this lane: the lane is forbidden to run Lean.
It contains `sorry` placeholders and is NOT a certificate. Root or a Sol worker must complete
and compile it. API names are from memory of Mathlib and must be checked against the pinned
Mathlib d13f23b7.

MathDB 343536 (Neuberger–Sieben–Swift, arXiv:1908.05797, Conjecture 5.6): literal endpoint.
Vertex set Fin m × Fin n (0-based coordinates; the paper's [m] × [n]).
-/
import Mathlib

open SimpleGraph Finset

namespace Grid343536

variable {V : Type*}

/-- The rectangular grid graph `P_m □ P_n` (Mathlib's box product of path graphs). -/
abbrev Grid (m n : ℕ) : SimpleGraph (Fin m × Fin n) := pathGraph m □ pathGraph n

/-- Definition 5.1 of the source: `d_B(u) = d_B(v)` for `u, v` in one cell and every cell `B`.
Here a cell is `{x | r x w}`, the class of `w`. -/
def IsEquitable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : Setoid V)
    [DecidableRel r.r] : Prop :=
  ∀ u v, r u v → ∀ w : V,
    (univ.filter (fun x => G.Adj u x ∧ r x w)).card =
      (univ.filter (fun x => G.Adj v x ∧ r x w)).card

/-- The orbit partition of a subgroup `H` of `Aut G`, for its natural action on vertices. -/
def orbitSetoid (G : SimpleGraph V) (H : Subgroup (G ≃g G)) : Setoid V where
  r u v := ∃ g ∈ H, g u = v
  iseqv := by
    refine ⟨fun u => ⟨1, H.one_mem, rfl⟩, ?_, ?_⟩
    · rintro u v ⟨g, hg, rfl⟩
      exact ⟨g⁻¹, H.inv_mem hg, by simp⟩
    · rintro u v w ⟨g, hg, rfl⟩ ⟨k, hk, rfl⟩
      exact ⟨k * g, H.mul_mem hk hg, rfl⟩

/-- A vertex with trivial stabilizer in `Aut G`. -/
def HasFreeVertex (G : SimpleGraph V) : Prop :=
  ∃ x : V, ∀ g : G ≃g G, g x = x → g = 1

/-- The poset of equitable partitions, ordered by refinement (`Setoid` order: `r ≤ s` iff
`r` refines `s`). Decidability is supplied classically. -/
def EqPart [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Type _ :=
  {r : Setoid V // @IsEquitable V _ G _ r (Classical.decRel _)}

noncomputable instance [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    PartialOrder (EqPart G) := Subtype.partialOrder _

/-! ## Literal endpoints (the three sentences of Conjecture 5.6) -/

/-- Sentence 1: the equitable partitions are exactly the orbit partitions of subgroups of the
automorphism group. -/
theorem equitable_iff_orbit (m n : ℕ) (r : Setoid (Fin m × Fin n)) [DecidableRel r.r] :
    IsEquitable (Grid m n) r ↔ ∃ H : Subgroup (Grid m n ≃g Grid m n), r = orbitSetoid _ H := by
  sorry -- §2 easy direction + Main Theorem (§3–§6 of PROOF-343536.md)

/-- Sentence 3: a vertex with trivial stabilizer exists iff not `2 ≤ m = n ≤ 3`. -/
theorem free_vertex_iff (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    HasFreeVertex (Grid m n) ↔ ¬ (2 ≤ m ∧ m = n ∧ n ≤ 3) := by
  sorry -- §7: stabilizer computation in A0 + Corollary B

/-- Sentence 2: the lattice of equitable partitions is isomorphic to the lattice of subgroups
exactly when there is a vertex with trivial stabilizer. Isomorphism of lattices is stated as an
order isomorphism, which is equivalent for lattices. -/
theorem lattice_iso_iff (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    Nonempty (EqPart (Grid m n) ≃o Subgroup (Grid m n ≃g Grid m n)) ↔
      HasFreeVertex (Grid m n) := by
  sorry -- Corollary C

/-- Conjecture 5.6, all three sentences together. -/
theorem conjecture_5_6 (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (∀ r : Setoid (Fin m × Fin n), ∀ _ : DecidableRel r.r,
        IsEquitable (Grid m n) r ↔ ∃ H : Subgroup (Grid m n ≃g Grid m n), r = orbitSetoid _ H) ∧
    (Nonempty (EqPart (Grid m n) ≃o Subgroup (Grid m n ≃g Grid m n)) ↔
        HasFreeVertex (Grid m n)) ∧
    (HasFreeVertex (Grid m n) ↔ ¬ (2 ≤ m ∧ m = n ∧ n ≤ 3)) :=
  ⟨fun r _ => equitable_iff_orbit m n r, lattice_iso_iff m n hm hn, free_vertex_iff m n hm hn⟩

/-! ## Proof skeleton (lemma statements matching PROOF-343536.md) -/

section Skeleton

variable {m n : ℕ}

/-- Coordinates as natural numbers, adjacency in the grid. -/
lemma grid_adj_iff (x y : Fin m × Fin n) :
    (Grid m n).Adj x y ↔
      (x.2 = y.2 ∧ (x.1.val + 1 = y.1.val ∨ y.1.val + 1 = x.1.val)) ∨
      (x.1 = y.1 ∧ (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)) := by
  simp [Grid, boxProd_adj, pathGraph_adj]; tauto

/-- The reflections `ρ_r`, `ρ_c` and (for `m = n`) the transpose `τ`, as graph automorphisms. -/
def rowFlip : Grid m n ≃g Grid m n where
  toEquiv := (Fin.revPerm).prodCongr (Equiv.refl _)
  map_rel_iff' := by sorry

def colFlip : Grid m n ≃g Grid m n where
  toEquiv := (Equiv.refl _).prodCongr Fin.revPerm
  map_rel_iff' := by sorry

def transpose : Grid n n ≃g Grid n n where
  toEquiv := Equiv.prodComm _ _
  map_rel_iff' := by sorry

/-- The explicit group `A0`. -/
def A0 (m n : ℕ) : Subgroup (Grid m n ≃g Grid m n) :=
  if h : m = n then
    Subgroup.closure {rowFlip, colFlip, h ▸ (transpose (n := n) : Grid n n ≃g Grid n n)}
  else Subgroup.closure {rowFlip, colFlip}

/-- `H(π) = {g ∈ A0 : χ ∘ g = χ}`. -/
def Hpi (r : Setoid (Fin m × Fin n)) : Subgroup (Grid m n ≃g Grid m n) where
  carrier := {g | g ∈ A0 m n ∧ ∀ x, r (g x) x}
  one_mem' := ⟨Subgroup.one_mem _, fun x => Setoid.refl _⟩
  mul_mem' := by sorry
  inv_mem' := by sorry

/-- L2: row determinism for two colourings with the same neighbour rule. Stated for the
colourings `x ↦ ⟦x⟧` and `x ↦ ⟦g x⟧`. -/
lemma row_determinism (r : Setoid (Fin m × Fin n)) [DecidableRel r.r]
    (hr : IsEquitable (Grid m n) r) (g : Grid m n ≃g Grid m n)
    (hrow : ∀ j : Fin n, ∀ h0 : 0 < m, r (g (⟨0, h0⟩, j)) (⟨0, h0⟩, j)) :
    ∀ x, r (g x) x := by
  sorry -- induction on x.1.val; multiset subtraction argument

/-- L3: propagation through layers. -/
lemma propagation (r : Setoid (Fin m × Fin n)) [DecidableRel r.r]
    (hr : IsEquitable (Grid m n) r) (lay : Fin m × Fin n → ℕ)
    (hinv : ∀ x y, r x y → lay x = lay y) (hA0 : ∀ g ∈ A0 m n, ∀ x, lay (g x) = lay x)
    (hstep : ∀ w, 2 ≤ lay w → ∃ a, (Grid m n).Adj w a ∧ lay a + 1 = lay w ∧
        ∀ b, (Grid m n).Adj a b → lay w ≤ lay b → b = w)
    (hbase : ∀ u u', lay u = 1 → r u u' → ∃ g ∈ Hpi r, g u = u') :
    ∀ u u', r u u' → ∃ g ∈ Hpi r, g u = u' := by
  sorry

/-- Border transitivity in the three regimes (§4, §5, §6). -/
lemma border_transitive (r : Setoid (Fin m × Fin n)) [DecidableRel r.r]
    (hr : IsEquitable (Grid m n) r) :
    ∃ lay : Fin m × Fin n → ℕ, (∀ x y, r x y → lay x = lay y) ∧
      (∀ g ∈ A0 m n, ∀ x, lay (g x) = lay x) ∧
      (∀ w, 2 ≤ lay w → ∃ a, (Grid m n).Adj w a ∧ lay a + 1 = lay w ∧
        ∀ b, (Grid m n).Adj a b → lay w ≤ lay b → b = w) ∧
      (∀ u u', lay u = 1 → r u u' → ∃ g ∈ Hpi r, g u = u') := by
  sorry

/-- Main Theorem: an equitable partition is the orbit partition of `H(π)`. -/
theorem main (r : Setoid (Fin m × Fin n)) [DecidableRel r.r]
    (hr : IsEquitable (Grid m n) r) : r = orbitSetoid _ (Hpi r) := by
  obtain ⟨lay, h1, h2, h3, h4⟩ := border_transitive r hr
  have key := propagation r hr lay h1 h2 h3 h4
  ext u v
  constructor
  · intro huv; exact key u v huv
  · rintro ⟨g, hg, rfl⟩; exact Setoid.symm (hg.2 u)

end Skeleton

end Grid343536
