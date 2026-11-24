# Lean source appendix for MathDB 345190

Modules appear in import order.

### `BridgeFragmentModel.lean`

```lean
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace BridgeFragment

open SimpleGraph

/-- A graph class on finite vertex types, closed under isomorphism. -/
structure GClass where
  mem : ∀ {V : Type} [Finite V], SimpleGraph V → Prop
  iso : ∀ {V W : Type} [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W},
    G ≃g H → (mem G ↔ mem H)

def Decomposable (A : GClass) : Prop :=
  ∀ {V : Type} [Finite V] (G : SimpleGraph V),
    A.mem G ↔ ∀ c : G.ConnectedComponent, A.mem (G.induce c.supp)

def BridgeAddable (A : GClass) : Prop :=
  ∀ {V : Type} [Finite V] (G : SimpleGraph V) (u v : V),
    A.mem G → ¬G.Reachable u v → A.mem (G ⊔ edge u v)

/-- Isomorphism on the labelled graphs satisfying a given predicate. -/
def graphIsoSetoid {V : Type} (P : SimpleGraph V → Prop) : Setoid {G // P G} where
  r G H := Nonempty (G.val ≃g H.val)
  iseqv := ⟨fun _ => ⟨SimpleGraph.Iso.refl⟩, fun ⟨e⟩ => ⟨e.symm⟩,
    fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

abbrev GraphTypes {V : Type} (P : SimpleGraph V → Prop) :=
  Quotient (graphIsoSetoid P)

noncomputable instance {V : Type} [Finite V] (P : SimpleGraph V → Prop) :
    Fintype (GraphTypes P) :=
  Fintype.ofFinite _

abbrev UnlabelledMembers (A : GClass) (n : ℕ) :=
  GraphTypes (fun G : SimpleGraph (Fin n) => A.mem G)

noncomputable def largestComponent {V : Type} [Finite V] (G : SimpleGraph V) : ℕ :=
  letI := Fintype.ofFinite G.ConnectedComponent
  Finset.univ.sup (fun c : G.ConnectedComponent => Nat.card c.supp)

theorem largestComponent_iso {V W : Type} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    largestComponent G = largestComponent H := by
  classical
  let := Fintype.ofFinite G.ConnectedComponent
  let := Fintype.ofFinite H.ConnectedComponent
  have hc (c : G.ConnectedComponent) :
      Nat.card c.supp = Nat.card (e.connectedComponentEquiv c).supp :=
    Nat.card_congr (c.isoEquivSupp e)
  change Finset.univ.sup (fun c : G.ConnectedComponent => Nat.card c.supp) =
    Finset.univ.sup (fun c : H.ConnectedComponent => Nat.card c.supp)
  apply le_antisymm
  · apply Finset.sup_le
    intro c _
    rw [hc c]
    exact Finset.le_sup (f := fun d : H.ConnectedComponent => Nat.card d.supp)
      (Finset.mem_univ (e.connectedComponentEquiv c))
  · apply Finset.sup_le
    intro c _
    obtain ⟨d, rfl⟩ := e.connectedComponentEquiv.surjective c
    rw [← hc d]
    exact Finset.le_sup (f := fun d : G.ConnectedComponent => Nat.card d.supp)
      (Finset.mem_univ d)

/-- The number of vertices outside a largest connected component. -/
noncomputable def frag {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  n - largestComponent G

noncomputable def fragType (A : GClass) (n : ℕ) : UnlabelledMembers A n → ℕ :=
  Quotient.lift (fun G => frag G.val) (fun _ _ ⟨e⟩ => by
    simp only [frag, largestComponent_iso e])

/-- Arithmetic mean for the uniform distribution on isomorphism classes. -/
noncomputable def meanFrag (A : GClass) (n : ℕ) : ℚ :=
  (∑ q : UnlabelledMembers A n, (fragType A n q : ℚ)) / Fintype.card (UnlabelledMembers A n)

/-- The literal counterexample target, with membership at each positive order. -/
def Counterexample : Prop :=
  ∃ A : GClass, Decomposable A ∧ BridgeAddable A ∧
    (∀ n : ℕ, 0 < n → Nonempty (UnlabelledMembers A n)) ∧
    ¬ ∃ c : ℚ, ∀ n : ℕ, 0 < n → meanFrag A n ≤ c

end BridgeFragment

#print axioms BridgeFragment.largestComponent_iso
#print axioms BridgeFragment.meanFrag
#print axioms BridgeFragment.Counterexample
```

### `BridgeFragmentPieces.lean`

```lean
import BridgeFragmentModel
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace BridgeFragment

open SimpleGraph

variable {V W : Type}

/-- The spanning graph left when all bridges have been deleted. -/
def core (G : SimpleGraph V) : SimpleGraph V :=
  G.deleteEdges {e | G.IsBridge e}

@[simp] theorem core_adj {G : SimpleGraph V} {u v : V} :
    (core G).Adj u v ↔ G.Adj u v ∧ ¬G.IsBridge s(u, v) := by
  simp [core]

theorem core_le (G : SimpleGraph V) : core G ≤ G := deleteEdges_le _

/-- Graph induced by the nonbridge edges on a piece. -/
abbrev Piece (G : SimpleGraph V) := (core G).ConnectedComponent

abbrev pieceGraph (G : SimpleGraph V) (p : Piece G) := (core G).induce p.supp

theorem core_add {G : SimpleGraph V} {u v : V} (h : ¬G.Reachable u v) :
    core (G ⊔ edge u v) = core G := by
  ext x y
  simp only [core_adj, sup_adj, adj_edge]
  have newBridge : (G ⊔ edge u v).IsBridge s(u, v) :=
    isBridge_sup_edge.mpr (IsBridge.of_not_reachable h)
  constructor
  · rintro ⟨hxy | ⟨he, _⟩, hb⟩
    · exact ⟨hxy, fun hb' =>
        hb (IsBridge.sup_edge_of_not_reachable_of_isBridge h hb' hxy)⟩
    · exact (hb (he ▸ newBridge)).elim
  · exact fun ⟨hxy, hb⟩ => ⟨Or.inl hxy, fun h' => hb (h'.anti le_sup_left)⟩

/-- An isomorphism also identifies the graphs with corresponding edges deleted. -/
def deleteEdgeIso {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (u v : V) :
    G.deleteEdges {s(u, v)} ≃g H.deleteEdges {s(e u, e v)} where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro a b
    change (H.deleteEdges _).Adj (e a) (e b) ↔ (G.deleteEdges _).Adj a b
    simp only [deleteEdges_adj, Set.mem_singleton_iff, e.map_rel_iff, Sym2.eq_iff,
      e.injective.eq_iff]

theorem iso_bridge_iff {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (u v : V) :
    H.IsBridge s(e u, e v) ↔ G.IsBridge s(u, v) :=
  not_congr (Iso.reachable_iff (φ := deleteEdgeIso e u v))

def coreIso {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) : core G ≃g core H where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro u v
    change (core H).Adj (e u) (e v) ↔ (core G).Adj u v
    simp only [core_adj, e.map_rel_iff, iso_bridge_iff]

def componentIso {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (c : G.ConnectedComponent) :
    c.toSimpleGraph ≃g (e.connectedComponentEquiv c).toSimpleGraph where
  toEquiv := c.isoEquivSupp e
  map_rel_iff' := by
    intro a b
    exact e.map_rel_iff

/-- A walk starting in an adjacency-closed set can be lifted to the induced graph. -/
theorem reachable_induce_closed {G : SimpleGraph V} {s : Set V}
    (closed : ∀ ⦃u v⦄, u ∈ s → G.Adj u v → v ∈ s) (a b : s) :
    (G.induce s).Reachable a b ↔ G.Reachable a.val b.val := by
  refine ⟨fun h => h.map (Embedding.induce s).toHom, ?_⟩
  rintro ⟨p⟩
  have liftWalk {x y : V} (p : G.Walk x y) :
      ∀ (hx : x ∈ s) (hy : y ∈ s), (G.induce s).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
    induction p with
    | nil => intros; exact Reachable.rfl
    | cons h _ ih =>
      intro hx hy
      exact (Adj.reachable (G := G.induce s) (show (G.induce s).Adj
        ⟨_, hx⟩ ⟨_, closed hx h⟩ from h)).trans (ih (closed hx h) hy)
  exact liftWalk p a.prop b.prop

theorem reachable_mem_closed {G : SimpleGraph V} {s : Set V}
    (closed : ∀ ⦃u v⦄, u ∈ s → G.Adj u v → v ∈ s) {u v : V}
    (h : G.Reachable u v) (hu : u ∈ s) : v ∈ s := by
  rw [reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact hu
  | tail _ ha ih => exact closed ih ha

theorem induce_bridge_iff {G : SimpleGraph V} {s : Set V}
    (closed : ∀ ⦃u v⦄, u ∈ s → G.Adj u v → v ∈ s) (a b : s) :
    (G.induce s).IsBridge s(a, b) ↔ G.IsBridge s(a.val, b.val) := by
  have he : (G.induce s).deleteEdges {s(a, b)} =
      (G.deleteEdges {s(a.val, b.val)}).induce s := by
    ext x y
    simp only [deleteEdges_adj, comap_adj, induce, Function.Embedding.subtype_apply,
      Set.mem_singleton_iff, Sym2.eq_iff, Subtype.val_inj]
  rw [isBridge_iff, isBridge_iff, he]
  exact not_congr (reachable_induce_closed (fun _ _ hu huv => closed hu (deleteEdges_adj.mp huv).1) a b)

theorem core_induce_closed {G : SimpleGraph V} {s : Set V}
    (closed : ∀ ⦃u v⦄, u ∈ s → G.Adj u v → v ∈ s) :
    core (G.induce s) = (core G).induce s := by
  ext x y
  rw [core_adj, induce_bridge_iff closed]
  exact (core_adj (u := x.val) (v := y.val) (G := G)).symm

/-- A component of a closed induced subgraph is isomorphic to the ambient component. -/
noncomputable def inducedComponentIso {G : SimpleGraph V} {s : Set V}
    (closed : ∀ ⦃u v⦄, u ∈ s → G.Adj u v → v ∈ s) (a : s) :
    ((G.induce s).connectedComponentMk a).toSimpleGraph ≃g
      (G.connectedComponentMk a.val).toSimpleGraph where
  toEquiv :=
    { toFun := fun x => ⟨x.val.val, by
        change G.connectedComponentMk x.val.val = G.connectedComponentMk a.val
        exact ConnectedComponent.sound ((reachable_induce_closed closed x.val a).mp
          (ConnectedComponent.exact x.prop))⟩
      invFun := fun x =>
        let hx : G.Reachable x.val a.val := ConnectedComponent.exact x.prop
        let y : s := ⟨x.val, reachable_mem_closed closed hx.symm a.prop⟩
        ⟨y, ConnectedComponent.sound ((reachable_induce_closed closed y a).mpr hx)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_rel_iff' := Iff.rfl

theorem piece_closed_in_component {G : SimpleGraph V} (c : G.ConnectedComponent) :
    ∀ ⦃u v⦄, u ∈ c.supp → (core G).Adj u v → v ∈ c.supp :=
  fun _ _ hu h => c.mem_supp_of_adj_mem_supp hu (core_adj.mp h).1

theorem classOfPieces_iff {P : GClass} {G : SimpleGraph V} [Finite V] :
    (∀ p : Piece G, P.mem (pieceGraph G p)) ↔
      ∀ c : G.ConnectedComponent, ∀ p : Piece c.toSimpleGraph,
        P.mem (pieceGraph c.toSimpleGraph p) := by
  have eqCore (c : G.ConnectedComponent) :
      core c.toSimpleGraph = (core G).induce c.supp :=
    core_induce_closed (fun _ _ hu h => c.mem_supp_of_adj_mem_supp hu h)
  constructor
  · intro h c
    change ∀ p : (core c.toSimpleGraph).ConnectedComponent, P.mem p.toSimpleGraph
    rw [eqCore c]
    intro p
    induction p using ConnectedComponent.ind with
    | _ a => exact (P.iso (inducedComponentIso (piece_closed_in_component c) a)).mpr (h _)
  · intro h p
    induction p using ConnectedComponent.ind with
    | _ a =>
      let c := G.connectedComponentMk a
      have hc := h c
      change ∀ p : (core c.toSimpleGraph).ConnectedComponent, P.mem p.toSimpleGraph at hc
      rw [eqCore c] at hc
      exact (P.iso (inducedComponentIso (piece_closed_in_component c)
        ⟨a, rfl⟩)).mp (hc _)

/-- Class whose bridge-deleted pieces satisfy a specified isomorphism-invariant predicate. -/
def classOfPieces (P : GClass) : GClass where
  mem G := ∀ p : Piece G, P.mem (pieceGraph G p)
  iso e := by
    change (∀ p, P.mem (pieceGraph _ p)) ↔ ∀ q, P.mem (pieceGraph _ q)
    let f := coreIso e
    constructor
    · intro h q
      obtain ⟨p, rfl⟩ := f.connectedComponentEquiv.surjective q
      exact (P.iso (componentIso f p)).mp (h p)
    · intro h p
      exact (P.iso (componentIso f p)).mpr (h _)

theorem classOfPieces_decomposable (P : GClass) : Decomposable (classOfPieces P) :=
  by
    intro V _ G
    exact classOfPieces_iff (P := P) (G := G)

theorem classOfPieces_bridgeAddable (P : GClass) : BridgeAddable (classOfPieces P) := by
  intro V _ G u v hG h
  change ∀ p : (core (G ⊔ edge u v)).ConnectedComponent, P.mem p.toSimpleGraph
  rw [core_add h]
  exact hG

end BridgeFragment

#print axioms BridgeFragment.classOfPieces_bridgeAddable
#print axioms BridgeFragment.classOfPieces_decomposable
```

### `BridgeFragmentLayers.lean`

```lean
import BridgeFragmentPieces
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Perm

namespace BridgeFragment

open SimpleGraph

abbrev Layers (t : ℕ) := Fin t ⊕ Fin t
abbrev Vertices (t m : ℕ) := Layers t × ZMod m
abbrev Nonzero (m : ℕ) := {d : ZMod m // d ≠ 0}
abbrev Offsets (t m : ℕ) := Fin t → Fin t → Nonzero m → Bool

variable {t m : ℕ}

private def optional (D : Offsets t m) (u v : Vertices t m) : Prop :=
  ∃ (i j : Fin t) (d : Nonzero m), u.1 = Sum.inl i ∧ v.1 = Sum.inr j ∧
    v.2 - u.2 = d.val ∧ D i j d = true

/-- Each layer is a clique. Different layers share the zero-offset matching.
For a left and a right layer, the remaining offsets can be chosen independently. -/
def layersGraph (D : Offsets t m) : SimpleGraph (Vertices t m) where
  Adj u v :=
    (u.1 = v.1 ∧ u.2 ≠ v.2) ∨ (u.1 ≠ v.1 ∧ u.2 = v.2) ∨
      optional D u v ∨ optional D v u
  symm := ⟨by
    intro u v h
    rcases h with h | h | h | h
    · exact Or.inl ⟨h.1.symm, h.2.symm⟩
    · exact Or.inr (Or.inl ⟨h.1.symm, h.2.symm⟩)
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))⟩
  loopless := ⟨by intro u; simp [optional]⟩

private theorem adj_in_layer (D : Offsets t m) (i : Layers t) {a b : ZMod m} (h : a ≠ b) :
    (layersGraph D).Adj (i, a) (i, b) := Or.inl ⟨rfl, h⟩

private theorem adj_matching (D : Offsets t m) {i j : Layers t} (a : ZMod m) (h : i ≠ j) :
    (layersGraph D).Adj (i, a) (j, a) := Or.inr (Or.inl ⟨h, rfl⟩)

theorem layers_preconnected (D : Offsets t m) : (layersGraph D).Preconnected := by
  intro ⟨i, a⟩ ⟨j, b⟩
  have h₁ : (layersGraph D).Reachable (i, a) (i, b) := by
    by_cases h : a = b
    · subst b
      exact Reachable.rfl
    · exact (adj_in_layer D i h).reachable
  have h₂ : (layersGraph D).Reachable (i, b) (j, b) := by
    by_cases h : i = j
    · subst j
      exact Reachable.rfl
    · exact (adj_matching D b h).reachable
  exact h₁.trans h₂

theorem layers_connected (D : Offsets t m) (ht : 0 < t) : (layersGraph D).Connected :=
  { preconnected := layers_preconnected D, nonempty := ⟨Sum.inl ⟨0, ht⟩, 0⟩ }

/-- Simultaneous translation on the cyclic coordinate. -/
def shiftIso (D : Offsets t m) (z : ZMod m) : layersGraph D ≃g layersGraph D where
  toEquiv := (Equiv.refl _).prodCongr (Equiv.addRight z)
  map_rel_iff' := by
    intro u v
    change (layersGraph D).Adj (u.1, u.2 + z) (v.1, v.2 + z) ↔ (layersGraph D).Adj u v
    simp only [layersGraph, optional, not_congr add_right_cancel_iff, add_right_cancel_iff, add_sub_add_right_eq_sub]

@[simp] theorem shiftIso_apply (D : Offsets t m) (z : ZMod m) (u : Vertices t m) :
    shiftIso D z u = (u.1, u.2 + z) := rfl

theorem shift_to_zero (D : Offsets t m) (u : Vertices t m) :
    shiftIso D (-u.2) u = (u.1, 0) := by simp

private theorem third_residue [NeZero m] (hm : 2 < m) (a b : ZMod m) :
    ∃ c : ZMod m, c ≠ a ∧ c ≠ b := by
  classical
  have h : ({a, b} : Finset (ZMod m)).card < (Finset.univ : Finset (ZMod m)).card := by
    rw [Finset.card_univ, ZMod.card]
    by_cases hab : a = b
    · simp [hab, show 1 < m by omega]
    · simpa [hab] using hm
  obtain ⟨c, _, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card h
  exact ⟨c, by simpa using hnot⟩

theorem layers_bridgeless [NeZero m] (D : Offsets t m) (hm : 2 < m)
    {u v : Vertices t m} (h : (layersGraph D).Adj u v) :
    ¬ (layersGraph D).IsBridge s(u, v) := by
  intro hb
  rw [isBridge_iff] at hb
  apply hb
  rcases u with ⟨i, a⟩
  rcases v with ⟨j, b⟩
  by_cases hij : i = j
  · subst j
    obtain ⟨c, hca, hcb⟩ := third_residue hm a b
    have h₁ : ((layersGraph D).deleteEdges {s((i,a),(i,b))}).Adj (i,a) (i,c) :=
      deleteEdges_adj.mpr ⟨adj_in_layer D i hca.symm, by
        simp [hcb, hca]⟩
    have h₂ : ((layersGraph D).deleteEdges {s((i,a),(i,b))}).Adj (i,c) (i,b) :=
      deleteEdges_adj.mpr ⟨adj_in_layer D i hcb, by
        simp [hcb, hca]⟩
    exact h₁.reachable.trans h₂.reachable
  · have hm' : 1 < m := by omega
    let : Fact (1 < m) := ⟨hm'⟩
    have h₁ : ((layersGraph D).deleteEdges {s((i,a),(j,b))}).Adj (i,a) (i,a+1) :=
      deleteEdges_adj.mpr ⟨adj_in_layer D i (by simp), by simp [hij]⟩
    have h₂ : ((layersGraph D).deleteEdges {s((i,a),(j,b))}).Adj (i,a+1) (j,b+1) :=
      deleteEdges_adj.mpr ⟨(shiftIso D 1).map_rel_iff.mpr h, by
        simp [hij]⟩
    have h₃ : ((layersGraph D).deleteEdges {s((i,a),(j,b))}).Adj (j,b+1) (j,b) :=
      deleteEdges_adj.mpr ⟨adj_in_layer D j (by simp), by simp [Ne.symm hij]⟩
    exact h₁.reachable.trans (h₂.reachable.trans h₃.reachable)

theorem layers_core [NeZero m] (D : Offsets t m) (hm : 2 < m) :
    core (layersGraph D) = layersGraph D := by
  ext u v
  exact core_adj.trans ⟨And.left, fun h => ⟨h, layers_bridgeless D hm h⟩⟩

private theorem read_offset (D : Offsets t m) (i j : Fin t) (d : Nonzero m) :
    (layersGraph D).Adj (Sum.inl i, 0) (Sum.inr j, d.val) ↔ D i j d = true := by
  change (_ ∨ (_ ∧ 0 = d.val) ∨ optional D _ _ ∨ optional D _ _) ↔ _
  simp only [reduceCtorEq, false_and, false_or, not_false_eq_true, true_and,
    ne_eq, eq_comm (a := (0 : ZMod m)), d.prop, optional,
    Sum.inl.injEq, Sum.inr.injEq, sub_zero]
  constructor
  · rintro (⟨i', j', d', rfl, rfl, hd, h⟩ | ⟨_, _, _, h, _⟩)
    · have : d = d' := Subtype.ext hd
      exact this ▸ h
  · intro h
    exact Or.inl ⟨i, j, d, rfl, rfl, rfl, h⟩

theorem layers_injective : Function.Injective (layersGraph (t := t) (m := m)) := by
  intro D E h
  funext i j d
  have he := (read_offset D i j d).symm.trans
    ((congrArg (fun G : SimpleGraph (Vertices t m) =>
      G.Adj (Sum.inl i, 0) (Sum.inr j, d.val)) h).to_iff.trans (read_offset E i j d))
  cases hD : D i j d <;> cases hE : E i j d <;> simp_all

/-- Labelled graphs in the family, possibly transported by a permutation. -/
def IsLayerType (t m : ℕ) {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ D : Offsets t m, Nonempty (layersGraph D ≃g G)

abbrev LayerTypes (t m : ℕ) :=
  GraphTypes (IsLayerType t m : SimpleGraph (Vertices t m) → Prop)

theorem isLayerType_iso {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    IsLayerType t m G ↔ IsLayerType t m H :=
  ⟨fun ⟨D, ⟨f⟩⟩ => ⟨D, ⟨f.trans e⟩⟩, fun ⟨D, ⟨f⟩⟩ => ⟨D, ⟨f.trans e.symm⟩⟩⟩

def offsetType (D : Offsets t m) : LayerTypes t m :=
  Quotient.mk _ ⟨layersGraph D, D, ⟨SimpleGraph.Iso.refl⟩⟩

theorem offsetType_surjective : Function.Surjective (offsetType (t := t) (m := m)) := by
  intro q
  induction q using Quotient.ind with
  | _ G =>
    obtain ⟨D, ⟨e⟩⟩ := G.prop
    exact ⟨D, Quotient.sound ⟨e⟩⟩

end BridgeFragment

#print axioms BridgeFragment.layers_bridgeless
#print axioms BridgeFragment.layers_injective
```

### `BridgeFragmentCounting.lean`

```lean
import BridgeFragmentLayers
import Mathlib.Data.Fintype.BigOperators

namespace BridgeFragment

open SimpleGraph

theorem card_le_mul_of_fibres {α β : Type} [Fintype α] [Fintype β]
    (f : α → β) (M : ℕ) (h : ∀ b, Nat.card {a // f a = b} ≤ M) :
    Fintype.card α ≤ Fintype.card β * M := by
  classical
  have eq := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
  rw [Fintype.card_sigma] at eq
  rw [← eq]
  calc
    (∑ b : β, Fintype.card {a // f a = b}) ≤ ∑ _ : β, M :=
      Finset.sum_le_sum fun b _ => by simpa only [Nat.card_eq_fintype_card] using h b
    _ = _ := by simp

theorem card_vertices (t m : ℕ) [NeZero m] : Fintype.card (Vertices t m) = 2 * t * m := by
  simp [two_mul]

theorem card_offsets (t m : ℕ) [NeZero m] :
    Fintype.card (Offsets t m) = 2 ^ (t * t * (m - 1)) := by
  classical
  have hc : Fintype.card (Nonzero m) = m - 1 := by
    rw [Fintype.card_subtype_compl (fun x : ZMod m => x = 0), ZMod.card,
      Fintype.card_subtype_eq]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, hc, ← pow_mul]
  congr 1
  ac_rfl

noncomputable def offsetRep (t m : ℕ) [NeZero m] (q : LayerTypes t m) : Offsets t m :=
  Classical.choose (offsetType_surjective q)

@[simp] theorem offsetRep_spec {t m : ℕ} [NeZero m] (q : LayerTypes t m) :
    offsetType (offsetRep t m q) = q :=
  Classical.choose_spec (offsetType_surjective q)

theorem layerType_fibre_le {t m : ℕ} [NeZero m] (q : LayerTypes t m) :
    Nat.card {D : Offsets t m // offsetType D = q} ≤ (2 * t * m).factorial := by
  classical
  let α := {D : Offsets t m // offsetType D = q}
  have h (a : α) : Nonempty (layersGraph a.val ≃g layersGraph (offsetRep t m q)) :=
    Quotient.exact (a.prop.trans (offsetRep_spec q).symm)
  let f (a : α) : Equiv.Perm (Vertices t m) := (h a).some.toEquiv
  have inj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply layers_injective
    ext u v
    have ha := (h a).some.map_rel_iff (a := u) (b := v)
    have hb := (h b).some.map_rel_iff (a := u) (b := v)
    change (layersGraph (offsetRep t m q)).Adj (f a u) (f a v) ↔ _ at ha
    change (layersGraph (offsetRep t m q)).Adj (f b u) (f b v) ↔ _ at hb
    rw [hab] at ha
    exact ha.symm.trans hb
  have bound := Fintype.card_le_of_injective f inj
  simpa only [Nat.card_eq_fintype_card, Fintype.card_perm, card_vertices] using bound

theorem layerType_count {t m : ℕ} [NeZero m] :
    2 ^ (t * t * (m - 1)) ≤ Fintype.card (LayerTypes t m) * (2 * t * m).factorial := by
  rw [← card_offsets]
  exact card_le_mul_of_fibres offsetType _ layerType_fibre_le

/-- The spanning graph containing just the bridges. -/
def bridges {V : Type} (G : SimpleGraph V) : SimpleGraph V :=
  G.deleteEdges {e | ¬G.IsBridge e}

@[simp] theorem bridges_adj {V : Type} {G : SimpleGraph V} {u v : V} :
    (bridges G).Adj u v ↔ G.Adj u v ∧ G.IsBridge s(u, v) := by simp [bridges]

theorem bridges_le {V : Type} (G : SimpleGraph V) : bridges G ≤ G := deleteEdges_le _

theorem bridges_acyclic {V : Type} (G : SimpleGraph V) : (bridges G).IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro u v h
  exact (bridges_adj.mp h).2.anti (bridges_le G)

theorem acyclic_card_edges_le {V : Type} [Fintype V] [Nonempty V] {G : SimpleGraph V}
    (h : G.IsAcyclic) : Nat.card G.edgeSet + 1 ≤ Fintype.card V := by
  classical
  let : DecidableRel G.Adj := Classical.decRel _
  obtain ⟨T, hGT, _, hT⟩ := (connected_top (V := V)).exists_isTree_le_of_le_of_isAcyclic
    (le_top : G ≤ ⊤) h
  let : DecidableRel T.Adj := Classical.decRel _
  have hi : Nat.card G.edgeSet ≤ Nat.card T.edgeSet :=
    Nat.card_le_card_of_injective _ (Set.inclusion_injective (edgeSet_mono hGT))
  rw [Nat.card_eq_fintype_card (α := T.edgeSet), T.card_edgeSet] at hi
  exact (Nat.add_le_add_right hi 1).trans_eq hT.card_edgeFinset

theorem same_piece_no_bridge {V : Type} {G : SimpleGraph V} {u v : V}
    (h : (core G).Reachable u v) : ¬G.IsBridge s(u, v) := by
  intro hb
  apply (isBridge_iff.mp hb)
  apply h.mono
  intro a b hab
  refine deleteEdges_adj.mpr ⟨(core_adj.mp hab).1, ?_⟩
  intro he
  exact (core_adj.mp hab).2 ((Set.mem_singleton_iff.mp he).symm ▸ hb)

theorem bridge_cross_unique {V : Type} {G : SimpleGraph V} {u v x y : V}
    (hu : (core G).Reachable u x) (hv : (core G).Reachable v y)
    (h : (bridges G).Adj u v) (h' : G.Adj x y) :
    s(u, v) = s(x, y) := by
  by_contra he
  have hb := (bridges_adj.mp h).2
  have hle : core G ≤ G.deleteEdges {s(u, v)} := by
    intro a b hab
    refine deleteEdges_adj.mpr ⟨(core_adj.mp hab).1, ?_⟩
    intro eq
    exact (core_adj.mp hab).2 ((Set.mem_singleton_iff.mp eq).symm ▸ hb)
  have step : (G.deleteEdges {s(u, v)}).Adj x y :=
    deleteEdges_adj.mpr ⟨h', by simpa only [Set.mem_singleton_iff] using Ne.symm he⟩
  exact (isBridge_iff.mp hb) ((hu.mono hle).trans (step.reachable.trans (hv.mono hle).symm))

end BridgeFragment

#print axioms BridgeFragment.layerType_count
#print axioms BridgeFragment.acyclic_card_edges_le
```

### `BridgeFragmentStages.lean`

```lean
import BridgeFragmentCounting
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace BridgeFragment

open SimpleGraph

def stageT (M : ℕ) : ℕ := 2 ^ (M + 20)
def stageM (M : ℕ) : ℕ := stageT M ^ 3
def stageSize (M : ℕ) : ℕ := 2 * stageT M * stageM M
def stageOrder (M : ℕ) : ℕ := 2 * stageSize M

theorem stageT_eq (M : ℕ) : stageT M = 4 * 2 ^ (M + 18) := by
  change 2 ^ (M + 18 + 2) = _
  rw [pow_add]
  ring

theorem succ_le_two_pow (M : ℕ) : M + 1 ≤ 2 ^ M := by
  induction M with
  | zero => decide
  | succ M ih =>
    rw [pow_succ]
    omega

theorem exponent_allowance (M : ℕ) :
    4 * (M+20) + 1 + 2 * (7 * (4 * (M+20) + 2) + M) ≤ 2 ^ (M + 18) := by
  have h := Nat.mul_le_mul_right (2 ^ 18) (succ_le_two_pow M)
  rw [pow_add]
  norm_num at h ⊢
  omega

theorem stageT_large (M : ℕ) : M + 4 ≤ stageT M := by
  have h := exponent_allowance M
  rw [stageT_eq]
  omega

theorem stageM_large (M : ℕ) : 2 < stageM M := by
  have h := stageT_large M
  have hh := Nat.pow_le_pow_left (show 3 ≤ stageT M by omega) 3
  exact lt_of_lt_of_le (by decide : 2 < 3 ^ 3) hh

instance (M : ℕ) : NeZero (stageM M) := ⟨by have := stageM_large M; omega⟩

theorem stageSize_pow (M : ℕ) : stageSize M = 2 ^ (4 * (M + 20) + 1) := by
  unfold stageSize stageM stageT
  rw [← pow_mul, ← pow_succ', ← pow_add]
  congr 1
  omega

theorem stageOrder_pow (M : ℕ) : stageOrder M = 2 ^ (4 * (M + 20) + 2) := by
  unfold stageOrder
  rw [stageSize_pow, ← pow_succ']

theorem stageSize_large (M : ℕ) : 2 * M < stageSize M := by
  have h := Nat.le_mul_of_pos_right (2 * stageT M) (by have := stageM_large M; omega :
    0 < stageM M)
  have := stageT_large M
  unfold stageSize
  omega

def sizeAt : ℕ → ℕ
  | 0 => 1
  | j+1 => stageSize (sizeAt j)

theorem sizeAt_gap (j : ℕ) : 2 * sizeAt j < sizeAt (j+1) :=
  stageSize_large _

theorem sizeAt_strictMono : StrictMono sizeAt :=
  strictMono_nat_of_lt_succ fun j => by have := sizeAt_gap j; omega

theorem sizeAt_ge (j : ℕ) : j + 1 ≤ sizeAt j := by
  induction j with
  | zero => decide
  | succ j h =>
    have := sizeAt_gap j
    omega

/-- Allowed pieces consist of single vertices and all cyclic-layer types at the chosen orders. -/
def allowedPieces : GClass where
  mem {V} _ G :=
    Nat.card V = 1 ∨ ∃ j : ℕ, IsLayerType (stageT (sizeAt j)) (stageM (sizeAt j)) G
  iso e := by
    exact or_congr (iff_of_eq (congrArg (· = 1) (Nat.card_congr e.toEquiv)))
      (exists_congr fun _ => isLayerType_iso e)

def witness : GClass := classOfPieces allowedPieces

theorem witness_decomposable : Decomposable witness := classOfPieces_decomposable _

theorem witness_bridgeAddable : BridgeAddable witness := classOfPieces_bridgeAddable _

theorem core_bot {V : Type} : core (⊥ : SimpleGraph V) = ⊥ :=
  le_antisymm (core_le _) bot_le

theorem witness_bot {V : Type} [Finite V] : witness.mem (⊥ : SimpleGraph V) := by
  change ∀ p : (core (⊥ : SimpleGraph V)).ConnectedComponent, allowedPieces.mem p.toSimpleGraph
  rw [core_bot]
  intro p
  left
  have hne : Nonempty p.supp := by
    obtain ⟨a, ha⟩ := p.nonempty_supp
    exact ⟨⟨a, ha⟩⟩
  have hs : Subsingleton p.supp := ⟨by
    intro a b
    apply Subtype.ext
    exact reachable_bot.mp (p.reachable_of_mem_supp a.prop b.prop)⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨hs, hne⟩

theorem witness_nonempty (n : ℕ) : Nonempty (UnlabelledMembers witness n) :=
  ⟨Quotient.mk _ ⟨⊥, witness_bot⟩⟩

theorem layerOrder {t m : ℕ} [NeZero m] {V : Type} {G : SimpleGraph V}
    (h : IsLayerType t m G) : Nat.card V = 2 * t * m := by
  obtain ⟨_, ⟨e⟩⟩ := h
  rw [← Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_vertices]

/-- At the observation order, only earlier pieces and the current size can occur. -/
theorem piece_size_at {V : Type} [Finite V] {G : SimpleGraph V} (hG : witness.mem G)
    (j : ℕ) (hn : Nat.card V = stageOrder (sizeAt j)) (p : Piece G) :
    Nat.card p.supp ≤ sizeAt j ∨
      IsLayerType (stageT (sizeAt j)) (stageM (sizeAt j)) (pieceGraph G p) := by
  have hp : allowedPieces.mem (pieceGraph G p) := hG p
  change Nat.card p.supp = 1 ∨ ∃ k : ℕ,
    IsLayerType (stageT (sizeAt k)) (stageM (sizeAt k)) (pieceGraph G p) at hp
  rcases hp with hp | ⟨k, hk⟩
  · have := sizeAt_ge j
    exact Or.inl (by omega)
  have eqOrder : Nat.card p.supp = sizeAt (k+1) := layerOrder hk
  rcases lt_trichotomy k j with hlt | rfl | hgt
  · exact Or.inl (eqOrder.le.trans (sizeAt_strictMono.monotone (by omega)))
  · exact Or.inr hk
  · have hle := Nat.card_le_card_of_injective Subtype.val
      (Subtype.val_injective (p := fun v => v ∈ p.supp))
    rw [eqOrder, hn] at hle
    have hs := sizeAt_strictMono.monotone (show j+2 ≤ k+1 by omega)
    have hg : 2 * sizeAt (j+1) < sizeAt (j+2) := sizeAt_gap (j+1)
    change sizeAt (k+1) ≤ 2 * sizeAt (j+1) at hle
    omega

def competitorFactor (M : ℕ) : ℕ :=
  stageOrder M ^ (7 * stageOrder M) * 2 ^ (M * stageOrder M)

theorem competitorFactor_le (M : ℕ) :
    competitorFactor M ≤ Fintype.card (LayerTypes (stageT M) (stageM M)) := by
  let k := stageSize M
  let n := stageOrder M
  let L := 4 * (M+20) + 1
  let B := 7 * (L+1) + M
  have hk : k = 2 ^ L := stageSize_pow M
  have hn : n = 2 ^ (L+1) := stageOrder_pow M
  have hnk : n = 2 * k := rfl
  have hU : competitorFactor M = 2 ^ (n * B) := by
    change n ^ (7*n) * 2 ^ (M*n) = _
    calc
      n ^ (7*n) * 2 ^ (M*n) = (2 ^ (L+1)) ^ (7*n) * 2 ^ (M*n) :=
        congrArg (fun x : ℕ => x ^ (7*n) * 2 ^ (M*n)) hn
      _ = 2 ^ ((L+1) * (7*n) + M*n) := by simp only [← pow_mul, ← pow_add]
      _ = 2 ^ (n * B) := congrArg (fun x : ℕ => 2 ^ x) (by dsimp only [B]; ring)
  have hE : k * 2 ^ (M + 18) ≤ stageT M * stageT M * (stageM M - 1) := by
    have hm : stageM M ≤ 2 * (stageM M - 1) := by
      have := stageM_large M
      omega
    calc
      k * 2 ^ (M+18) = 2 ^ (M+18) * stageT M * stageM M * 2 := by
        change (2 * stageT M * stageM M) * _ = _
        ring
      _ ≤ 2 ^ (M+18) * stageT M * (2 * (stageM M - 1)) * 2 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hm)
      _ = stageT M * (4 * 2 ^ (M+18)) * (stageM M - 1) := by ring
      _ = _ := by rw [← stageT_eq M]
  have hExp : n * B + L * k ≤ stageT M * stageT M * (stageM M - 1) := by
    calc
      n * B + L * k = k * (L + 2 * B) := by rw [hnk]; ring
      _ ≤ k * 2 ^ (M+18) := Nat.mul_le_mul_left _ (exponent_allowance M)
      _ ≤ _ := hE
  have hbound : competitorFactor M * k.factorial ≤
      Fintype.card (LayerTypes (stageT M) (stageM M)) * k.factorial := calc
    _ ≤ competitorFactor M * k ^ k := Nat.mul_le_mul_left _ (Nat.factorial_le_pow _)
    _ = 2 ^ (n * B + L * k) := by
      calc
        competitorFactor M * k^k = 2 ^ (n * B) * k^k :=
          congrArg (· * k^k) hU
        _ = 2 ^ (n * B) * (2^L)^k :=
          congrArg (fun x : ℕ => 2 ^ (n * B) * x^k) hk
        _ = _ := by simp only [← pow_mul, ← pow_add]
    _ ≤ 2 ^ (stageT M * stageT M * (stageM M - 1)) := Nat.pow_le_pow_right (by decide) hExp
    _ ≤ _ := layerType_count
  exact Nat.le_of_mul_le_mul_right hbound (Nat.factorial_pos _)

end BridgeFragment

#print axioms BridgeFragment.witness_nonempty
#print axioms BridgeFragment.piece_size_at
#print axioms BridgeFragment.competitorFactor_le
```

### `BridgeFragmentCompetitors.lean`

```lean
import BridgeFragmentStages
import Mathlib.Tactic.Linarith

set_option maxHeartbeats 450000

namespace BridgeFragment

open SimpleGraph

def FewBig {V : Type} (G : SimpleGraph V) (M : ℕ) : Prop :=
  ∀ p q : Piece G, M < Nat.card p.supp → M < Nat.card q.supp → p = q

abbrev Competitors (j : ℕ) :=
  {G : SimpleGraph (Fin (stageOrder (sizeAt j))) // witness.mem G ∧ FewBig G (sizeAt j)}

private theorem tag_eq_of_some {V : Type} {G : SimpleGraph V} {p q : Piece G}
    (h : p.out = q.out) : p = q := by
  rw [← p.out_eq, ← q.out_eq, h]

private theorem core_adj_iff_induced {V : Type} {G : SimpleGraph V} {u v : V}
    {p : Piece G} (hu : u ∈ p.supp) (hv : v ∈ p.supp) :
    (core G).Adj u v ↔ (pieceGraph G p).Adj ⟨u, hu⟩ ⟨v, hv⟩ := Iff.rfl

private theorem bridge_code {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) :
    ∃ b : Fin n → Option (Sym2 (Fin n)),
      ∀ u v, (bridges G).Adj u v ↔ ∃ i : Fin n, b i = some s(u, v) := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h := acyclic_card_edges_le (bridges_acyclic G)
  let S := (bridges G).edgeSet
  have hle : Nat.card S ≤ n := by
    change Nat.card S + 1 ≤ Fintype.card (Fin n) at h
    simp only [Fintype.card_fin] at h
    omega
  let e : S ↪ Fin n :=
    (Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card (α := S)).symm).toEmbedding.trans
      (Fin.castLEEmb hle)
  let b (i : Fin n) : Option (Sym2 (Fin n)) :=
    if h : ∃ x : S, e x = i then some (Classical.choose h).val else none
  refine ⟨b, fun u v => ⟨?_, ?_⟩⟩
  · intro huv
    let x : S := ⟨s(u,v), huv⟩
    have hx : ∃ y : S, e y = e x := ⟨x, rfl⟩
    refine ⟨e x, ?_⟩
    dsimp only [b]
    rw [dite_eq_left hx, e.injective (Classical.choose_spec hx)]
  · rintro ⟨i, hi⟩
    by_cases hx : ∃ x : S, e x = i
    · dsimp only [b] at hi
      rw [dite_eq_left hx, Option.some.injEq] at hi
      change s(u,v) ∈ S
      exact hi ▸ (Classical.choose hx).prop
    · dsimp only [b] at hi
      rw [dite_eq_right hx] at hi
      contradiction

/-- The fields encode piece labels, small-piece coordinates, one large-piece
representative and its coordinates, small adjacency rows, and the bridges. -/
abbrev CompetitorCode (t m M n : ℕ) [NeZero m] :=
  (Fin n → Option (Fin n)) × (Fin n → Fin M) ×
  LayerTypes t m × (Fin n → Vertices t m) ×
  (Fin n → Fin M → Bool) × (Fin n → Option (Sym2 (Fin n)))

private def decodeAdj {t m M n : ℕ} [NeZero m] (c : CompetitorCode t m M n) (u v : Fin n) : Prop :=
  let (tag, small, big, coord, bits, b) := c
  (∃ i, b i = some s(u,v)) ∨
    (tag u = tag v ∧
      ((tag u = none ∧ (layersGraph (offsetRep t m big)).Adj (coord u) (coord v)) ∨
       (tag u ≠ none ∧ bits u (small v) = true)))

private theorem exists_competitorCode {t m M n : ℕ} [NeZero m]
    (ht : 0 < t) (hM : 0 < M) (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (hFew : FewBig G M)
    (hTypes : ∀ q : Piece G, M < Nat.card q.supp → IsLayerType t m (pieceGraph G q)) :
    ∃ c : CompetitorCode t m M n, ∀ u v, G.Adj u v ↔ decodeAdj c u v := by
  classical
  let p (u : Fin n) : Piece G := (core G).connectedComponentMk u
  let small (p : Piece G) : Prop := Nat.card p.supp ≤ M
  let tag (u : Fin n) : Option (Fin n) := if small (p u) then some (p u).out else none
  have tag_none (u : Fin n) : tag u = none ↔ ¬small (p u) := by simp [tag]
  have tag_eq (u v : Fin n) : tag u = tag v ↔ p u = p v := by
    refine ⟨?_, fun h => by simp only [tag, h]⟩
    intro he
    by_cases hu : small (p u)
    · by_cases hv : small (p v)
      · exact tag_eq_of_some (by simpa only [tag, ite_eq_left hu, ite_eq_left hv, Option.some.injEq] using he)
      · simp [tag, hu, hv] at he
    · have hv := (tag_none v).mp (he.symm.trans ((tag_none u).mpr hu))
      exact hFew (p u) (p v) (Nat.lt_of_not_ge hu) (Nat.lt_of_not_ge hv)
  let pos (q : Piece G) (hq : small q) : q.supp ↪ Fin M :=
    (Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card (α := q.supp)).symm).toEmbedding.trans
      (Fin.castLEEmb hq)
  let slot (u : Fin n) : Fin M :=
    if hu : small (p u) then pos (p u) hu ⟨u, rfl⟩ else ⟨0, hM⟩
  let bits (u : Fin n) (i : Fin M) : Bool :=
    decide (∃ v : Fin n, p u = p v ∧ slot v = i ∧ (core G).Adj u v)
  have bits_correct {u v : Fin n} (h : p u = p v) (hv : small (p v)) :
      bits u (slot v) = true ↔ (core G).Adj u v := by
    simp only [bits, decide_eq_true_eq]
    refine ⟨?_, fun hv => ⟨v, h, rfl, hv⟩⟩
    rintro ⟨w, hw, hs, hadj⟩
    have hEq : p w = p v := hw.symm.trans h
    have hw' : small (p w) := hEq.symm ▸ hv
    simp only [slot, dite_eq_left hw', dite_eq_left hv] at hs
    have eqV : w = v := by
      have wmem : w ∈ (p v).supp := hEq
      have hTransport :
          pos (p w) hw' ⟨w, rfl⟩ = pos (p v) hv ⟨w, wmem⟩ := by
        have transport (q₁ q₂ : Piece G) (eq : q₁ = q₂)
            (hq₁ : small q₁) (hq₂ : small q₂) (h₁ : w ∈ q₁.supp) (h₂ : w ∈ q₂.supp) :
            pos q₁ hq₁ ⟨w, h₁⟩ = pos q₂ hq₂ ⟨w, h₂⟩ := by subst q₂; rfl
        exact transport _ _ hEq _ _ _ _
      rw [hTransport] at hs
      exact congrArg Subtype.val ((pos (p v) hv).injective hs)
    exact eqV ▸ hadj
  obtain ⟨b, hb⟩ := bridge_code hn G
  suffices ∃ (big : LayerTypes t m)
    (coord : Fin n → Vertices t m),
    ∀ u v, p u = p v → ¬small (p u) →
      ((core G).Adj u v ↔ (layersGraph (offsetRep t m big)).Adj
        (coord u) (coord v)) by
    obtain ⟨big, coord, hbig⟩ := this
    refine ⟨(tag, slot, big, coord, bits, b), ?_⟩
    intro u v
    dsimp only [decodeAdj]
    have ht : tag u ≠ none ↔ small (p u) := (not_congr (tag_none u)).trans not_not
    rw [← hb u v, tag_eq, ht, tag_none]
    constructor
    · intro huv
      by_cases hbr : G.IsBridge s(u,v)
      · exact Or.inl (bridges_adj.mpr ⟨huv, hbr⟩)
      · have hc := core_adj.mpr ⟨huv, hbr⟩
        have hp : p u = p v := ConnectedComponent.sound hc.reachable
        refine Or.inr ⟨hp, ?_⟩
        by_cases hs : small (p u)
        · exact Or.inr ⟨hs, (bits_correct hp (hp ▸ hs)).mpr hc⟩
        · exact Or.inl ⟨hs, (hbig u v hp hs).mp hc⟩
    · rintro (hbr | ⟨hp, ⟨hs, ha⟩ | ⟨hs, ha⟩⟩)
      · exact bridges_le G hbr
      · exact core_le G ((hbig u v hp hs).mpr ha)
      · exact core_le G ((bits_correct hp (hp ▸ hs)).mp ha)
  by_cases hExists : ∃ q : Piece G, ¬small q
  · obtain ⟨q, hq⟩ := hExists
    have hty := hTypes q (Nat.lt_of_not_ge hq)
    obtain ⟨D, ⟨e⟩⟩ := hty
    let big := offsetType D
    have heq : offsetType (offsetRep t m big) = offsetType D :=
      offsetRep_spec big
    have f : layersGraph (offsetRep t m big) ≃g pieceGraph G q :=
      let eqIso : Nonempty (layersGraph (offsetRep t m big) ≃g
          layersGraph D) := Quotient.exact heq
      eqIso.some.trans e
    have hq' : ∀ u, ¬small (p u) → u ∈ q.supp :=
      fun u hu => hFew (p u) q (Nat.lt_of_not_ge hu) (Nat.lt_of_not_ge hq)
    let base : Vertices t m :=
      (Sum.inl ⟨0, ht⟩, 0)
    let coord (u : Fin n) : Vertices t m :=
      if h : u ∈ q.supp then f.symm ⟨u, h⟩ else base
    refine ⟨big, coord, ?_⟩
    intro u v huv hu
    have huv' := hq' v (huv ▸ hu)
    simp only [coord, dite_eq_left (hq' u hu), dite_eq_left huv']
    exact (core_adj_iff_induced (hq' u hu) huv').trans f.symm.map_rel_iff.symm
  · exact ⟨offsetType (fun _ _ _ => false), fun _ =>
      (Sum.inl ⟨0, ht⟩, 0),
      fun u _ _ hu => (hExists ⟨p u, hu⟩).elim⟩

private theorem competitor_code_card (t m M n : ℕ) [NeZero m]
    (hn : 2 ≤ n) (hMn : M ≤ n) (hkn : 2 * t * m ≤ n) :
    Fintype.card (CompetitorCode t m M n) ≤
      Fintype.card (LayerTypes t m) * (n ^ (7*n) * 2 ^ (M*n)) := by
  classical
  let T := Fintype.card (LayerTypes t m)
  have hs : Fintype.card (Sym2 (Fin n)) ≤ n*n := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using
      Fintype.card_le_of_surjective _ (Sym2.mk_surjective (α := Fin n))
  have htag : n + 1 ≤ n^2 := by nlinarith
  have hbridge : Fintype.card (Sym2 (Fin n)) + 1 ≤ n^3 := by
    calc
      _ ≤ n*n + 1 := by omega
      _ ≤ n*n + n*n := by nlinarith
      _ ≤ n^3 := by
        rw [pow_succ, pow_two]
        simpa only [← two_mul, mul_comm (n*n) 2] using Nat.mul_le_mul_left (n*n) hn
  change Fintype.card (CompetitorCode t m M n) ≤ T * _
  simp only [CompetitorCode, Fintype.card_prod, Fintype.card_fun, Fintype.card_option,
    Fintype.card_fin, Fintype.card_bool, Fintype.card_sum, ZMod.card, ← two_mul t]
  calc
    _ ≤ (n^2)^n * (n^n * (T * (n^n * ((2^M)^n * (n^3)^n)))) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left htag _) <|
      Nat.mul_le_mul (Nat.pow_le_pow_left hMn _) <|
      Nat.mul_le_mul_left T <| Nat.mul_le_mul (Nat.pow_le_pow_left hkn _) <|
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbridge _)
    _ = T * (n ^ (7*n) * 2 ^ (M*n)) := by
      simp only [← pow_mul]
      rw [show 7*n = 2*n + n + n + 3*n by omega, pow_add, pow_add, pow_add]
      ac_rfl

theorem competitor_count (j : ℕ) :
    Nat.card (Competitors j) ≤
      Fintype.card (LayerTypes (stageT (sizeAt j)) (stageM (sizeAt j))) *
        competitorFactor (sizeAt j) := by
  classical
  have code (G : Competitors j) :
      ∃ c : CompetitorCode (stageT (sizeAt j)) (stageM (sizeAt j)) (sizeAt j)
        (stageOrder (sizeAt j)), ∀ u v, G.val.Adj u v ↔ decodeAdj c u v := by
    let M := sizeAt j
    have ht : 0 < stageT M := by have := stageT_large M; omega
    have hM : 0 < M := by have := sizeAt_ge j; omega
    have hn : 0 < stageOrder M := by simp [stageOrder_pow]
    refine exists_competitorCode ht hM hn G.val G.prop.2 ?_
    intro q hq
    exact (piece_size_at G.prop.1 j (by simp) q).resolve_left (not_le.mpr hq)
  let c (G : Competitors j) := Classical.choose (code G)
  have inj : Function.Injective c := by
    intro G H h
    apply Subtype.ext
    ext u v
    have hG := Classical.choose_spec (code G) u v
    have hH := Classical.choose_spec (code H) u v
    change G.val.Adj u v ↔ decodeAdj (c G) u v at hG
    change H.val.Adj u v ↔ decodeAdj (c H) u v at hH
    rw [h] at hG
    exact hG.trans hH.symm
  rw [Nat.card_eq_fintype_card]
  apply (Fintype.card_le_of_injective c inj).trans
  let M := sizeAt j
  let n := stageOrder M
  have hn : 2 ≤ n := by rw [show n = _ from stageOrder_pow M]; exact Nat.le_self_pow (by omega) _
  have hMn : M ≤ n := by have := stageSize_large M; change M ≤ 2 * stageSize M; omega
  have hkn : 2 * stageT M * stageM M ≤ n := by change stageSize M ≤ 2 * stageSize M; omega
  exact competitor_code_card _ _ _ _ hn hMn hkn

end BridgeFragment

#print axioms BridgeFragment.competitor_count
```

### `BridgeFragmentPairs.lean`

```lean
import BridgeFragmentStages
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Basic.Finite.Sum

namespace BridgeFragment

open SimpleGraph

variable {V W V' W' : Type}

theorem same_piece_adj {G : SimpleGraph V} {u v : V} (h : (core G).Reachable u v) :
    (core G).Adj u v ↔ G.Adj u v :=
  core_adj.trans ⟨And.left, fun ha => ⟨ha, same_piece_no_bridge h⟩⟩

/-- Two pieces whose orders add to the ambient order partition the vertices. -/
noncomputable def twoPieceEquiv [Finite V] {G : SimpleGraph V} (p q : Piece G)
    (hpq : p ≠ q) (hcard : Nat.card p.supp + Nat.card q.supp = Nat.card V) :
    p.supp ⊕ q.supp ≃ V := by
  classical
  let f : p.supp ⊕ q.supp → V := Sum.elim Subtype.val Subtype.val
  have hf : Function.Injective f := by
    rintro (a | a) (b | b) hab
    · exact congrArg Sum.inl (Subtype.ext hab)
    · change a.val = b.val at hab
      exact (hpq (p.eq_of_common_vertex a.prop (hab.symm ▸ b.prop))).elim
    · change a.val = b.val at hab
      exact (hpq (p.eq_of_common_vertex (hab.symm ▸ b.prop) a.prop)).elim
    · exact congrArg Sum.inr (Subtype.ext hab)
  let : Fintype (p.supp ⊕ q.supp) := Fintype.ofFinite _
  let : Fintype V := Fintype.ofFinite _
  have hc : Fintype.card (p.supp ⊕ q.supp) = Fintype.card V := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_sum]
    exact hcard
  exact Equiv.ofBijective f ⟨hf, (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hc⟩ |>.2⟩

@[simp] theorem twoPieceEquiv_inl [Finite V] {G : SimpleGraph V} (p q : Piece G)
    (hpq : p ≠ q) (hcard : Nat.card p.supp + Nat.card q.supp = Nat.card V) (a : p.supp) :
    twoPieceEquiv p q hpq hcard (.inl a) = a.val := rfl

@[simp] theorem twoPieceEquiv_inr [Finite V] {G : SimpleGraph V} (p q : Piece G)
    (hpq : p ≠ q) (hcard : Nat.card p.supp + Nat.card q.supp = Nat.card V) (a : q.supp) :
    twoPieceEquiv p q hpq hcard (.inr a) = a.val := rfl

/-- Two graphs placed side by side, with one optional edge between the sides. -/
def pairGraph (G : SimpleGraph V) (H : SimpleGraph W) :
    Option (V × W) → SimpleGraph (V ⊕ W)
  | none => G ⊕g H
  | some (u, v) => (G ⊕g H) ⊔ edge (.inl u) (.inr v)

theorem twoPiece_pairGraph [Finite V] {G : SimpleGraph V} (p q : Piece G)
    (hpq : p ≠ q) (hcard : Nat.card p.supp + Nat.card q.supp = Nat.card V) :
    ∃ o, Nonempty (pairGraph (pieceGraph G p) (pieceGraph G q) o ≃g G) := by
  classical
  let e := twoPieceEquiv p q hpq hcard
  have disjoint (a : p.supp) (b : q.supp) : a.val ≠ b.val :=
    fun eq => hpq (ConnectedComponent.eq_of_common_vertex a.prop (eq.symm ▸ b.prop))
  have crossBridge (a : p.supp) (b : q.supp) (hab : G.Adj a.val b.val) :
      (bridges G).Adj a.val b.val := by
    refine bridges_adj.mpr ⟨hab, ?_⟩
    by_contra h
    exact hpq (a.prop.symm.trans ((ConnectedComponent.sound
      (core_adj.mpr ⟨hab, h⟩).reachable).trans b.prop))
  have crossUnique (a : p.supp) (b : q.supp) (hab : G.Adj a.val b.val)
      (x : p.supp) (y : q.supp) :
      G.Adj x.val y.val ↔ x = a ∧ y = b := by
    constructor
    · intro hxy
      have eq := bridge_cross_unique (p.reachable_of_mem_supp a.prop x.prop)
        (q.reachable_of_mem_supp b.prop y.prop) (crossBridge a b hab) hxy
      rcases Sym2.eq_iff.mp eq with ⟨ha, hb⟩ | ⟨ha, _⟩
      · exact ⟨Subtype.ext ha.symm, Subtype.ext hb.symm⟩
      · exact (disjoint a y ha).elim
    · rintro ⟨rfl, rfl⟩
      exact hab
  have local_l (a b : p.supp) : G.Adj a.val b.val ↔ (pieceGraph G p).Adj a b :=
    (same_piece_adj (p.reachable_of_mem_supp a.prop b.prop)).symm
  have local_r (a b : q.supp) : G.Adj a.val b.val ↔ (pieceGraph G q).Adj a b :=
    (same_piece_adj (q.reachable_of_mem_supp a.prop b.prop)).symm
  by_cases h : ∃ (a : p.supp) (b : q.supp), G.Adj a.val b.val
  · obtain ⟨a, b, hab⟩ := h
    refine ⟨some (a, b), ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩⟩
    rintro (x|x) (y|y)
    · simpa [e, pairGraph, sup_adj, edge_adj] using local_l x y
    · simpa [e, pairGraph, sup_adj, edge_adj] using crossUnique a b hab x y
    · simpa [e, pairGraph, sup_adj, edge_adj, and_comm, adj_comm (G := G)] using
        crossUnique a b hab y x
    · simpa [e, pairGraph, sup_adj, edge_adj] using local_r x y
  · push Not at h
    refine ⟨none, ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩⟩
    rintro (x|x) (y|y)
    · exact local_l x y
    · simpa [e, pairGraph] using iff_false_intro (h x y)
    · simpa [e, pairGraph] using
        iff_false_intro (fun hxy : G.Adj x.val y.val => h y x hxy.symm)
    · exact local_r x y

def supEdgeIso {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (u v : V) :
    (G ⊔ edge u v) ≃g (H ⊔ edge (e u) (e v)) where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro a b
    change (H ⊔ edge (e u) (e v)).Adj (e a) (e b) ↔ (G ⊔ edge u v).Adj a b
    simp only [sup_adj, e.map_rel_iff, edge_adj, e.injective.eq_iff, ne_eq]

theorem sum_mk_inl_ne_inr (G : SimpleGraph V) (H : SimpleGraph W) (u : V) (v : W) :
    (G ⊕g H).connectedComponentMk (.inl u) ≠ (G ⊕g H).connectedComponentMk (.inr v) :=
  fun h => not_reachable_sum_inl_inr u v (ConnectedComponent.exact h)

theorem sum_mk_inl_eq (G : SimpleGraph V) (H : SimpleGraph W) (hG : G.Preconnected) (u v : V) :
    (G ⊕g H).connectedComponentMk (.inl u) = (G ⊕g H).connectedComponentMk (.inl v) :=
  ConnectedComponent.sound ((hG u v).map
    (Embedding.sumInl (G := G) (H := H)).toHom)

theorem sum_mk_inr_eq (G : SimpleGraph V) (H : SimpleGraph W) (hH : H.Preconnected) (u v : W) :
    (G ⊕g H).connectedComponentMk (.inr u) = (G ⊕g H).connectedComponentMk (.inr v) :=
  ConnectedComponent.sound ((hH u v).map
    (Embedding.sumInr (G := G) (H := H)).toHom)

def sumLeftIso {G : SimpleGraph V} {H : SimpleGraph W} (hG : G.Preconnected) (u : V) :
    G ≃g ((G ⊕g H).connectedComponentMk (.inl u)).toSimpleGraph where
  toEquiv := {
    toFun := fun v => ⟨.inl v, sum_mk_inl_eq G H hG v u⟩
    invFun := fun
      | ⟨.inl a, _⟩ => a
      | ⟨.inr b, h⟩ => (sum_mk_inl_ne_inr G H u b h.symm).elim
    left_inv := fun _ => rfl
    right_inv := by
      rintro ⟨a | b, ha⟩
      · rfl
      · exact (sum_mk_inl_ne_inr G H u b ha.symm).elim }
  map_rel_iff' := Iff.rfl

def sumRightIso {G : SimpleGraph V} {H : SimpleGraph W} (hH : H.Preconnected) (u : W) :
    H ≃g ((G ⊕g H).connectedComponentMk (.inr u)).toSimpleGraph where
  toEquiv := {
    toFun := fun v => ⟨.inr v, sum_mk_inr_eq G H hH v u⟩
    invFun := fun
      | ⟨.inl a, h⟩ => (sum_mk_inl_ne_inr G H a u h).elim
      | ⟨.inr b, _⟩ => b
    left_inv := fun _ => rfl
    right_inv := by
      rintro ⟨a | b, ha⟩
      · exact (sum_mk_inl_ne_inr G H a u ha).elim
      · rfl }
  map_rel_iff' := Iff.rfl

theorem core_sum_of_core_eq {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : core G = G) (hH : core H = H) : core (G ⊕g H) = G ⊕g H := by
  have l : ∀ a b, G.Adj a b → (core (G ⊕g H)).Adj (.inl a) (.inl b) := by
    intro a b hab
    refine core_adj.mpr ⟨hab, ?_⟩
    intro hb
    have ha : (core G).Adj a b := hG.symm ▸ hab
    apply (core_adj.mp ha).2
    rw [isBridge_iff] at hb ⊢
    let f : G.deleteEdges {s(a, b)} →g
        (G ⊕g H).deleteEdges {s(.inl a, .inl b)} :=
      { toFun := Sum.inl
        map_rel' := by
          intro u v huv
          have he := deleteEdges_adj.mp huv
          exact deleteEdges_adj.mpr ⟨he.1, by
            simpa only [Set.mem_singleton_iff, Sym2.eq_iff, Sum.inl.injEq] using he.2⟩ }
    exact fun h => hb (h.map f)
  have r : ∀ a b, H.Adj a b → (core (G ⊕g H)).Adj (.inr a) (.inr b) := by
    intro a b hab
    refine core_adj.mpr ⟨hab, ?_⟩
    intro hb
    have ha : (core H).Adj a b := hH.symm ▸ hab
    apply (core_adj.mp ha).2
    rw [isBridge_iff] at hb ⊢
    let f : H.deleteEdges {s(a, b)} →g
        (G ⊕g H).deleteEdges {s(.inr a, .inr b)} :=
      { toFun := Sum.inr
        map_rel' := by
          intro u v huv
          have he := deleteEdges_adj.mp huv
          exact deleteEdges_adj.mpr ⟨he.1, by
            simpa only [Set.mem_singleton_iff, Sym2.eq_iff, Sum.inr.injEq] using he.2⟩ }
    exact fun h => hb (h.map f)
  apply le_antisymm (core_le _)
  rintro (a|a) (b|b)
  · exact l a b
  · exact fun h => (not_adj_sum_inl_inr a b h).elim
  · exact fun h => (not_adj_sum_inl_inr b a h.symm).elim
  · exact r a b

theorem largestComponent_sum [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : G.Connected) (hH : H.Connected) :
    largestComponent (G ⊕g H) = max (Nat.card V) (Nat.card W) := by
  classical
  let : Fintype (G ⊕g H).ConnectedComponent := Fintype.ofFinite _
  have eqL (u : V) :
      Nat.card ((G ⊕g H).connectedComponentMk (.inl u)).supp = Nat.card V :=
    (Nat.card_congr (sumLeftIso hG.preconnected u).toEquiv).symm
  have eqR (v : W) :
      Nat.card ((G ⊕g H).connectedComponentMk (.inr v)).supp = Nat.card W :=
    (Nat.card_congr (sumRightIso hH.preconnected v).toEquiv).symm
  change Finset.univ.sup (fun c : (G ⊕g H).ConnectedComponent => Nat.card c.supp) = _
  apply le_antisymm
  · apply Finset.sup_le
    intro c _
    induction c using ConnectedComponent.ind with
    | _ x =>
      cases x with
      | inl u => rw [eqL]; exact le_max_left _ _
      | inr v => rw [eqR]; exact le_max_right _ _
  · obtain ⟨u⟩ := hG.nonempty
    obtain ⟨v⟩ := hH.nonempty
    apply max_le
    · rw [← eqL u]
      exact Finset.le_sup (f := fun c => Nat.card ((c : (G ⊕g H).ConnectedComponent).supp))
        (Finset.mem_univ ((G ⊕g H).connectedComponentMk (.inl u)))
    · rw [← eqR v]
      exact Finset.le_sup (f := fun c => Nat.card ((c : (G ⊕g H).ConnectedComponent).supp))
        (Finset.mem_univ ((G ⊕g H).connectedComponentMk (.inr v)))

end BridgeFragment

#print axioms BridgeFragment.twoPiece_pairGraph
#print axioms BridgeFragment.largestComponent_sum
```

### `BridgeFragmentPairTypes.lean`

```lean
import BridgeFragmentPairs

namespace BridgeFragment

open SimpleGraph

set_option maxHeartbeats 450000

abbrev PairCode (t m : ℕ) :=
  LayerTypes t m × LayerTypes t m × Option (Layers t × Layers t)

private def endpoints {t m : ℕ} (o : Option (Layers t × Layers t)) :
    Option (Vertices t m × Vertices t m) :=
  o.map fun (i, j) => ((i, 0), (j, 0))

noncomputable def codedPair {t m : ℕ} [NeZero m] (c : PairCode t m) :
    SimpleGraph (Vertices t m ⊕ Vertices t m) :=
  pairGraph (layersGraph (offsetRep t m c.1)) (layersGraph (offsetRep t m c.2.1))
    (endpoints c.2.2)

private theorem allowed_sum {V W : Type} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (hg : G.Preconnected) (hh : H.Preconnected) (hG : core G = G) (hH : core H = H)
    (g : allowedPieces.mem G) (h : allowedPieces.mem H) : witness.mem (G ⊕g H) := by
  change ∀ p : (core (G ⊕g H)).ConnectedComponent, allowedPieces.mem p.toSimpleGraph
  rw [core_sum_of_core_eq hG hH]
  intro p
  induction p using ConnectedComponent.ind with
  | _ x =>
    cases x with
    | inl u => exact (allowedPieces.iso (sumLeftIso hg u)).mp g
    | inr v => exact (allowedPieces.iso (sumRightIso hh v)).mp h

private theorem pairGraph_mem {V W : Type} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (base : witness.mem (G ⊕g H))
    (o : Option (V × W)) : witness.mem (pairGraph G H o) := by
  cases o with
  | none => exact base
  | some uv => exact witness_bridgeAddable _ _ _ base (not_reachable_sum_inl_inr uv.1 uv.2)

private theorem codedPair_mem_of_allowed {t m : ℕ} [NeZero m] (hm : 2 < m)
    (c : PairCode t m) (g : allowedPieces.mem (layersGraph (offsetRep t m c.1)))
    (h : allowedPieces.mem (layersGraph (offsetRep t m c.2.1))) : witness.mem (codedPair c) := by
  let D := offsetRep t m c.1
  let E := offsetRep t m c.2.1
  have base : witness.mem (layersGraph D ⊕g layersGraph E) :=
    allowed_sum (layers_preconnected D) (layers_preconnected E)
      (layers_core D hm) (layers_core E hm) g h
  exact pairGraph_mem base (endpoints c.2.2)

private theorem allowedLayer (j : ℕ) (D : Offsets (stageT (sizeAt j)) (stageM (sizeAt j))) :
    allowedPieces.mem (layersGraph D) := by
  right
  exact ⟨j, D, ⟨SimpleGraph.Iso.refl⟩⟩

theorem codedPair_member (j : ℕ) (c : PairCode (stageT (sizeAt j)) (stageM (sizeAt j))) :
    witness.mem (codedPair c) :=
  codedPair_mem_of_allowed (stageM_large (sizeAt j)) c (allowedLayer j _) (allowedLayer j _)

private theorem canonicalLayerIso {t m : ℕ} [NeZero m] {V : Type} {G : SimpleGraph V}
    (h : IsLayerType t m G) : ∃ q : LayerTypes t m,
      Nonempty (layersGraph (offsetRep t m q) ≃g G) := by
  obtain ⟨D, ⟨e⟩⟩ := h
  let q := offsetType D
  have h' : offsetType (offsetRep t m q) = offsetType D := offsetRep_spec q
  let e' : Nonempty (layersGraph (offsetRep t m q) ≃g layersGraph D) := Quotient.exact h'
  exact ⟨q, ⟨e'.some.trans e⟩⟩

theorem twoLayerPieces_coded {V : Type} [Finite V] {t m : ℕ} [NeZero m]
    {G : SimpleGraph V} {p q : Piece G} (hpq : p ≠ q)
    (hcard : Nat.card p.supp + Nat.card q.supp = Nat.card V)
    (hp : IsLayerType t m (pieceGraph G p)) (hq : IsLayerType t m (pieceGraph G q)) :
    ∃ c : PairCode t m, Nonempty (codedPair c ≃g G) := by
  obtain ⟨a, ⟨ea⟩⟩ := canonicalLayerIso hp
  obtain ⟨b, ⟨eb⟩⟩ := canonicalLayerIso hq
  obtain ⟨o, ⟨e⟩⟩ := twoPiece_pairGraph p q hpq hcard
  cases o with
  | none => exact ⟨(a, b, none), ⟨(ea.sumCongr eb).trans e⟩⟩
  | some uv =>
    let x := ea.symm uv.1
    let y := eb.symm uv.2
    let f : pieceGraph G p ≃g layersGraph (offsetRep t m a) :=
      ea.symm.trans (shiftIso (offsetRep t m a) (-x.2))
    let g : pieceGraph G q ≃g layersGraph (offsetRep t m b) :=
      eb.symm.trans (shiftIso (offsetRep t m b) (-y.2))
    let c : PairCode t m := (a, b, some (x.1, y.1))
    let e' := supEdgeIso (f.sumCongr g) (Sum.inl uv.1) (Sum.inr uv.2)
    have hx : (f.sumCongr g) (.inl uv.1) = Sum.inl (x.1, 0) := by
      change Sum.inl (shiftIso _ (-x.2) x) = _
      rw [shift_to_zero]
    have hy : (f.sumCongr g) (.inr uv.2) = Sum.inr (y.1, 0) := by
      change Sum.inr (shiftIso _ (-y.2) y) = _
      rw [shift_to_zero]
    refine ⟨c, ⟨?_⟩⟩
    have iso : pairGraph (pieceGraph G p) (pieceGraph G q) (some uv) ≃g codedPair c := by
      change ((pieceGraph G p ⊕g pieceGraph G q) ⊔ edge (.inl uv.1) (.inr uv.2)) ≃g
        ((layersGraph (offsetRep t m a) ⊕g layersGraph (offsetRep t m b)) ⊔
          edge (.inl (x.1, 0)) (.inr (y.1, 0)))
      rw [← hx, ← hy]
      exact e'
    exact iso.symm.trans e

noncomputable def stageEquiv (t m n : ℕ) [NeZero m] (h : 2 * (2 * t * m) = n) :
    Vertices t m ⊕ Vertices t m ≃ Fin n :=
  Fintype.equivFinOfCardEq (by simp only [Fintype.card_sum, card_vertices, ← two_mul, h])

noncomputable def pairType (j : ℕ) (c : PairCode (stageT (sizeAt j)) (stageM (sizeAt j))) :
    UnlabelledMembers witness (stageOrder (sizeAt j)) :=
  let e := stageEquiv (stageT (sizeAt j)) (stageM (sizeAt j)) (stageOrder (sizeAt j)) rfl
  Quotient.mk _ ⟨(codedPair c).map e, (witness.iso (Iso.map e (codedPair c))).mp
    (codedPair_member j c)⟩

theorem pairType_cover (j : ℕ) {G : SimpleGraph (Fin (stageOrder (sizeAt j)))}
    (hG : witness.mem G) {p q : Piece G} (hpq : p ≠ q)
    (hp : sizeAt j < Nat.card p.supp) (hq : sizeAt j < Nat.card q.supp) :
    ∃ c, pairType j c = Quotient.mk _ ⟨G, hG⟩ := by
  have hn : Nat.card (Fin (stageOrder (sizeAt j))) = stageOrder (sizeAt j) := by simp
  have h' := (piece_size_at hG j hn p).resolve_left (not_le.mpr hp)
  have h'' := (piece_size_at hG j hn q).resolve_left (not_le.mpr hq)
  have he₁ := layerOrder h'
  have he₂ := layerOrder h''
  have hcard : Nat.card p.supp + Nat.card q.supp = Nat.card (Fin (stageOrder (sizeAt j))) := by
    rw [he₁, he₂, hn, stageOrder, stageSize]
    omega
  obtain ⟨c, ⟨e⟩⟩ := twoLayerPieces_coded hpq hcard h' h''
  refine ⟨c, Quotient.sound ?_⟩
  change Nonempty ((codedPair c).map _ ≃g G)
  exact ⟨(Iso.map (stageEquiv _ _ _ rfl) (codedPair c)).symm.trans e⟩

theorem pairType_frag (j : ℕ) (a b : LayerTypes (stageT (sizeAt j)) (stageM (sizeAt j))) :
    fragType witness (stageOrder (sizeAt j)) (pairType j (a, b, none)) = stageSize (sizeAt j) := by
  let M := sizeAt j
  let t := stageT M
  let m := stageM M
  let D := offsetRep t m a
  let E := offsetRep t m b
  let e := stageEquiv t m (stageOrder M) rfl
  change stageOrder M - largestComponent ((layersGraph D ⊕g layersGraph E).map e) = _
  have ht : 0 < t := by have := stageT_large M; omega
  rw [← largestComponent_iso (Iso.map e _),
    largestComponent_sum (layers_connected D ht) (layers_connected E ht), max_self,
    Nat.card_eq_fintype_card, card_vertices]
  change 2 * stageSize M - stageSize M = stageSize M
  omega

end BridgeFragment

#print axioms BridgeFragment.pairType_cover
#print axioms BridgeFragment.pairType_frag
```

### `BridgeFragmentUnionCount.lean`

```lean
import BridgeFragmentPairTypes

namespace BridgeFragment

open SimpleGraph

private theorem sum_parts_iso {V : Type} {G H G' H' : SimpleGraph V} (v : V)
    (g : G.Preconnected) (h : H.Preconnected) (g' : G'.Preconnected) (h' : H'.Preconnected)
    (e : G ⊕g H ≃g G' ⊕g H') :
    (Nonempty (G ≃g G') ∧ Nonempty (H ≃g H')) ∨
      (Nonempty (G ≃g H') ∧ Nonempty (H ≃g G')) := by
  have part (u : V ⊕ V) :
      ((G ⊕g H).connectedComponentMk u).toSimpleGraph ≃g
        ((G' ⊕g H').connectedComponentMk (e u)).toSimpleGraph :=
    componentIso e _
  have side_eq : ∀ (u w : V ⊕ V),
      (G' ⊕g H').connectedComponentMk (e u) = (G' ⊕g H').connectedComponentMk (e w) →
        (G ⊕g H).connectedComponentMk u = (G ⊕g H).connectedComponentMk w :=
    fun _ _ eq => e.connectedComponentEquiv.injective eq
  cases el : e (Sum.inl v) with
  | inl l =>
    have iso₁ := part (.inl v)
    rw [el] at iso₁
    cases er : e (Sum.inr v) with
    | inl r =>
      have eq := sum_mk_inl_eq G' H' g' l r
      rw [← el, ← er] at eq
      exact (sum_mk_inl_ne_inr G H v v (side_eq _ _ eq)).elim
    | inr r =>
      have iso₂ := part (.inr v)
      rw [er] at iso₂
      exact Or.inl ⟨⟨(sumLeftIso g v).trans (iso₁.trans (sumLeftIso g' l).symm)⟩,
        ⟨(sumRightIso h v).trans (iso₂.trans (sumRightIso h' r).symm)⟩⟩
  | inr l =>
    have iso₁ := part (.inl v)
    rw [el] at iso₁
    cases er : e (Sum.inr v) with
    | inl r =>
      have iso₂ := part (.inr v)
      rw [er] at iso₂
      exact Or.inr ⟨⟨(sumLeftIso g v).trans (iso₁.trans (sumRightIso h' l).symm)⟩,
        ⟨(sumRightIso h v).trans (iso₂.trans (sumLeftIso g' r).symm)⟩⟩
    | inr r =>
      have eq := sum_mk_inr_eq G' H' h' l r
      rw [← el, ← er] at eq
      exact (sum_mk_inl_ne_inr G H v v (side_eq _ _ eq)).elim

private theorem disjoint_code_recovery {t m : ℕ} [NeZero m] (ht : 0 < t)
    (x y : LayerTypes t m × LayerTypes t m)
    (f : (layersGraph (offsetRep t m x.1) ⊕g layersGraph (offsetRep t m x.2)) ≃g
      (layersGraph (offsetRep t m y.1) ⊕g layersGraph (offsetRep t m y.2))) :
    x = y ∨ x = y.swap := by
  let v : Vertices t m := (Sum.inl ⟨0, ht⟩, 0)
  rcases sum_parts_iso v (layers_preconnected _) (layers_preconnected _)
    (layers_preconnected _) (layers_preconnected _) f with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · left
    apply Prod.ext
    · have he : offsetType (offsetRep t m x.1) = offsetType (offsetRep t m y.1) :=
        Quotient.sound h₁
      simpa only [offsetRep_spec] using he
    · have he : offsetType (offsetRep t m x.2) = offsetType (offsetRep t m y.2) :=
        Quotient.sound h₂
      simpa only [offsetRep_spec] using he
  · right
    apply Prod.ext
    · have he : offsetType (offsetRep t m x.1) = offsetType (offsetRep t m y.2) :=
        Quotient.sound h₁
      simpa only [offsetRep_spec, Prod.swap] using he
    · have he : offsetType (offsetRep t m x.2) = offsetType (offsetRep t m y.1) :=
        Quotient.sound h₂
      simpa only [offsetRep_spec, Prod.swap] using he

theorem union_pair_eq_or_swap (j : ℕ)
    (x y : LayerTypes (stageT (sizeAt j)) (stageM (sizeAt j)) ×
      LayerTypes (stageT (sizeAt j)) (stageM (sizeAt j)))
    (h : pairType j (x.1, x.2, none) = pairType j (y.1, y.2, none)) :
    x = y ∨ x = y.swap := by
  let M := sizeAt j
  let t := stageT M
  let m := stageM M
  let e := stageEquiv t m (stageOrder M) rfl
  let G := layersGraph (offsetRep t m x.1) ⊕g layersGraph (offsetRep t m x.2)
  let H := layersGraph (offsetRep t m y.1) ⊕g layersGraph (offsetRep t m y.2)
  have iso : Nonempty (G.map e ≃g H.map e) := Quotient.exact h
  let f : G ≃g H := (Iso.map e G).trans (iso.some.trans (Iso.map e H).symm)
  have ht : 0 < t := by have := stageT_large M; omega
  exact disjoint_code_recovery ht x y f

abbrev OrderedPairs (j : ℕ) :=
  LayerTypes (stageT (sizeAt j)) (stageM (sizeAt j)) ×
    LayerTypes (stageT (sizeAt j)) (stageM (sizeAt j))

noncomputable def unionType (j : ℕ) (x : OrderedPairs j) :=
  pairType j (x.1, x.2, none)

abbrev UnionTypes (j : ℕ) := Set.range (unionType j)

noncomputable instance (j : ℕ) : Fintype (UnionTypes j) := Fintype.ofFinite _

theorem unionType_card (j : ℕ) : Fintype.card (OrderedPairs j) ≤ 2 * Fintype.card (UnionTypes j) := by
  classical
  let f (x : OrderedPairs j) : UnionTypes j := ⟨unionType j x, x, rfl⟩
  have hf (b : UnionTypes j) : Nat.card {a // f a = b} ≤ 2 := by
    obtain ⟨x, hx⟩ := b.prop
    have ex (y : {a // f a = b}) : y.val = x ∨ y.val = x.swap :=
      union_pair_eq_or_swap j y.val x ((congrArg Subtype.val y.prop).trans hx.symm)
    let g (y : {a // f a = b}) : Bool := decide (y.val = x)
    have inj : Function.Injective g := by
      intro u v eq
      apply Subtype.ext
      have h : u.val = x ↔ v.val = x := by
        change decide (u.val = x) = decide (v.val = x) at eq
        exact ⟨fun h => of_decide_eq_true (eq.symm.trans (decide_eq_true h)),
          fun h => of_decide_eq_true (eq.trans (decide_eq_true h))⟩
      by_cases hu : u.val = x
      · exact hu.trans (h.mp hu).symm
      · exact ((ex u).resolve_left hu).trans ((ex v).resolve_left (mt h.mpr hu)).symm
    simpa only [Nat.card_eq_fintype_card, Fintype.card_bool] using
      Fintype.card_le_of_injective g inj
  exact (card_le_mul_of_fibres f 2 hf).trans_eq (Nat.mul_comm _ _)

theorem unionType_frag (j : ℕ) (q : UnionTypes j) :
    fragType witness (stageOrder (sizeAt j)) q.val = stageSize (sizeAt j) := by
  obtain ⟨x, hx⟩ := q.prop
  rw [← hx]
  exact pairType_frag j _ _

end BridgeFragment

#print axioms BridgeFragment.unionType_card
#print axioms BridgeFragment.unionType_frag
```

### `BridgeFragmentCounterexample.lean`

```lean
import BridgeFragmentCompetitors
import BridgeFragmentUnionCount
import Mathlib.Algebra.Order.Archimedean.Basic

namespace BridgeFragment

open SimpleGraph

private theorem pairCode_card {t m : ℕ} [NeZero m] :
    Fintype.card (PairCode t m) =
      Fintype.card (LayerTypes t m) * Fintype.card (LayerTypes t m) *
        ((2 * t) ^ 2 + 1) := by
  simp only [PairCode, Fintype.card_prod, Fintype.card_option, Fintype.card_sum,
    Fintype.card_fin, two_mul, pow_two, mul_assoc]

theorem observation_count (j : ℕ) :
    Fintype.card (UnlabelledMembers witness (stageOrder (sizeAt j))) ≤
      Fintype.card (LayerTypes (stageT (sizeAt j)) (stageM (sizeAt j))) ^ 2 *
        ((2 * stageT (sizeAt j)) ^ 2 + 2) := by
  classical
  let M := sizeAt j
  let n := stageOrder M
  let B := PairCode (stageT M) (stageM M)
  let T := Fintype.card (LayerTypes (stageT M) (stageM M))
  let f : Competitors j ⊕ B → UnlabelledMembers witness n :=
    Sum.elim (fun G => Quotient.mk _ ⟨G.val, G.prop.1⟩) (pairType j)
  have surj : Function.Surjective f := by
    intro q
    induction q using Quotient.ind with
    | _ G =>
      by_cases h : FewBig G.val M
      · exact ⟨.inl ⟨G.val, G.prop, h⟩, rfl⟩
      · unfold FewBig at h
        push Not at h
        obtain ⟨p, q, hp, hq, hpq⟩ := h
        obtain ⟨c, hc⟩ := pairType_cover j G.prop hpq hp hq
        exact ⟨.inr c, hc⟩
  have hcover := Fintype.card_le_of_surjective f surj
  rw [Fintype.card_sum, ← Nat.card_eq_fintype_card (α := Competitors j), pairCode_card] at hcover
  change _ ≤ T ^ 2 * ((2 * stageT M) ^ 2 + 2)
  calc
    _ ≤ Nat.card (Competitors j) + T * T * ((2 * stageT M) ^ 2 + 1) := hcover
    _ ≤ T * competitorFactor M + T * T * ((2 * stageT M) ^ 2 + 1) :=
      Nat.add_le_add_right (competitor_count j) _
    _ ≤ T * T + T * T * ((2 * stageT M) ^ 2 + 1) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ (competitorFactor_le M)) _
    _ = _ := by ring

/-- If at most T²B outcomes exist and at least T²/2 of them contribute k,
the average is at least k/(2B). -/
private theorem finite_mean_bound {α : Type} [Fintype α] [Nonempty α] (S : Set α)
    [Fintype S] (f : α → ℕ) {T B k : ℕ}
    (hT : 0 < T) (hB : 0 < B)
    (hcard : Fintype.card α ≤ T^2 * B) (hS : T^2 ≤ 2 * Fintype.card S)
    (hf : ∀ q : S, f q.val = k) :
    (k : ℚ) / (2 * (B : ℚ)) ≤ (∑ q : α, (f q : ℚ)) / Fintype.card α := by
  classical
  let N := Fintype.card α
  let D := Fintype.card S
  let sum : ℚ := ∑ q : α, (f q : ℚ)
  let μ : ℚ := sum / N
  have hN : (0 : ℚ) < N := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card α)
  have hB' : (0 : ℚ) < 2 * (B : ℚ) := by positivity
  have hT' : (0 : ℚ) < (T : ℚ)^2 := by positivity
  have hμ : 0 ≤ μ := div_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) hN.le
  have hAll : (N : ℚ) ≤ (T : ℚ)^2 * B := by exact_mod_cast hcard
  have hDis : (T : ℚ)^2 ≤ 2 * (D : ℚ) := by exact_mod_cast hS
  have hsum : (D : ℚ) * k ≤ sum := calc
    _ = ∑ q : S, (f q.val : ℚ) := by
      simp only [hf, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, D]
    _ = ∑ q ∈ S.toFinset, (f q : ℚ) := Finset.sum_set_coe (f := fun q => (f q : ℚ)) S
    _ ≤ sum := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ =>
      Nat.cast_nonneg _
  have hs : μ * N = sum := div_mul_cancel₀ _ hN.ne'
  change (k : ℚ) / (2 * (B : ℚ)) ≤ μ
  apply (div_le_iff₀ hB').mpr
  apply le_of_mul_le_mul_right _ hT'
  calc
    (k : ℚ) * (T : ℚ)^2 ≤ k * (2 * (D : ℚ)) :=
      mul_le_mul_of_nonneg_left hDis (Nat.cast_nonneg _)
    _ = 2 * ((D : ℚ) * k) := by ring
    _ ≤ 2 * sum := mul_le_mul_of_nonneg_left hsum (by decide)
    _ = 2 * (μ * N) := by rw [hs]
    _ ≤ 2 * (μ * ((T : ℚ)^2 * B)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAll hμ) (by decide)
    _ = (μ * (2 * (B : ℚ))) * (T : ℚ)^2 := by ring

private theorem observation_ratio (t : ℕ) (ht : 2 ≤ t) :
    (t : ℚ)^2 / 6 ≤ ((2 * t * t^3 : ℕ) : ℚ) / (2 * (((2*t)^2 + 2 : ℕ) : ℚ)) := by
  let B := (2*t)^2 + 2
  have hB : 0 < B := by dsimp only [B]; omega
  have ht' : (2 : ℚ) ≤ t := by exact_mod_cast ht
  have hB' : (0 : ℚ) < 2 * (B : ℚ) := by positivity
  have hBounds : (2 : ℚ) * (B : ℚ) ≤ 12 * (t : ℚ)^2 := by
    dsimp only [B]
    push_cast
    nlinarith
  have hk : ((2 * t * t^3 : ℕ) : ℚ) = 2 * (t : ℚ)^4 := by
    push_cast
    ring
  apply (le_div_iff₀ hB').mpr
  calc
    (t : ℚ)^2 / 6 * (2 * (B : ℚ)) ≤ (t : ℚ)^2 / 6 * (12 * (t : ℚ)^2) :=
      mul_le_mul_of_nonneg_left hBounds (by positivity)
    _ = ((2 * t * t^3 : ℕ) : ℚ) := by rw [hk]; ring

theorem observation_mean (j : ℕ) :
    (stageT (sizeAt j) : ℚ)^2 / 6 ≤ meanFrag witness (stageOrder (sizeAt j)) := by
  let M := sizeAt j
  let t := stageT M
  let T := Fintype.card (LayerTypes t (stageM M))
  let B := (2*t)^2+2
  let k := stageSize M
  let n := stageOrder M
  let : Nonempty (UnlabelledMembers witness n) := witness_nonempty n
  have hT : 0 < T := Fintype.card_pos_iff.mpr ⟨offsetType (fun _ _ _ => false)⟩
  have hB : 0 < B := by dsimp only [B]; omega
  have hS : T^2 ≤ 2 * Fintype.card (UnionTypes j) := by
    simpa only [OrderedPairs, Fintype.card_prod, pow_two] using unionType_card j
  have hmean : (k : ℚ) / (2 * (B : ℚ)) ≤ meanFrag witness n :=
    finite_mean_bound (Set.range (unionType j)) (fragType witness n) hT hB
      (observation_count j) hS (unionType_frag j)
  have ht : 2 ≤ t := by have := stageT_large M; omega
  exact (observation_ratio t ht).trans hmean

private theorem lt_square_six (c : ℚ) (j t : ℕ) (hj : 6*c < j) (hjt : j ≤ t)
    (ht : 1 ≤ t) : c < (t : ℚ)^2 / 6 := by
  have hjt' : (j : ℚ) ≤ t := by exact_mod_cast hjt
  have ht' : (1 : ℚ) ≤ t := by exact_mod_cast ht
  have hsq : (t : ℚ) ≤ (t : ℚ)^2 := by nlinarith
  exact (lt_div_iff₀ (by decide : (0 : ℚ) < 6)).mpr
    (by rw [mul_comm]; exact hj.trans_le (hjt'.trans hsq))

theorem witness_unbounded (c : ℚ) :
    ∃ n : ℕ, 0 < n ∧ c < meanFrag witness n := by
  obtain ⟨j, hj⟩ := exists_nat_gt (6 * c)
  let M := sizeAt j
  let t := stageT M
  have hjt : j ≤ t := by
    have h := sizeAt_ge j
    have h' := stageT_large M
    change j + 1 ≤ M at h
    change M + 4 ≤ t at h'
    omega
  have ht : 1 ≤ t := by have := stageT_large M; omega
  have hn : 0 < stageOrder M := (stageOrder_pow M).symm ▸ (Nat.pow_pos (by decide))
  exact ⟨stageOrder M, hn, (lt_square_six c j t hj hjt ht).trans_le (observation_mean j)⟩

theorem mathdb_345190 :
    ∃ A : GClass, Decomposable A ∧ BridgeAddable A ∧
      (∀ n : ℕ, 0 < n → Nonempty (UnlabelledMembers A n)) ∧
      ¬ ∃ c : ℚ, ∀ n : ℕ, 0 < n → meanFrag A n ≤ c := by
  refine ⟨witness, witness_decomposable, witness_bridgeAddable, fun n _ => witness_nonempty n, ?_⟩
  rintro ⟨c, hc⟩
  obtain ⟨n, hn, h⟩ := witness_unbounded c
  exact (not_le.mpr h) (hc n hn)

end BridgeFragment

#print axioms BridgeFragment.observation_count
#print axioms BridgeFragment.observation_mean
#print axioms BridgeFragment.witness_unbounded
#print axioms BridgeFragment.mathdb_345190
```

### `BridgeFragmentReal.lean`

```lean
import BridgeFragmentCounterexample
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace BridgeFragment

/-- The same uniform expectation, evaluated in the real numbers. -/
noncomputable def meanFragReal (A : GClass) (n : ℕ) : ℝ :=
  (∑ q : UnlabelledMembers A n, (fragType A n q : ℝ)) / Fintype.card (UnlabelledMembers A n)

theorem meanFragReal_eq (A : GClass) (n : ℕ) :
    meanFragReal A n = (meanFrag A n : ℝ) := by
  simp only [meanFragReal, meanFrag, Rat.cast_div, Rat.cast_sum, Rat.cast_natCast]

theorem mathdb_345190_real :
    ∃ A : GClass, Decomposable A ∧ BridgeAddable A ∧
      (∀ n : ℕ, 0 < n → Nonempty (UnlabelledMembers A n)) ∧
      ¬ ∃ c : ℝ, ∀ n : ℕ, 0 < n → meanFragReal A n ≤ c := by
  refine ⟨witness, witness_decomposable, witness_bridgeAddable, fun n _ => witness_nonempty n, ?_⟩
  rintro ⟨c, hc⟩
  obtain ⟨k, hk⟩ := exists_nat_gt c
  obtain ⟨n, hn, h⟩ := witness_unbounded (k : ℚ)
  have h' : (k : ℝ) < (meanFrag witness n : ℝ) := by exact_mod_cast h
  rw [← meanFragReal_eq] at h'
  exact (not_le.mpr (hk.trans h')) (hc n hn)

end BridgeFragment

#print axioms BridgeFragment.meanFragReal_eq
#print axioms BridgeFragment.mathdb_345190_real
```
