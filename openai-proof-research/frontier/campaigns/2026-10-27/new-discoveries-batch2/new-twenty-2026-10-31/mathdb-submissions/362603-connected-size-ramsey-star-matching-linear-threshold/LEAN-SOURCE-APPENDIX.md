# Lean source appendix

Modules appear in import order.

### `StarRamseyStatement.lean`

```lean
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Option

open SimpleGraph

namespace StarRamsey

/-- A center (none) and p leaves (some j) in each of n components. -/
def starForest (n p : ℕ) : SimpleGraph (Fin n × Option (Fin p)) where
  Adj x y := x.1 = y.1 ∧
    ((x.2 = none ∧ y.2 ≠ none) ∨ (y.2 = none ∧ x.2 ≠ none))
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2.elim (fun h => h.2 h.1) (fun h => h.2 h.1)⟩

/-- Extra edges in the host are allowed. -/
def HasCopy {α β : Type*} (H : SimpleGraph α) (G : SimpleGraph β) : Prop :=
  ∃ f : H →g G, Function.Injective f

/-- The red graph is R and the remaining host edges are blue. -/
def Arrows {α : Type*} (G : SimpleGraph α) (n p m : ℕ) : Prop :=
  ∀ R : SimpleGraph α, R ≤ G →
    HasCopy (starForest n p) R ∨ HasCopy (starForest 1 m) (G ⊓ Rᶜ)

noncomputable def ConnectedRamseyHost (n p m e : ℕ) : Prop := by
  classical
  exact ∃ v : ℕ, ∃ G : SimpleGraph (Fin v),
    G.Connected ∧ G.edgeFinset.card = e ∧ Arrows G n p m

theorem star_adj {n p : ℕ} (i : Fin n) (j : Fin p) :
    (starForest n p).Adj (i, none) (i, some j) :=
  ⟨rfl, Or.inl ⟨rfl, Option.some_ne_none _⟩⟩

theorem star_copy_of_leaves {α : Type*} {G : SimpleGraph α} {p : ℕ} {x : α}
    (leaf : Fin p → α) (hinj : Function.Injective leaf) (hadj : ∀ j, G.Adj x (leaf j)) :
    HasCopy (starForest 1 p) G := by
  let f : Fin 1 × Option (Fin p) → α := fun a => a.2.elim x leaf
  refine ⟨⟨f, ?_⟩, ?_⟩
  · rintro ⟨i, a⟩ ⟨k, b⟩ ⟨_, h | h⟩
    · rcases h with ⟨rfl, hb⟩
      cases b with
      | none => exact (hb rfl).elim
      | some j => exact hadj j
    · rcases h with ⟨rfl, ha⟩
      cases a with
      | none => exact (ha rfl).elim
      | some j => exact (hadj j).symm
  · rintro ⟨i, a⟩ ⟨k, b⟩ heq
    refine Prod.ext (Subsingleton.elim _ _) ?_
    cases a <;> cases b
    · rfl
    · exact (G.ne_of_adj (hadj _) heq).elim
    · exact (G.ne_of_adj (hadj _) heq.symm).elim
    · exact congrArg some (hinj heq)

theorem star_copy_iff_degree {α : Type*} [Fintype α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (p : ℕ) :
    HasCopy (starForest 1 p) G ↔ ∃ x, p ≤ G.degree x := by
  classical
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f (0, none), ?_⟩
    let leaf : Fin p → G.neighborFinset (f (0, none)) :=
      fun j => ⟨f (0, some j), (G.mem_neighborFinset _ _).mpr (f.map_adj (star_adj 0 j))⟩
    have h : Function.Injective leaf := by
      intro j k heq
      have hpair := hf (congrArg Subtype.val heq)
      simpa using congrArg Prod.snd hpair
    simpa only [Fintype.card_fin, Fintype.card_coe, G.card_neighborFinset_eq_degree] using
      Fintype.card_le_of_injective leaf h
  · rintro ⟨x, hx⟩
    have h : p ≤ Fintype.card (G.neighborFinset x) := by simpa only [Fintype.card_coe, G.card_neighborFinset_eq_degree] using hx
    let leaf := (Fin.castLEEmb h).trans (Fintype.equivFin (G.neighborFinset x)).symm.toEmbedding
    exact star_copy_of_leaves (fun j => (leaf j).1)
      (fun _ _ h => leaf.injective (Subtype.ext h))
      (fun j => (G.mem_neighborFinset _ _).mp (leaf j).2)

theorem Arrows.of_iso {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β}
    (i : G ≃g H) {n p m : ℕ} (h : Arrows G n p m) : Arrows H n p m := by
  intro R hR
  let S := R.comap i
  have hS : S ≤ G := fun _ _ hab => i.map_rel_iff.mp (hR hab)
  rcases h S hS with ⟨f, hf⟩ | ⟨f, hf⟩
  · exact Or.inl ⟨⟨i ∘ f, fun {_ _} hab => f.map_adj hab⟩, i.injective.comp hf⟩
  · refine Or.inr ⟨⟨i ∘ f, ?_⟩, i.injective.comp hf⟩
    intro a b hab
    have h := f.map_adj hab
    exact ⟨i.map_rel_iff.mpr h.1, ⟨fun he => (G.ne_of_adj h.1) (i.injective he), h.2.2⟩⟩

theorem connectedRamseyHost_of_graph {α : Type} [Fintype α] (G : SimpleGraph α)
    [Fintype G.edgeSet] {n p m e : ℕ} (hc : G.Connected)
    (he : G.edgeFinset.card = e) (ha : Arrows G n p m) :
    ConnectedRamseyHost n p m e := by
  classical
  let i := Fintype.equivFin α
  let H := G.map i
  let j : G ≃g H := SimpleGraph.Iso.map i G
  let : DecidableRel H.Adj := Classical.decRel _
  exact ⟨_, H, hc.map j.toHom j.surjective, (j.card_edgeFinset_eq).symm.trans he, Arrows.of_iso j ha⟩

#print axioms star_copy_iff_degree
#print axioms connectedRamseyHost_of_graph

end StarRamsey
```

### `StarRamseySemantics.lean`

```lean
import StarRamseyStatement

open SimpleGraph

namespace StarRamsey

theorem hasCopy_iff_subgraph {α β : Type*} (H : SimpleGraph α) (G : SimpleGraph β) :
    HasCopy H G ↔ ∃ S : G.Subgraph, Nonempty (H ≃g S.coe) := by
  classical
  constructor
  · rintro ⟨f, hf⟩
    let S := (⊤ : H.Subgraph).map f
    let g : α → S.verts := fun a => ⟨f a, ⟨a, by simp, rfl⟩⟩
    have hg : Function.Bijective g := by
      refine ⟨fun _ _ h => hf (congrArg Subtype.val h), ?_⟩
      rintro ⟨b, ⟨a, _, ha⟩⟩
      exact ⟨a, Subtype.ext ha⟩
    refine ⟨S, ⟨{ toEquiv := Equiv.ofBijective g hg, map_rel_iff' := ?_ }⟩⟩
    intro a b
    change S.Adj (f a) (f b) ↔ H.Adj a b
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      have hh : H.Adj u v := (⊤ : H.Subgraph).adj_sub huv
      rwa [hf hu, hf hv] at hh
    · intro hab
      exact ⟨a, b, hab, rfl, rfl⟩
  · rintro ⟨S, ⟨f⟩⟩
    exact ⟨S.hom.comp f.toHom, S.hom_injective.comp f.injective⟩

theorem arrows_iff_edge_partition {α : Type*} (G : SimpleGraph α) (n p m : ℕ) :
    Arrows G n p m ↔
      ∀ R B : SimpleGraph α, R ⊔ B = G → Disjoint R B →
        HasCopy (starForest n p) R ∨ HasCopy (starForest 1 m) B := by
  classical
  constructor
  · intro h R B hsup hdis
    have hR : R ≤ G := hsup ▸ le_sup_left
    have hb : B = G ⊓ Rᶜ := by
      ext u v
      constructor
      · intro h
        have hg : G.Adj u v := hsup ▸ (Or.inr h : (R ⊔ B).Adj u v)
        exact ⟨hg, ⟨G.ne_of_adj hg, fun hr => SimpleGraph.disjoint_left.mp hdis u v hr h⟩⟩
      · intro h
        have hg : (R ⊔ B).Adj u v := hsup.symm ▸ h.1
        exact hg.elim (fun hr => (h.2.2 hr).elim) id
    rw [hb]
    exact h R hR
  · intro h R hR
    refine h R (G ⊓ Rᶜ) ?_ ?_
    · ext u v
      constructor
      · rintro (h | h)
        · exact hR h
        · exact h.1
      · intro h
        by_cases hr : R.Adj u v
        · exact Or.inl hr
        · exact Or.inr ⟨h, ⟨G.ne_of_adj h, hr⟩⟩
    · exact SimpleGraph.disjoint_left.mpr (fun _ _ hR hB => hB.2.2 hR)

#print axioms hasCopy_iff_subgraph
#print axioms arrows_iff_edge_partition

end StarRamsey
```

### `StarRamseyUpper.lean`

```lean
import StarRamseyStatement
import Mathlib.Data.Fintype.EquivFin

open SimpleGraph Finset

namespace StarRamsey

private abbrev Vert (n M : ℕ) := Fin n × Option (Fin M)

private def parent {n M : ℕ} (root : Fin n) (x : Vert n M) : Vert n M :=
  if x.2 = none then (root, none) else (x.1, none)

private def hubGraph {n M : ℕ} (root : Fin n) : SimpleGraph (Vert n M) where
  Adj x y := x ≠ y ∧ (parent root x = y ∨ parent root y = x)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private theorem hub_adj_leaf {n M : ℕ} (r i : Fin n) (j : Fin M) :
    (hubGraph r).Adj (i, none) (i, some j) :=
  ⟨by simp, Or.inr (by simp [parent])⟩

private theorem hub_connected {n M : ℕ} (r : Fin n) :
    (hubGraph (M := M) r).Connected := by
  have toHub : ∀ x, (hubGraph (M := M) r).Reachable x (r, none) := by
    rintro ⟨i, a⟩
    have hc : (hubGraph (M := M) r).Reachable (i, none) (r, none) := by
      by_cases h : i = r
      · subst i
        exact SimpleGraph.Reachable.rfl
      · exact SimpleGraph.Adj.reachable (G := hubGraph r)
          ⟨by simpa using h, Or.inl (by simp [parent])⟩
    cases a with
    | none => exact hc
    | some j => exact (hub_adj_leaf r i j).reachable.symm.trans hc
  let : Nonempty (Vert n M) := ⟨(r, none)⟩
  exact ⟨fun x y => (toHub x).trans (toHub y).symm⟩

private theorem hub_card {n M : ℕ} (r : Fin n)
    [Fintype (hubGraph (M := M) r).edgeSet] :
    (hubGraph (M := M) r).edgeFinset.card = n * (M + 1) - 1 := by
  classical
  let C : Finset (Vert n M) := univ.erase (r, none)
  have parent_ne : ∀ x ∈ C, x ≠ parent r x := by
    rintro ⟨i, a⟩ hx
    cases a with
    | none => simpa [C, parent] using hx
    | some j => simp [parent]
  let f : Vert n M → Sym2 (Vert n M) := fun x => s(x, parent r x)
  have hf : Set.InjOn f ↑C := by
    intro x hx y hy h
    rcases Sym2.eq_iff.mp h with h | ⟨hxy, hyx⟩
    · exact h.1
    · have hnone : x.2 = none := by rw [hxy]; simp [parent]; split <;> rfl
      have hnone' : y.2 = none := by rw [← hyx]; simp [parent]; split <;> rfl
      have hh : x = (r, none) := by simpa [parent, hnone'] using hxy
      exact False.elim ((mem_erase.mp hx).1 hh)
  have he : (hubGraph (M := M) r).edgeFinset = C.image f := by
    ext e
    induction e using Sym2.inductionOn with
    | _ x y =>
      constructor
      · intro he
        obtain ⟨hne, h | h⟩ := (SimpleGraph.mem_edgeFinset.mp he :
          (hubGraph r).Adj x y)
        · refine mem_image.mpr ⟨x, mem_erase.mpr ⟨?_, mem_univ _⟩, ?_⟩
          · rintro rfl
            exact hne (by simpa [parent] using h)
          · change s(x, parent r x) = s(x, y)
            rw [h]
        · refine mem_image.mpr ⟨y, mem_erase.mpr ⟨?_, mem_univ _⟩, ?_⟩
          · rintro rfl
            exact hne (by simpa [parent] using h.symm)
          · exact Sym2.eq_iff.mpr (Or.inr ⟨rfl, h⟩)
      · intro he
        rcases mem_image.mp he with ⟨z, hz, h⟩
        rw [← h]
        exact SimpleGraph.mem_edgeFinset.mpr ⟨parent_ne z hz, Or.inl rfl⟩
  rw [he, card_image_of_injOn hf, show C.card = _ from card_erase_of_mem (mem_univ _)]
  simp

private theorem hub_arrows {n m p : ℕ} (r : Fin n) :
    Arrows (hubGraph (M := m + p - 1) r) n p m := by
  classical
  let M := m + p - 1
  let G := hubGraph (M := M) r
  intro R hR
  let A : Fin n → Finset (Fin M) := fun i => univ.filter (fun j => R.Adj (i, none) (i, some j))
  let B : Fin n → Finset (Fin M) := fun i => univ \ A i
  by_cases hb : ∃ i, m ≤ (B i).card
  · obtain ⟨i, hi⟩ := hb
    let pick := (Fin.castLEEmb (show m ≤ Fintype.card (B i) by simpa using hi)).trans
      (Fintype.equivFin (B i)).symm.toEmbedding
    apply Or.inr
    refine star_copy_of_leaves (x := (i, none))
      (fun j => (i, some (pick j).1)) ?_ ?_
    · intro a b h
      exact pick.injective (Subtype.ext (by simpa using congrArg Prod.snd h))
    · intro j
      refine ⟨hub_adj_leaf r i _, ⟨by simp, ?_⟩⟩
      have hj := (pick j).2
      exact fun h => (mem_sdiff.mp hj).2 (mem_filter.mpr ⟨mem_univ _, h⟩)
  · push Not at hb
    have ha (i : Fin n) : p ≤ Fintype.card (A i) := by
      have h := card_sdiff_add_card_eq_card (subset_univ (A i))
      have h' := hb i
      change (B i).card + (A i).card = _ at h
      simp only [card_univ, Fintype.card_fin] at h
      rw [Fintype.card_coe]
      dsimp [M] at h
      omega
    let pick (i : Fin n) := (Fin.castLEEmb (ha i)).trans
      (Fintype.equivFin (A i)).symm.toEmbedding
    let f : Vert n p → Vert n M := fun x => (x.1, x.2.map (fun j => (pick x.1 j).1))
    apply Or.inl
    refine ⟨⟨f, ?_⟩, ?_⟩
    · rintro ⟨i, a⟩ ⟨k, b⟩ ⟨rfl, h | h⟩
      · rcases h with ⟨rfl, hb⟩
        cases b with
        | none => exact (hb rfl).elim
        | some j => exact (mem_filter.mp (pick i j).2).2
      · rcases h with ⟨rfl, ha⟩
        cases a with
        | none => exact (ha rfl).elim
        | some j => exact R.adj_symm (mem_filter.mp (pick i j).2).2
    · rintro ⟨i, a⟩ ⟨k, b⟩ heq
      have hik : i = k := congrArg Prod.fst heq
      subst k
      have hab := congrArg Prod.snd heq
      change a.map _ = b.map _ at hab
      have hinj : Function.Injective (fun j => (pick i j).1) :=
        fun _ _ h => (pick i).injective (Subtype.ext h)
      exact Prod.ext rfl (Option.map_injective hinj hab)

theorem connectedRamsey_upper (n p m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    ConnectedRamseyHost n p m (n * (m + p) - 1) := by
  classical
  let r : Fin n := ⟨0, hn⟩
  refine connectedRamseyHost_of_graph (hubGraph (M := m + p - 1) r)
    (hub_connected r) ?_ (hub_arrows r)
  rw [hub_card, show m + p - 1 + 1 = m + p by omega]

#print axioms connectedRamsey_upper

end StarRamsey
```

### `StarRamseyColor.lean`

```lean
import StarRamseyStatement
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open SimpleGraph Finset
open scoped BigOperators

namespace StarRamsey

variable {α : Type*}

noncomputable def high [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj] (m : ℕ) : Finset α :=
  univ.filter (fun u => m ≤ G.degree u)

noncomputable def lowNbr [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj] (U : Finset α) (u : α) :
    Finset α := by
  classical
  exact (G.neighborFinset u).filter (fun v => v ∉ U)

@[simp] theorem mem_lowNbr [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj] (U : Finset α) (u v : α) :
    v ∈ lowNbr G U u ↔ G.Adj u v ∧ v ∉ U := by
  classical
  simp [lowNbr]

noncomputable def strong [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj] (U : Finset α)
    (M : ℕ) : Finset α := by
  classical
  exact U.filter (fun u => M ≤ (lowNbr G U u).card)

def redGraph (G : SimpleGraph α) (U : Finset α) (A : α → Finset α) : SimpleGraph α where
  Adj u v := G.Adj u v ∧ ((u ∈ U ∧ v ∈ U) ∨ (u ∈ U ∧ v ∈ A u) ∨ (v ∈ U ∧ u ∈ A v))
  symm := ⟨fun _ _ h => ⟨h.1.symm, by
    rcases h.2 with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

theorem redGraph_le (G : SimpleGraph α) (U : Finset α) (A : α → Finset α) :
    redGraph G U A ≤ G := fun _ _ h => h.1

theorem redGraph_meets_high {G : SimpleGraph α} {U : Finset α} {A : α → Finset α}
    {u v : α} (h : (redGraph G U A).Adj u v) : u ∈ U ∨ v ∈ U := by
  rcases h.2 with h | h | h
  · exact Or.inl h.1
  · exact Or.inl h.1
  · exact Or.inr h.1

theorem redGraph_cross {G : SimpleGraph α} {U : Finset α} {A : α → Finset α}
    {u v : α} (hv : v ∉ U) (h : (redGraph G U A).Adj u v) : v ∈ A u := by
  rcases h.2 with h | h | h
  · exact (hv h.2).elim
  · exact h.2
  · exact (hv h.1).elim

theorem choose_red_neighborhoods [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (U : Finset α) (m : ℕ) (B : α → Finset α)
    (hB : ∀ u, B u ⊆ lowNbr G U u)
    (hcard : ∀ u, (B u).card ≤ (lowNbr G U u).card - (m - 1)) :
    ∃ A : α → Finset α, ∀ u,
      B u ⊆ A u ∧ A u ⊆ lowNbr G U u ∧ (A u).card = (lowNbr G U u).card - (m - 1) := by
  classical
  have h u := exists_subsuperset_card_eq (hB u) (hcard u) (Nat.sub_le ..)
  choose A hBA hAG hA using h
  exact ⟨A, fun u => ⟨hBA u, hAG u, hA u⟩⟩

theorem no_blue_star [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj] (m : ℕ) (hm : 0 < m)
    (A : α → Finset α)
    (hA : ∀ u, A u ⊆ lowNbr G (high G m) u ∧
      (A u).card = (lowNbr G (high G m) u).card - (m - 1)) :
    ¬HasCopy (starForest 1 m) (G ⊓ (redGraph G (high G m) A)ᶜ) := by
  classical
  let U := high G m
  let R := redGraph G U A
  let B := G ⊓ Rᶜ
  change ¬HasCopy (starForest 1 m) B
  rw [star_copy_iff_degree]
  rintro ⟨u, hu⟩
  by_cases huu : u ∈ U
  · have hsub : B.neighborFinset u ⊆ lowNbr G U u \ A u := by
      intro v hv
      have hb := (B.mem_neighborFinset _ _).mp hv
      have hG : G.Adj u v := hb.1
      have hnR : ¬R.Adj u v := hb.2.2
      refine mem_sdiff.mpr ⟨(mem_lowNbr G U u v).mpr ⟨hG, ?_⟩, ?_⟩
      · exact fun h => hnR ⟨hG, Or.inl ⟨huu, h⟩⟩
      · exact fun h => hnR ⟨hG, Or.inr (Or.inl ⟨huu, h⟩)⟩
    have hc := card_le_card hsub
    rw [card_sdiff_of_subset (hA u).1, (hA u).2, B.card_neighborFinset_eq_degree] at hc
    omega
  · have hdeg : ¬m ≤ G.degree u := by simpa [U, high] using huu
    have hsub : B.neighborFinset u ⊆ G.neighborFinset u := by
      intro v hv
      exact (G.mem_neighborFinset _ _).mpr ((B.mem_neighborFinset _ _).mp hv).1
    have hc := card_le_card hsub
    rw [B.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at hc
    omega

section Packing

variable {G : SimpleGraph α} {U : Finset α} {A : α → Finset α} {n p : ℕ}
variable (f : starForest n p →g redGraph G U A)

noncomputable def highTags (i : Fin n) : Finset (Option (Fin p)) := by
  classical
  exact univ.filter (fun a => f (i, a) ∈ U)

@[simp] theorem mem_highTags {i : Fin n} {a : Option (Fin p)} :
    a ∈ highTags f i ↔ f (i, a) ∈ U := by
  classical
  simp [highTags]

theorem highTags_nonempty (hp : 0 < p) (i : Fin n) : (highTags f i).Nonempty := by
  let j : Fin p := ⟨0, hp⟩
  rcases redGraph_meets_high (f.map_adj (star_adj i j)) with h | h
  · exact ⟨none, (mem_highTags f).mpr h⟩
  · exact ⟨some j, (mem_highTags f).mpr h⟩

/-- Reorient a single edge when its high-degree vertex is the designated leaf. -/
theorem unique_high_leaves (hf : Function.Injective f) {i : Fin n} {a : Option (Fin p)}
    (ha : highTags f i = {a}) :
    ∃ leaf : Fin p ↪ α, ∀ j, leaf j ∈ A (f (i, a)) ∧ ∃ b, leaf j = f (i, b) := by
  classical
  have unique (b : Option (Fin p)) : f (i, b) ∈ U ↔ b = a := by
    rw [← mem_highTags f, ha, mem_singleton]
  cases a with
  | none =>
    refine ⟨⟨fun j => f (i, some j), ?_⟩, ?_⟩
    · intro j k h
      simpa using congrArg Prod.snd (hf h)
    · intro j
      have hlow : f (i, some j) ∉ U := fun h => Option.some_ne_none _ ((unique _).mp h)
      exact ⟨redGraph_cross hlow (f.map_adj (star_adj i j)), some j, rfl⟩
  | some k =>
    have hlow : f (i, none) ∉ U := fun h => Option.some_ne_none _ ((unique _).mp h).symm
    have hall (j : Fin p) : j = k := by
      rcases redGraph_meets_high (f.map_adj (star_adj i j)) with h | h
      · exact (hlow h).elim
      · exact Option.some.inj ((unique _).mp h)
    refine ⟨⟨fun _ => f (i, none), fun {j k'} _ => (hall j).trans (hall k').symm⟩, ?_⟩
    intro j
    exact ⟨redGraph_cross hlow (f.map_adj (star_adj i k)).symm, none, rfl⟩

theorem highTags_sum_le (hf : Function.Injective f) :
    (∑ i, (highTags f i).card) ≤ U.card := by
  classical
  let pick : (Σ i, highTags f i) → U :=
    fun x => ⟨f (x.1, x.2), (mem_highTags f).mp x.2.2⟩
  have h : Function.Injective pick := by
    intro ⟨i, a⟩ ⟨j, b⟩ heq
    have hp := hf (congrArg Subtype.val heq)
    have hij : i = j := congrArg Prod.fst hp
    subst j
    exact congrArg (Sigma.mk i) (Subtype.ext (congrArg Prod.snd hp))
  simpa only [Fintype.card_sigma, Fintype.card_coe] using Fintype.card_le_of_injective pick h

end Packing

theorem packing_necessary [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj] (U : Finset α)
    (A : α → Finset α) {n p m : ℕ} (hp : 0 < p)
    (hA : ∀ u, (A u).card = (lowNbr G U u).card - (m - 1))
    (hcopy : HasCopy (starForest n p) (redGraph G U A)) :
    n ≤ U.card ∧ 2 * n ≤ U.card + (strong G U (m + p - 1)).card := by
  classical
  obtain ⟨f, hf⟩ := hcopy
  let single : Finset (Fin n) := univ.filter (fun i => (highTags f i).card = 1)
  let S := strong G U (m + p - 1)
  have hsingle (i : single) : ∃ a, highTags f i = {a} := by
    exact card_eq_one.mp (mem_filter.mp i.2).2
  let tag (i : single) := (hsingle i).choose
  have ht (i : single) : highTags f i = {tag i} := (hsingle i).choose_spec
  let pick : single → S := fun i => ⟨f (i, tag i), by
    have hu : f (i, tag i) ∈ U := (mem_highTags f).mp (by rw [ht]; simp)
    obtain ⟨leaf, hl⟩ := unique_high_leaves f hf (ht i)
    let inj : Fin p → A (f (i, tag i)) := fun j => ⟨leaf j, (hl j).1⟩
    have h := Fintype.card_le_of_injective inj
      (fun _ _ heq => leaf.injective (congrArg Subtype.val heq))
    simp only [Fintype.card_fin, Fintype.card_coe, hA] at h
    exact mem_filter.mpr ⟨hu, by omega⟩⟩
  have hinj : Function.Injective pick := by
    intro a b h
    exact Subtype.ext (congrArg Prod.fst (hf (congrArg Subtype.val h)))
  have hs : single.card ≤ S.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective pick hinj
  have htU := highTags_sum_le f hf
  have hpos (i : Fin n) : 1 ≤ (highTags f i).card :=
    card_pos.mpr (highTags_nonempty f hp i)
  constructor
  · have hh := sum_le_sum (s := univ) (fun i _ => hpos i)
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hh
    exact hh.trans htU
  · have hh := sum_le_sum (s := univ) (g := fun i => (highTags f i).card)
        (f := fun i => if (highTags f i).card = 1 then 1 else 2) (by
      intro i _
      split <;> have := hpos i <;> omega)
    have eq : (∑ i : Fin n, if (highTags f i).card = 1 then 1 else 2) =
        single.card + 2 * (n - single.card) := by
      rw [sum_ite]
      have hc : (univ.filter (fun i : Fin n => ¬(highTags f i).card = 1)).card =
          n - single.card := by
        have he : (univ.filter (fun i : Fin n => ¬(highTags f i).card = 1)) = univ \ single := by
          ext i
          simp [single]
        rw [he, card_sdiff_of_subset (subset_univ single)]
        simp
      simp only [sum_const, smul_eq_mul, mul_one, hc, mul_comm _ 2]
      rfl
    change 2 * n ≤ U.card + S.card
    rw [eq] at hh
    have hc : single.card ≤ n := by simpa using card_le_card (subset_univ single)
    omega

#print axioms no_blue_star
#print axioms packing_necessary

end StarRamsey
```

### `StarRamseyCount.lean`

```lean
import StarRamseyColor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open SimpleGraph Finset
open scoped BigOperators

namespace StarRamsey

variable {α : Type*}

/-- Unordered edges indexed by an endpoint in S and a prescribed neighbor outside S. -/
noncomputable def crossEdges (S : Finset α) (A : α → Finset α) : Finset (Sym2 α) := by
  classical
  exact S.biUnion (fun u => (A u).image (fun v => s(u, v)))

@[simp] theorem mem_crossEdges (S : Finset α) (A : α → Finset α) (e : Sym2 α) :
    e ∈ crossEdges S A ↔ ∃ u ∈ S, ∃ v ∈ A u, s(u, v) = e := by
  classical
  simp [crossEdges]

theorem card_crossEdges (S : Finset α) (A : α → Finset α)
    (hout : ∀ u ∈ S, ∀ v ∈ A u, v ∉ S) :
    (crossEdges S A).card = ∑ u ∈ S, (A u).card := by
  classical
  unfold crossEdges
  rw [card_biUnion]
  · apply sum_congr rfl
    intro u _
    exact card_image_of_injective _ (fun _ _ h => Sym2.congr_right.mp h)
  · intro u hu v hv huv
    apply Finset.disjoint_left.mpr
    rintro e he hf
    obtain ⟨x, hx, rfl⟩ := mem_image.mp he
    obtain ⟨y, _, hy⟩ := mem_image.mp hf
    rcases Sym2.eq_iff.mp hy with h | h
    · exact huv h.1.symm
    · exact hout u hu x hx (h.1 ▸ hv)

def crossGraph (G : SimpleGraph α) (U : Finset α) : SimpleGraph α where
  Adj u v := G.Adj u v ∧ ((u ∈ U ∧ v ∉ U) ∨ (v ∈ U ∧ u ∉ U))
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

theorem crossGraph_le (G : SimpleGraph α) (U : Finset α) : crossGraph G U ≤ G :=
  fun _ _ h => h.1

theorem edgeFinset_crossGraph [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj] (U : Finset α) :
    letI : DecidableRel (crossGraph G U).Adj := Classical.decRel _
    (crossGraph G U).edgeFinset = crossEdges U (lowNbr G U) := by
  classical
  ext e
  constructor
  · induction e using Sym2.inductionOn with
    | _ u v =>
      intro h
      obtain ⟨hG, h | h⟩ := SimpleGraph.mem_edgeFinset.mp h
      · exact (mem_crossEdges _ _ _).mpr ⟨u, h.1, v, by simp [hG, h.2], rfl⟩
      · exact (mem_crossEdges _ _ _).mpr ⟨v, h.1, u, by simp [hG.symm, h.2],
          Sym2.eq_swap⟩
  · intro h
    obtain ⟨u, hu, v, hv, rfl⟩ := (mem_crossEdges _ _ _).mp h
    have hv := (mem_lowNbr G U u v).mp hv
    exact SimpleGraph.mem_edgeFinset.mpr ⟨hv.1, Or.inl ⟨hu, hv.2⟩⟩

theorem high_handshake [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj] (m : ℕ) :
    (high G m).card * m ≤ 2 * G.edgeFinset.card := by
  classical
  have h : (∑ _u ∈ high G m, m) ≤ ∑ u ∈ high G m, G.degree u :=
    sum_le_sum (fun u hu => (mem_filter.mp hu).2)
  simp only [sum_const, smul_eq_mul] at h
  rw [← G.sum_degrees_eq_twice_card_edges]
  exact h.trans (sum_le_sum_of_subset (subset_univ _))

/-- The two classes counted here are strong-to-low edges and weak-to-nonweak edges.
The weak degree sum can lose at most one contribution per ordered weak pair. -/
theorem strong_weak_budget [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj] (m M : ℕ) :
    let U := high G m
    let S := strong G U M
    let W := U \ S
    S.card * M + W.card * m ≤ G.edgeFinset.card + W.card * W.card := by
  classical
  dsimp only
  let U := high G m
  let S := strong G U M
  let W := U \ S
  let ES := crossEdges S (lowNbr G U)
  let EW := crossEdges W (lowNbr G W)
  have hSU : S ⊆ U := filter_subset _ _
  have hWU : W ⊆ U := fun _ h => (mem_sdiff.mp h).1
  have hSW : Disjoint ES EW := by
    apply Finset.disjoint_left.mpr
    intro e he hw
    obtain ⟨s, hs, x, hx, rfl⟩ := (mem_crossEdges _ _ _).mp he
    obtain ⟨w, hw, y, _, hy⟩ := (mem_crossEdges _ _ _).mp hw
    rcases Sym2.eq_iff.mp hy with h | h
    · exact (mem_sdiff.mp hw).2 (h.1 ▸ hs)
    · exact ((mem_lowNbr _ _ _ _).mp hx).2 (h.1 ▸ hWU hw)
  have hsub : ∀ (T Z : Finset α), crossEdges T (lowNbr G Z) ⊆ G.edgeFinset := by
    intro T Z e he
    obtain ⟨u, _, v, hv, rfl⟩ := (mem_crossEdges _ _ _).mp he
    exact SimpleGraph.mem_edgeFinset.mpr ((mem_lowNbr _ _ _ _).mp hv).1
  have hsum := card_le_card (union_subset (hsub S U) (hsub W W))
  rw [show crossEdges S (lowNbr G U) = ES from rfl,
    show crossEdges W (lowNbr G W) = EW from rfl, card_union_of_disjoint hSW] at hsum
  have hS : S.card * M ≤ ES.card := by
    rw [card_crossEdges _ _ (fun u _ v hv h => ((mem_lowNbr _ _ _ _).mp hv).2 (hSU h))]
    simpa only [sum_const, smul_eq_mul] using
      (sum_le_sum (s := S) (f := fun _ => M) (g := fun u => (lowNbr G U u).card)
        (fun u hu => (mem_filter.mp hu).2))
  have hW : W.card * m ≤ EW.card + W.card * W.card := by
    rw [card_crossEdges _ _ (fun u _ v hv => ((mem_lowNbr _ _ _ _).mp hv).2)]
    have step (u : α) (hu : u ∈ W) : m ≤ (lowNbr G W u).card + W.card := by
      have hd : m ≤ G.degree u := (mem_filter.mp (hWU hu)).2
      have hsub : G.neighborFinset u ⊆ lowNbr G W u ∪ W := by
        intro v hv
        by_cases h : v ∈ W
        · exact mem_union_right _ h
        · exact mem_union_left _ ((mem_lowNbr _ _ _ _).mpr
            ⟨(G.mem_neighborFinset _ _).mp hv, h⟩)
      have hh := (card_le_card hsub).trans (card_union_le _ _)
      exact hd.trans hh
    simpa only [sum_add_distrib, sum_const, smul_eq_mul] using sum_le_sum (s := W) step
  change S.card * M + W.card * m ≤ G.edgeFinset.card + W.card * W.card
  omega

theorem exceptional_counts [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj]
    {n p m : ℕ} (hn : 0 < n) (hp : 0 < p) (hm : 5 * (n + p) ≤ m)
    (he : G.edgeFinset.card < n * (m + p) - 1)
    (ht : n ≤ (high G m).card)
    (hts : 2 * n ≤ (high G m).card + (strong G (high G m) (m + p - 1)).card) :
    (high G m).card = n ∧ (strong G (high G m) (m + p - 1)).card = n := by
  classical
  let U := high G m
  let S := strong G U (m + p - 1)
  let W := U \ S
  have hSU : S ⊆ U := filter_subset _ _
  have hs := card_le_card hSU
  have hw := card_sdiff_of_subset hSU
  change W.card = U.card - S.card at hw
  change n ≤ U.card at ht
  change 2 * n ≤ U.card + S.card at hts
  change U.card = n ∧ S.card = n
  by_cases h : U.card = n
  · omega
  · exfalso
    have hhand := high_handshake G m
    change U.card * m ≤ _ at hhand
    have hbudget := strong_weak_budget G m (m + p - 1)
    change S.card * (m + p - 1) + W.card * m ≤ _ + W.card * W.card at hbudget
    let t : ℤ := U.card
    let s : ℤ := S.card
    let w : ℤ := W.card
    let a : ℤ := t - n
    have ha : 1 ≤ a := by dsimp [a, t]; omega
    have hw' : w = t - s := by dsimp [w, t, s]; omega
    have hw₀ : 0 ≤ w := by simp [w]
    have hweak : w ≤ 2 * a := by dsimp [a, w, t, s]; omega
    have hs' : (n : ℤ) - a ≤ s := by dsimp [s, a, t]; omega
    have hm' : 5 * ((n : ℤ) + p) ≤ m := by exact_mod_cast hm
    have hm₀ : (0 : ℤ) < m := by omega
    have hp' : (1 : ℤ) ≤ p := by omega
    have hhand' : t * m ≤ 2 * (G.edgeFinset.card : ℤ) := by
      dsimp only [t]
      exact_mod_cast hhand
    have hE : (G.edgeFinset.card : ℤ) + 2 ≤ (n : ℤ) * ((m : ℤ) + p) := by
      have hh : G.edgeFinset.card + 2 ≤ n * (m + p) := by omega
      exact_mod_cast hh
    have happ : 2 * a ≤ 2 * (n : ℤ) + p := by
      have hmp := mul_nonneg (show 0 ≤ (p : ℤ) by omega) (show 0 ≤ (m : ℤ) - 4 * n by omega)
      by_contra! hbad
      have hmul := mul_pos (show 0 < 2 * a - (2 * (n : ℤ) + p) by omega) hm₀
      dsimp only [a] at hmul
      nlinarith only [hmp, hmul, hhand', hE]
    have hww : w * w ≤ 4 * a * a := by
      nlinarith [mul_nonneg hw₀ (show 0 ≤ 2 * a - w by omega),
        mul_nonneg (show 0 ≤ 2 * a by omega) (show 0 ≤ 2 * a - w by omega)]
    have hM : (↑(m + p - 1) : ℤ) = (m : ℤ) + p - 1 := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      rfl
    have hb : s * ((m : ℤ) + p - 1) + w * m ≤ (G.edgeFinset.card : ℤ) + w * w := by
      rw [← hM]
      dsimp only [s, w]
      exact_mod_cast hbudget
    have hsp := mul_nonneg (show 0 ≤ s - ((n : ℤ) - a) by omega)
      (show 0 ≤ (p : ℤ) - 1 by omega)
    have he' : (G.edgeFinset.card : ℤ) ≤ (n : ℤ) * ((m : ℤ) + p - 1) + n - 2 := by
      nlinarith only [hE]
    have hfac : (n : ℤ) + 2 * p + 1 ≤ (m : ℤ) - p + 1 - 4 * a := by omega
    have hprod := mul_nonneg (show 0 ≤ a - 1 by omega)
      (show 0 ≤ (n : ℤ) + 2 * p + 1 by omega)
    have hprod' : (0 : ℤ) ≤ a * (((m : ℤ) - p + 1 - 4 * a) - ((n : ℤ) + 2 * p + 1)) := mul_nonneg (show 0 ≤ a by omega)
      (sub_nonneg.mpr hfac)
    rw [hw'] at hb
    have ha' : t = (n : ℤ) + a := by dsimp [a]; omega
    rw [ha'] at hb
    rw [hw', ha'] at hww
    nlinarith only [hb, hsp, hww, he', hprod, hprod', hp']

#print axioms exceptional_counts

end StarRamsey
```

### `StarRamseyForest.lean`

```lean
import StarRamseyCount
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

open SimpleGraph Finset
open scoped BigOperators

namespace StarRamsey

variable {α : Type*} [Fintype α]

omit [Fintype α] in
private theorem mapped_reachable {β : Type*} {G : SimpleGraph α}
    (f : α → β) {x y : α} (h : G.Walk x y) : (G.map f).Reachable (f x) (f y) := by
  induction h with
  | nil => exact SimpleGraph.Reachable.rfl
  | @cons u v w huv _ ih =>
    by_cases he : f u = f v
    · rwa [he]
    · exact (SimpleGraph.Adj.reachable (G := G.map f) ⟨he, u, v, huv, rfl, rfl⟩).trans ih

/-- The number of missing edges is at least the number of components minus one. -/
theorem component_cost (G H : SimpleGraph α) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hG : G.Connected) (hHG : H ≤ G) :
    Nat.card H.ConnectedComponent + H.edgeFinset.card ≤ G.edgeFinset.card + 1 := by
  classical
  let q := H.connectedComponentMk
  let Q := G.map q
  have hQ : Q.Connected := by
    let : Nonempty α := hG.nonempty
    refine ⟨?_⟩
    intro c d
    obtain ⟨u, rfl⟩ := c.exists_rep
    obtain ⟨v, rfl⟩ := d.exists_rep
    exact mapped_reachable q (hG.preconnected u v).some
  obtain ⟨T, hTQ, hT⟩ := hQ.exists_isTree_le
  rw [Nat.card_eq_fintype_card]
  have hsize := hT.card_edgeFinset
  have hsub : Q.edgeFinset ⊆ (G.edgeFinset \ H.edgeFinset).image (Sym2.map q) := by
    intro e
    induction e using Sym2.inductionOn with
    | _ c d =>
      intro he
      obtain ⟨hne, u, v, huv, rfl, rfl⟩ := SimpleGraph.mem_edgeFinset.mp he
      have hnH : ¬H.Adj u v := fun hh => hne (ConnectedComponent.sound hh.reachable)
      exact mem_image.mpr ⟨s(u, v),
        mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr huv,
          fun h => hnH (SimpleGraph.mem_edgeFinset.mp h)⟩, rfl⟩
  have hle := (card_le_card (SimpleGraph.edgeFinset_mono hTQ)).trans
    ((card_le_card hsub).trans (card_image_le))
  rw [card_sdiff_of_subset (SimpleGraph.edgeFinset_mono hHG)] at hle
  have hh := card_le_card (SimpleGraph.edgeFinset_mono hHG)
  omega

noncomputable def componentVertices (H : SimpleGraph α) (c : H.ConnectedComponent) :
    Finset α := by
  classical
  exact univ.filter (fun x => H.connectedComponentMk x = c)

@[simp] theorem mem_componentVertices (H : SimpleGraph α) (c : H.ConnectedComponent) (x : α) :
    x ∈ componentVertices H c ↔ H.connectedComponentMk x = c := by
  classical
  simp [componentVertices]

theorem componentVertices_connected (H : SimpleGraph α) (c : H.ConnectedComponent) :
    (H.induce (↑(componentVertices H c) : Set α)).Connected := by
  have he : (↑(componentVertices H c) : Set α) = c.supp := by
    ext x
    exact (mem_componentVertices H c x).trans ((c.mem_supp_iff x).symm)
  rw [he]
  exact c.connected_toSimpleGraph

theorem component_weight_sum [DecidableEq α] (H : SimpleGraph α) [DecidableRel H.Adj]
    (w : α → ℤ) :
    (∑ c : H.ConnectedComponent, ∑ x ∈ componentVertices H c, w x) = ∑ x, w x := by
  classical
  exact sum_fiberwise_of_maps_to (g := H.connectedComponentMk) (f := w) (fun x (_ : x ∈ (univ : Finset α)) =>
    mem_univ (H.connectedComponentMk x))

noncomputable def vertexWeight (U : Finset α) (b : α → ℕ) (x : α) : ℤ := by
  classical
  exact if x ∈ U then 1 - (b x : ℤ) else 0

/-- The component bound. -/
theorem exists_heavy_cross_component (G : SimpleGraph α) [DecidableRel G.Adj]
    (U : Finset α) (b : α → ℕ) (M : ℕ) (hG : G.Connected)
    (hdeg : ∀ u ∈ U, (lowNbr G U u).card = M + b u)
    (he : G.edgeFinset.card + 2 ≤ U.card * M + U.card) :
    ∃ W : Finset α, ((crossGraph G U).induce (↑W : Set α)).Connected ∧
      2 ≤ ∑ x ∈ W, vertexWeight U b x := by
  classical
  let H := crossGraph G U
  let w := vertexWeight U b
  have hq := component_cost G H hG (crossGraph_le G U)
  rw [Nat.card_eq_fintype_card] at hq
  have hH : H.edgeFinset.card = U.card * M + ∑ u ∈ U, b u := by
    rw [show H.edgeFinset = crossEdges U (lowNbr G U) from edgeFinset_crossGraph G U,
      card_crossEdges _ _ (fun u _ v hv => ((mem_lowNbr G U u v).mp hv).2)]
    rw [sum_congr rfl hdeg, sum_add_distrib, sum_const, smul_eq_mul]
  have hsum : (∑ x, w x) = (U.card : ℤ) - ∑ x ∈ U, (b x : ℤ) := by
    simp only [w, vertexWeight, ← sum_filter, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, filter_mem_eq_inter,
      univ_inter]
  have hbase : (Fintype.card H.ConnectedComponent : ℤ) + 1 ≤ ∑ x, w x := by
    rw [hsum]
    have hh : Fintype.card H.ConnectedComponent + 1 + (∑ u ∈ U, b u) ≤ U.card := by omega
    have hh' : (Fintype.card H.ConnectedComponent : ℤ) + 1 + (∑ u ∈ U, (b u : ℤ)) ≤ U.card :=
      by exact_mod_cast hh
    omega
  by_contra! hnone
  have hh (c : H.ConnectedComponent) :
      (∑ x ∈ componentVertices H c, w x) ≤ 1 := by
    have h := hnone (componentVertices H c) (componentVertices_connected H c)
    change (∑ x ∈ componentVertices H c, w x) < 2 at h
    omega
  have htot := sum_le_sum (s := univ) (fun c _ => hh c)
  rw [component_weight_sum] at htot
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one] at htot
  omega

end StarRamsey
```

### `StarRamseyTree.lean`

```lean
import StarRamseyForest

open SimpleGraph Finset
open scoped BigOperators

namespace StarRamsey

variable {α : Type*} [Fintype α]

omit [Fintype α] in
private theorem avoids_root_path {T : SimpleGraph α} (hT : T.Connected) {u x : α}
    (hx : x ≠ u) : ∃ y, T.Adj u y ∧ (T.deleteIncidenceSet u).Reachable y x := by
  obtain ⟨p, hp⟩ := hT.exists_isPath u x
  cases p with
  | nil => exact (hx rfl).elim
  | cons h q =>
    have hnot : u ∉ q.support := (List.nodup_cons.mp hp.support_nodup).1
    refine ⟨_, h, ⟨q.transfer _ ?_⟩⟩
    intro e he
    rw [deleteIncidenceSet, SimpleGraph.edgeSet_deleteEdges]
    refine ⟨q.edges_subset_edgeSet he, ?_⟩
    intro hh
    exact hnot (q.mem_support_of_mem_edges he hh.2)

omit [Fintype α] in
private theorem induced_component_reachable {D T : SimpleGraph α} (hle : D ≤ T)
    {c : D.ConnectedComponent} {W : Set α} (hsub : c.supp ⊆ W)
    {x y : W} (hx : (x : α) ∈ c.supp) (hy : (y : α) ∈ c.supp) :
    (T.induce W).Reachable x y := by
  let f : c.toSimpleGraph →g T.induce W :=
    ⟨fun z => ⟨z, hsub z.2⟩, fun {_ _} h => hle h⟩
  exact (c.connected_toSimpleGraph.preconnected ⟨x, hx⟩ ⟨y, hy⟩).map f

/-- In a vertex-minimal connected set of weight at least two, every tree branch
at a fixed vertex has weight one. -/
private theorem minimal_tree_degree (T : SimpleGraph α) [DecidableRel T.Adj] (w : α → ℤ)
    (hT : T.IsTree) (hweight : 2 ≤ ∑ x, w x)
    (hmin : ∀ W : Finset α, W ≠ univ →
      (T.induce (↑W : Set α)).Connected → (∑ x ∈ W, w x) ≤ 1)
    (u : α) (hu : w u ≤ 1) : (T.degree u : ℤ) ≤ 2 - w u := by
  classical
  let D := T.deleteIncidenceSet u
  let r := D.connectedComponentMk u
  have root_eq (x : α) : D.connectedComponentMk x = r ↔ x = u := by
    constructor
    · intro h
      by_contra hne
      have hzero : D.degree u = 0 := by
        have h : D.neighborFinset u = ∅ := by
          ext v
          simp [D, deleteIncidenceSet_adj]
        rw [← D.card_neighborFinset_eq_degree, h, card_empty]
      exact D.not_reachable_of_right_degree_zero hne hzero (ConnectedComponent.eq.mp h)
    · rintro rfl
      rfl
  have root_set : componentVertices D r = {u} := by
    ext x
    simp [root_eq]
  have adj_branch (c : D.ConnectedComponent) (hc : c ≠ r) :
      ∃ y, T.Adj u y ∧ D.connectedComponentMk y = c := by
    obtain ⟨x, rfl⟩ := c.exists_rep
    obtain ⟨y, hy, hr⟩ := avoids_root_path hT.connected
      (fun h : x = u => hc ((root_eq x).mpr h))
    exact ⟨y, hy, ConnectedComponent.sound hr⟩
  have unique_branch {x y : α} (hx : T.Adj u x) (hy : T.Adj u y)
      (hxy : D.connectedComponentMk x = D.connectedComponentMk y) : x = y := by
    by_contra hne
    let K := T.deleteEdges {s(u, x)}
    have hDK : D ≤ K := deleteEdges_anti (by
      intro e he
      have he' := Set.mem_singleton_iff.mp he
      rw [he']
      exact (T.mem_incidenceSet u x).mpr hx)
    have hKv : K.Adj u y := (deleteEdges_adj).mpr
      ⟨hy, fun he => hne (Sym2.congr_right.mp (Set.mem_singleton_iff.mp he)).symm⟩
    have hbridge := (isAcyclic_iff_forall_isBridge.mp hT.isAcyclic) (e := s(u, x))
      (T.mem_edgeSet.mpr hx)
    exact (SimpleGraph.isBridge_iff.mp hbridge)
      (hKv.reachable.trans ((ConnectedComponent.eq.mp hxy.symm).mono hDK))
  let branches := (univ : Finset D.ConnectedComponent).erase r
  let pick : T.neighborFinset u → branches := fun x => ⟨D.connectedComponentMk x, by
    apply mem_erase.mpr
    exact ⟨fun h => (T.ne_of_adj ((T.mem_neighborFinset _ _).mp x.2)) ((root_eq x).mp h).symm,
      mem_univ _⟩⟩
  have hcard : branches.card = T.degree u := by
    have hb : Function.Bijective pick := by
      refine ⟨?_, ?_⟩
      · intro x y h
        exact Subtype.ext (unique_branch ((T.mem_neighborFinset _ _).mp x.2)
          ((T.mem_neighborFinset _ _).mp y.2) (congrArg Subtype.val h))
      · intro c
        obtain ⟨y, hy, h⟩ := adj_branch c (mem_erase.mp c.2).1
        exact ⟨⟨y, (T.mem_neighborFinset _ _).mpr hy⟩, Subtype.ext h⟩
    simpa only [Fintype.card_coe, T.card_neighborFinset_eq_degree] using
      (Fintype.card_of_bijective hb).symm
  have hbranch (c : D.ConnectedComponent) (hc : c ∈ branches) :
      (∑ x ∈ componentVertices D c, w x) = 1 ∧ (∑ x, w x) = 2 := by
    let C := componentVertices D c
    let R := univ \ C
    have hur : u ∈ R := mem_sdiff.mpr ⟨mem_univ _, fun h =>
      (mem_erase.mp hc).1 ((mem_componentVertices _ _ _).mp h).symm⟩
    have hcproper : C ≠ univ := fun h => (mem_sdiff.mp hur).2 (h ▸ mem_univ u)
    have hcconn : (T.induce (↑C : Set α)).Connected :=
      (componentVertices_connected D c).mono (fun _ _ h => SimpleGraph.deleteIncidenceSet_le T u h)
    have hC := hmin C hcproper hcconn
    have hrproper : R ≠ univ := by
      obtain ⟨x, hx⟩ := c.exists_rep
      exact fun h => (mem_sdiff.mp (show x ∈ R from h ▸ mem_univ _)).2
        ((mem_componentVertices _ _ _).mpr hx)
    have hrconn : (T.induce (↑R : Set α)).Connected := by
      let ru : (↑R : Set α) := ⟨u, hur⟩
      let : Nonempty (↑R : Set α) := ⟨ru⟩
      have hreach (x : (↑R : Set α)) : (T.induce (↑R : Set α)).Reachable ru x := by
        by_cases hx : x.val = u
        · have hx' : x = ru := Subtype.ext hx
          subst x
          exact SimpleGraph.Reachable.rfl
        · let d := D.connectedComponentMk x
          obtain ⟨y, hy, hd⟩ := adj_branch d (fun he => hx ((root_eq _).mp he))
          have hsub : d.supp ⊆ (↑R : Set α) := by
            intro z hz
            apply mem_sdiff.mpr
            refine ⟨mem_univ _, fun h => (mem_sdiff.mp x.2).2 ?_⟩
            apply (mem_componentVertices _ _ _).mpr
            exact ((d.mem_supp_iff z).mp hz).symm.trans ((mem_componentVertices _ _ _).mp h)
          let ry : (↑R : Set α) := ⟨y, hsub ((d.mem_supp_iff y).mpr hd)⟩
          have hury : (T.induce (↑R : Set α)).Adj ru ry := hy
          exact hury.reachable.trans (induced_component_reachable (T.deleteIncidenceSet_le u)
            hsub ((d.mem_supp_iff y).mpr hd) ((d.mem_supp_iff x).mpr rfl))
      exact ⟨fun x y => (hreach x).symm.trans (hreach y)⟩
    have hR := hmin R hrproper hrconn
    have hsplit := sum_sdiff (f := w) (subset_univ C)
    change (∑ x ∈ R, w x) + (∑ x ∈ C, w x) = _ at hsplit
    change (∑ x ∈ C, w x) = 1 ∧ (∑ x, w x) = 2
    constructor <;> omega
  have hs : (∑ c ∈ branches, ∑ x ∈ componentVertices D c, w x) = (T.degree u : ℤ) := by
    rw [sum_congr rfl (fun c hc => (hbranch c hc).1), sum_const, nsmul_eq_mul, mul_one, hcard]
  have hsplit := sum_erase_add (s := univ)
    (f := fun c => ∑ x ∈ componentVertices D c, w x) (mem_univ r)
  change (∑ c ∈ branches, ∑ x ∈ componentVertices D c, w x) +
    (∑ x ∈ componentVertices D r, w x) = _ at hsplit
  rw [hs, root_set, sum_singleton, component_weight_sum] at hsplit
  by_cases h : branches.Nonempty
  · obtain ⟨c, hc⟩ := h
    have he := (hbranch c hc).2
    omega
  · have hempty := not_nonempty_iff_eq_empty.mp h
    rw [hempty, card_empty] at hcard
    omega

/-- A heavy connected set has a connected subset whose spanning tree respects
the degree quotas supplied by its vertex weights. -/
theorem exists_quota_tree (H : SimpleGraph α) (w : α → ℤ)
    (hw : ∀ u, w u ≤ 1)
    (hex : ∃ W : Finset α, (H.induce (↑W : Set α)).Connected ∧ 2 ≤ ∑ x ∈ W, w x) :
    ∃ W : Finset α, ∃ T : SimpleGraph (↑W : Set α), T ≤ H.induce (↑W : Set α) ∧
      T.IsTree ∧ (2 ≤ ∑ x ∈ W, w x) ∧
      ∀ x : (↑W : Set α), ((T.neighborSet x).ncard : ℤ) ≤ 2 - w x := by
  classical
  let P (k : ℕ) := ∃ W : Finset α, W.card = k ∧
    (H.induce (↑W : Set α)).Connected ∧ 2 ≤ ∑ x ∈ W, w x
  have hP : ∃ k, P k := by
    obtain ⟨W, hc, hw⟩ := hex
    exact ⟨W.card, W, rfl, hc, hw⟩
  obtain ⟨W, hk, hc, hweight⟩ := Nat.find_spec hP
  obtain ⟨T, hle, ht⟩ := hc.exists_isTree_le
  let emb : (↑W : Set α) ↪ α := ⟨Subtype.val, Subtype.val_injective⟩
  have hwt : 2 ≤ ∑ x : (↑W : Set α), w x := by
    rw [← sum_attach W w] at hweight
    exact hweight
  have hmin (V : Finset (↑W : Set α)) (hV : V ≠ univ)
      (hcV : (T.induce (↑V : Set (↑W : Set α))).Connected) :
      (∑ x ∈ V, w x) ≤ 1 := by
    let A := V.map emb
    have hA : A.card < W.card := by
      rw [card_map, ← Fintype.card_coe W, ← card_univ]
      exact card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ V, hV⟩)
    let f : (T.induce (↑V : Set (↑W : Set α))) →g H.induce (↑A : Set α) :=
      ⟨fun x => ⟨x.val.val, mem_map.mpr ⟨x.val, x.2, rfl⟩⟩, fun {_ _} h => hle h⟩
    have hsurj : Function.Surjective f := by
      intro a
      obtain ⟨v, hv, he⟩ := mem_map.mp a.2
      exact ⟨⟨v, hv⟩, Subtype.ext he⟩
    have hconn := hcV.map f hsurj
    by_contra! h
    have hh : 2 ≤ ∑ x ∈ A, w x := by
      rw [show A = V.map emb from rfl, sum_map]
      change 2 ≤ ∑ x ∈ V, w (x : α)
      omega
    have hfind : Nat.find hP ≤ A.card := Nat.find_min' hP ⟨A, rfl, hconn, hh⟩
    omega
  refine ⟨W, T, hle, ht, hweight, ?_⟩
  intro x
  rw [T.ncard_neighborSet]
  exact minimal_tree_degree T (fun x => w x) ht hwt hmin x (hw x)

#print axioms component_cost
#print axioms exists_quota_tree

end StarRamsey
```

### `StarRamseyLower.lean`

```lean
import StarRamseyTree

open SimpleGraph Finset
open scoped BigOperators

namespace StarRamsey

variable {α : Type*} [Fintype α]

omit [Fintype α] in
theorem packing_neighborhood [DecidableEq α] {G : SimpleGraph α} {U : Finset α}
    (A : α → Finset α) {n p : ℕ} (hp : 0 < p) (hU : U.card = n)
    (S : Finset α) (hS : S ⊆ U)
    (hcopy : HasCopy (starForest n p) (redGraph G U A)) :
    S.card * p ≤ (S.biUnion A).card := by
  classical
  obtain ⟨f, hf⟩ := hcopy
  have hone (i : Fin n) : (highTags f i).card = 1 := by
    have hle := highTags_sum_le f hf
    have hpos (j : Fin n) : 1 ≤ (highTags f j).card :=
      card_pos.mpr (highTags_nonempty f hp j)
    by_contra h
    have hlt : (∑ _j : Fin n, (1 : ℕ)) < ∑ j, (highTags f j).card :=
      sum_lt_sum (fun j _ => hpos j) ⟨i, mem_univ i, by have := hpos i; omega⟩
    simp at hlt
    omega
  choose tag htag using fun i => card_eq_one.mp (hone i)
  let pick : Fin n → U := fun i => ⟨f (i, tag i), (mem_highTags f).mp (by rw [htag]; simp)⟩
  have hinj : Function.Injective pick := fun _ _ h =>
    congrArg Prod.fst (hf (congrArg Subtype.val h))
  have hsurj : Function.Surjective pick := by
    by_contra h
    have hlt := Fintype.card_lt_of_injective_not_surjective pick hinj h
    simp [hU] at hlt
  let index := (Equiv.ofBijective pick ⟨hinj, hsurj⟩).symm
  choose leaf hleaf using fun i => unique_high_leaves f hf (htag i)
  let idx (x : S) : Fin n := index ⟨x, hS x.2⟩
  have hpick (x : S) : f (idx x, tag (idx x)) = x := by
    exact congrArg Subtype.val (index.symm_apply_apply ⟨x, hS x.2⟩)
  let target := S.biUnion A
  let inj : S × Fin p → target := fun x => ⟨leaf (idx x.1) x.2, by
    apply mem_biUnion.mpr
    refine ⟨x.1, x.1.2, ?_⟩
    rw [← hpick x.1]
    exact (hleaf (idx x.1) x.2).1⟩
  have hi : Function.Injective inj := by
    rintro ⟨u, j⟩ ⟨v, k⟩ he
    have h := congrArg Subtype.val he
    change leaf (idx u) j = leaf (idx v) k at h
    obtain ⟨a, ha⟩ := (hleaf (idx u) j).2
    obtain ⟨b, hb⟩ := (hleaf (idx v) k).2
    have hij : idx u = idx v := congrArg Prod.fst (hf (ha.symm.trans (h.trans hb)))
    have hvals : (u : α) = (v : α) := congrArg (fun x : U => (x : α)) (index.injective hij)
    have huv : u = v := Subtype.ext hvals
    subst v
    exact Prod.ext rfl ((leaf (idx u)).injective h)
  simpa only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] using
    Fintype.card_le_of_injective inj hi

private theorem exceptional_coloring (G : SimpleGraph α) [DecidableRel G.Adj]
    {n p m : ℕ} (hp : 0 < p) (hm : 0 < m) (hc : G.Connected)
    (he : G.edgeFinset.card < n * (m + p) - 1)
    (hU : (high G m).card = n) (hstrong : (strong G (high G m) (m + p - 1)).card = n) :
    ¬Arrows G n p m := by
  classical
  let U := high G m
  change U.card = n at hU
  let M := m + p - 1
  let b (u : α) := (lowNbr G U u).card - M
  have hs : strong G U M = U :=
    eq_of_subset_of_card_le (filter_subset _ _) (by rw [hU, hstrong])
  have hdeg (u : α) (hu : u ∈ U) : (lowNbr G U u).card = M + b u := by
    have hmem : u ∈ strong G U M := hs.symm ▸ hu
    have h : M ≤ (lowNbr G U u).card := (mem_filter.mp hmem).2
    dsimp [b]
    omega
  have hE : G.edgeFinset.card + 2 ≤ U.card * M + U.card := by
    rw [hU, ← Nat.mul_succ]
    dsimp [M]
    rw [show m + p - 1 + 1 = m + p by omega]
    omega
  let H := crossGraph G U
  let w := vertexWeight U b
  have hw (u : α) : w u ≤ 1 := by
    by_cases h : u ∈ U <;> simp [w, vertexWeight, h]
  obtain ⟨W, T, hTH, hT, hweight, hquota⟩ :=
    exists_quota_tree H w hw (exists_heavy_cross_component G U b M hc hdeg hE)
  let S := W.filter (fun x => x ∈ U)
  let L := W.filter (fun x => x ∉ U)
  have hWL : S.card + L.card = W.card := card_filter_add_card_filter_not _
  have hSU : S ⊆ U := fun _ hu => (mem_filter.mp hu).2
  let emb : (↑W : Set α) ↪ α := ⟨Subtype.val, Subtype.val_injective⟩
  let F := T.map emb
  have hF {x y : α} (h : F.Adj x y) :
      x ∈ W ∧ y ∈ W ∧ H.Adj x y := by
    obtain ⟨a, c, hadj, rfl, rfl⟩ := (SimpleGraph.map_adj emb T x y).mp h
    exact ⟨a.2, c.2, hTH hadj⟩
  have hFS : crossGraph F S = F := by
    ext x y
    constructor
    · exact fun h => h.1
    · intro h
      obtain ⟨hx, hy, _, hh | hh⟩ := hF h
      · exact ⟨h, Or.inl ⟨mem_filter.mpr ⟨hx, hh.1⟩, fun hv => hh.2 (hSU hv)⟩⟩
      · exact ⟨h, Or.inr ⟨mem_filter.mpr ⟨hy, hh.1⟩, fun hv => hh.2 (hSU hv)⟩⟩
  let B (u : α) := if u ∈ S then lowNbr F S u else ∅
  have hBS (u : α) (hu : u ∈ S) : B u = F.neighborFinset u := by
    simp only [B, ite_eq_left hu]
    ext v
    rw [mem_lowNbr, F.mem_neighborFinset]
    refine ⟨And.left, fun h => ⟨h, ?_⟩⟩
    have hh : (crossGraph F S).Adj u v := hFS.symm ▸ h
    exact hh.2.elim And.right (fun he => (he.2 hu).elim)
  have hBL {u v : α} (hu : u ∈ S) (hv : v ∈ B u) : v ∈ L := by
    rw [hBS u hu, F.mem_neighborFinset] at hv
    obtain ⟨_, hvW, _, hh | hh⟩ := hF hv
    · exact mem_filter.mpr ⟨hvW, hh.2⟩
    · exact (hh.2 (hSU hu)).elim
  have hsub (u : α) : B u ⊆ lowNbr G U u := by
    by_cases hu : u ∈ S
    · intro v hv
      have hL := (mem_filter.mp (hBL hu hv)).2
      rw [hBS u hu, F.mem_neighborFinset] at hv
      exact (mem_lowNbr _ _ _ _).mpr ⟨(hF hv).2.2.1, hL⟩
    · simp [B, hu]
  have hcap (u : α) : (B u).card ≤ (lowNbr G U u).card - (m - 1) := by
    by_cases hu : u ∈ S
    · rw [hBS u hu, F.card_neighborFinset_eq_degree, hdeg u (hSU hu)]
      let x : (↑W : Set α) := ⟨u, (mem_filter.mp hu).1⟩
      change (T.map emb).degree (emb x) ≤ _
      rw [T.degree_map_apply]
      have hq := hquota x
      rw [T.ncard_neighborSet] at hq
      have hq' : (T.degree x : ℤ) ≤ 2 - ((1 : ℤ) - b u) := by
        simpa [w, x, vertexWeight, hSU hu] using hq
      dsimp [M]
      omega
    · simp [B, hu]
  obtain ⟨A, hA⟩ := choose_red_neighborhoods G U m B hsub hcap
  have hblue := no_blue_star G m hm A (fun u => ⟨(hA u).2.1, (hA u).2.2⟩)
  have hAt (u : α) (hu : u ∈ S) : (A u).card = p + b u := by
    rw [(hA u).2.2, hdeg u (hSU hu)]
    dsimp [M]
    omega
  have hBsum : (∑ u ∈ S, (B u).card) + 1 = W.card := by
    have eq := congrArg Finset.card (edgeFinset_crossGraph F S)
    rw [card_crossEdges _ _ (fun u _ v hv => ((mem_lowNbr F S u v).mp hv).2)] at eq
    have hcards : (crossGraph F S).edgeFinset.card = F.edgeFinset.card := by
      congr 1
      ext e
      simp only [SimpleGraph.mem_edgeFinset]
      rw [hFS]
    -- Normalize the edge-set instances via membership.
    have hcg : (crossGraph F S).edgeFinset.card = ∑ u ∈ S, (lowNbr F S u).card := by
      exact eq
    rw [hcards] at hcg
    have heq : (∑ u ∈ S, (B u).card) = F.edgeFinset.card := by
      rw [hcg]
      exact sum_congr rfl (fun u hu => by simp [B, hu])
    rw [heq, show F.edgeFinset.card = T.edgeFinset.card from card_edgeFinset_map emb T,
      hT.card_edgeFinset]
    exact Fintype.card_coe W
  have hweight' : (∑ u ∈ S, (b u : ℤ)) + 2 ≤ S.card := by
    have hh : (∑ u ∈ W, w u) = (S.card : ℤ) - ∑ u ∈ S, (b u : ℤ) := by
      simp only [w, vertexWeight, ← sum_filter, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one]
      rfl
    rw [hh] at hweight
    omega
  have hweightNat : (∑ u ∈ S, b u) + 2 ≤ S.card := by exact_mod_cast hweight'
  have hNbr : (S.biUnion A).card < S.card * p := by
    let extra (u : α) := A u \ B u
    have hcover : S.biUnion A ⊆ L ∪ S.biUnion extra := by
      intro v hv
      obtain ⟨u, hu, hvu⟩ := mem_biUnion.mp hv
      by_cases h : v ∈ B u
      · exact mem_union_left _ (hBL hu h)
      · exact mem_union_right _ (mem_biUnion.mpr ⟨u, hu, mem_sdiff.mpr ⟨hvu, h⟩⟩)
    have hcard := (card_le_card hcover).trans
      ((card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
    have hsum : (∑ u ∈ S, (extra u).card) + (∑ u ∈ S, (B u).card) =
        S.card * p + ∑ u ∈ S, b u := by
      calc
        _ = ∑ u ∈ S, ((extra u).card + (B u).card) := sum_add_distrib.symm
        _ = ∑ u ∈ S, (p + b u) := sum_congr rfl (fun u hu =>
          (card_sdiff_add_card_eq_card (hA u).1).trans (hAt u hu))
        _ = _ := by simp only [sum_add_distrib, sum_const, smul_eq_mul]
    omega
  intro harr
  rcases harr (redGraph G U A) (redGraph_le G U A) with hred | hblue'
  · exact (not_lt_of_ge (packing_neighborhood A hp hU S hSU hred)) hNbr
  · exact hblue hblue'

theorem connectedRamsey_lower (G : SimpleGraph α) [DecidableRel G.Adj]
    {n p m : ℕ} (hn : 0 < n) (hp : 0 < p) (hm : 5 * (n + p) ≤ m)
    (hc : G.Connected) (he : G.edgeFinset.card < n * (m + p) - 1) :
    ¬Arrows G n p m := by
  classical
  have hm' : 0 < m := by omega
  let U := high G m
  obtain ⟨A, hA⟩ := choose_red_neighborhoods G U m (fun _ => ∅)
    (fun _ => empty_subset _) (by simp)
  intro harr
  rcases harr (redGraph G U A) (redGraph_le G U A) with hred | hblue
  · obtain ⟨ht, hts⟩ := packing_necessary G U A hp (fun u => (hA u).2.2) hred
    obtain ⟨hU, hs⟩ := exceptional_counts G hn hp hm he ht hts
    exact exceptional_coloring G hp hm' hc he hU hs harr
  · exact no_blue_star G m hm' A (fun u => ⟨(hA u).2.1, (hA u).2.2⟩) hblue

#print axioms connectedRamsey_lower

end StarRamsey
```

### `StarRamseyConjecture.lean`

```lean
import StarRamseySemantics
import StarRamseyUpper
import StarRamseyLower

namespace StarRamsey

theorem connectedRamsey_eq_five (n p m : ℕ) (hn : 0 < n) (hp : 0 < p)
    (hm : 5 * (n + p) ≤ m) :
    IsLeast {e : ℕ | ConnectedRamseyHost n p m e} (n * (m + p) - 1) := by
  classical
  refine ⟨connectedRamsey_upper n p m hn (by omega), ?_⟩
  rintro e ⟨v, G, hc, he, ha⟩
  by_contra! h
  have hlt : G.edgeFinset.card < n * (m + p) - 1 := he.trans_lt h
  exact connectedRamsey_lower G hn hp hm hc hlt ha

theorem mathdb_362603 :
    ∃ c : ℝ, 0 < c ∧
      ∀ n p m : ℕ, 0 < n → 0 < p → 0 < m →
        c * ((n : ℝ) + (p : ℝ)) ≤ (m : ℝ) →
        IsLeast {e : ℕ | ConnectedRamseyHost n p m e} (n * (m + p) - 1) := by
  refine ⟨5, by norm_num, ?_⟩
  intro n p m hn hp _ h
  exact connectedRamsey_eq_five n p m hn hp (by exact_mod_cast h)

#check connectedRamsey_upper
#check connectedRamsey_lower
#check connectedRamsey_eq_five
#check mathdb_362603
#print ConnectedRamseyHost
#print Arrows
#print HasCopy
#print starForest
#print axioms connectedRamsey_upper
#print axioms connectedRamsey_lower
#print axioms connectedRamsey_eq_five
#print axioms mathdb_362603

end StarRamsey
```
