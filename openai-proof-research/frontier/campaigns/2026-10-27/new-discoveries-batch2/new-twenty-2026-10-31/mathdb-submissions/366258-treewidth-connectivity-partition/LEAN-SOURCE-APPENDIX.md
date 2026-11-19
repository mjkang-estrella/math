# MathDB 366258 exact Lean source appendix

The first four modules form the split build. The fifth is the standalone module and is replayed separately from an empty build. Each block preserves the author source bytes.

## Core.lean

```lean
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open SimpleGraph
open scoped Sym2

namespace MathDB366258

universe u v
variable {V : Type u}

structure Decomposition (G : SimpleGraph V) (k : ℤ) (T : Type v) where
  tree : SimpleGraph T
  isTree : tree.IsTree
  bag : T → Finset V
  bound : ∀ t, ((bag t).card : ℤ) ≤ k + 1
  covers : ∀ x, ∃ t, x ∈ bag t
  edge : ∀ ⦃x y⦄, G.Adj x y → ∃ t, x ∈ bag t ∧ y ∈ bag t
  occurs : ∀ x, (tree.induce {t | x ∈ bag t}).Connected

def WidthLE (G : SimpleGraph V) (k : ℤ) : Prop :=
  ∃ T : Type v, Nonempty (Decomposition G k T)

def VertexConnected (G : SimpleGraph V) (k : ℤ) : Prop :=
  k < (Nat.card V : ℤ) ∧
    ∀ S : Finset V, (S.card : ℤ) < k → (G.induce {x | x ∉ S}).Connected

abbrev Vertex := Fin 4 ⊕ (Fin 4 × Fin 3)
abbrev core (u : Fin 4) : Vertex := .inl u
abbrev gadget (u : Fin 4) (j : Fin 3) : Vertex := .inr (u, j)

def inA (u a : Fin 4) : Prop := a = u + 2 ∨ a = u + 3
instance (u a : Fin 4) : Decidable (inA u a) := inferInstanceAs (Decidable (_ ∨ _))

def cross (a u : Fin 4) (j : Fin 3) : Prop :=
  if j = 0 then a = u else inA u a
instance (a u : Fin 4) (j : Fin 3) : Decidable (cross a u j) := by
  unfold cross
  infer_instance

def adjacent : Vertex → Vertex → Prop
  | .inl a, .inl b => a ≠ b
  | .inl a, .inr (u,j) => cross a u j
  | .inr (u,j), .inl a => cross a u j
  | .inr (u,i), .inr (w,j) => u = w ∧ ((i = 0 ∧ j ≠ 0) ∨ (j = 0 ∧ i ≠ 0))

instance : DecidableRel adjacent := fun x y => by
  rcases x with a | ⟨u,i⟩ <;> rcases y with b | ⟨w,j⟩ <;> unfold adjacent <;>
    infer_instance

def witness : SimpleGraph Vertex where
  Adj := adjacent
  symm := ⟨by
    intro x y h
    rcases x with a | ⟨u,i⟩ <;> rcases y with b | ⟨w,j⟩
    · exact Ne.symm h
    · exact h
    · exact h
    · exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by
    intro x h
    rcases x with a | ⟨u,i⟩
    · exact h rfl
    · exact h.2.elim (fun e => e.2 e.1) (fun e => e.2 e.1)⟩

instance : DecidableRel witness.Adj := inferInstanceAs (DecidableRel adjacent)

theorem witness_order : Fintype.card Vertex = 16 := by decide

theorem witness_edges : witness.edgeFinset.card = 34 := by decide

abbrev Node := Option (Fin 4 × Fin 3)

def parent : Fin 4 × Fin 3 → Node
  | (u,j) => if j = 0 then none else some (u,0)

def nodeAdj (x y : Node) : Prop :=
  (∃ z : Fin 4 × Fin 3, x = some z ∧ y = parent z) ∨
    (∃ z : Fin 4 × Fin 3, y = some z ∧ x = parent z)

instance : DecidableRel nodeAdj := fun x y => by
  unfold nodeAdj
  infer_instance

def bagTree : SimpleGraph Node where
  Adj := nodeAdj
  symm := ⟨fun {_ _} h => h.symm⟩
  loopless := ⟨by
    change ∀ n : Node, ¬ nodeAdj n n
    decide⟩

instance : DecidableRel bagTree.Adj := inferInstanceAs (DecidableRel nodeAdj)

def bags : Node → Finset Vertex
  | none => Finset.univ.image core
  | some (u,j) => {core (u+2), core (u+3), gadget u 0,
      if j = 0 then core u else gadget u j}

theorem bag_order : Fintype.card Node = 13 := by decide
theorem bag_edges : bagTree.edgeFinset.card = 12 := by decide
theorem bag_size : ∀ t, (bags t).card = 4 := by decide

#eval Lean.versionString

theorem short_reachable {W : Type*} {G : SimpleGraph W} {x y : W}
    (h : x = y ∨ G.Adj x y ∨ ∃ m, G.Adj x m ∧ G.Adj m y) :
    G.Reachable x y := by
  rcases h with rfl | h | ⟨m, h, h'⟩
  · exact .refl _
  · exact h.reachable
  · exact h.reachable.trans h'.reachable

theorem short_induce {W : Type*} {G : SimpleGraph W} {S : Set W} (x y : S)
    (h : x.val = y.val ∨ G.Adj x.val y.val ∨
      ∃ m ∈ S, G.Adj x.val m ∧ G.Adj m y.val) : (G.induce S).Reachable x y := by
  apply short_reachable
  rcases h with h | h | ⟨m, hm, h₁, h₂⟩
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨⟨m, hm⟩, h₁, h₂⟩)

theorem node_short : ∀ x : Node, x = none ∨ bagTree.Adj x none ∨
    ∃ m, bagTree.Adj x m ∧ bagTree.Adj m none := by decide

theorem tree_isTree : bagTree.IsTree := by
  rw [isTree_iff_connected_and_card]
  refine And.intro (show bagTree.Connected from { preconnected := ?_, nonempty := ⟨none⟩ }) ?_
  · intro x y
    exact (short_reachable (node_short x)).trans (short_reachable (node_short y)).symm
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card, bag_edges,
      bag_order]

def home : Vertex → Node
  | .inl _ => none
  | .inr z => some z

theorem home_mem : ∀ x, x ∈ bags (home x) := by decide
theorem bag_local : ∀ (x : Vertex) (t : Node), x ∈ bags t →
    t = home x ∨ bagTree.Adj t (home x) ∨
      ∃ m, x ∈ bags m ∧ bagTree.Adj t m ∧ bagTree.Adj m (home x) := by decide
theorem bag_cover_edge : ∀ (x y : Vertex), witness.Adj x y →
    ∃ n, x ∈ bags n ∧ y ∈ bags n := by decide

def concreteDecomposition : Decomposition witness 3 Node where
  tree := bagTree
  isTree := tree_isTree
  bag := bags
  bound t := by rw [bag_size]; decide
  covers x := ⟨home x, home_mem x⟩
  edge := fun {x y} => bag_cover_edge x y
  occurs x := by
    let r : {t : Node // x ∈ bags t} := ⟨home x, home_mem x⟩
    have go (t : {t : Node // x ∈ bags t}) :
        (bagTree.induce {t | x ∈ bags t}).Reachable t r :=
      short_induce t r (bag_local x t t.property)
    exact { preconnected := fun t s => (go t).trans (go s).symm, nonempty := ⟨r⟩ }

theorem witness_width : WidthLE.{0,0} witness 3 :=
  ⟨Node, ⟨concreteDecomposition⟩⟩

end MathDB366258
```

## Helly.lean

```lean
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open SimpleGraph
open scoped Sym2

namespace MathDB366258
namespace RootedHelly

variable {T : Type*} {G : SimpleGraph T}

theorem support_induced {S : Set T} {a b : S} (p : (G.induce S).Walk a b) :
    ∀ z ∈ (p.map (Embedding.induce S).toHom).support, z ∈ S := by
  intro z hz
  rw [Walk.support_map] at hz
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
  exact w.property

theorem path_eq (h : G.IsTree) {a b : T} (p q : G.Path a b) : p = q :=
  (h.isAcyclic.subsingleton_path a b).elim p q

theorem path_inside (h : G.IsTree) {S : Set T} (hc : (G.induce S).Connected)
    {a b : T} (ha : a ∈ S) (hb : b ∈ S) (p : G.Path a b) :
    ∀ z ∈ p.val.support, z ∈ S := by
  classical
  obtain ⟨w⟩ := hc ⟨a, ha⟩ ⟨b, hb⟩
  let q : G.Walk a b := w.map (Embedding.induce S).toHom
  rw [path_eq h p q.toPath]
  exact fun z hz => support_induced w z (q.support_toPath_subset_support hz)

noncomputable def rootPath (h : G.IsTree) (r a : T) : G.Path r a := by
  classical
  exact (Classical.choice (h.connected r a)).toPath

noncomputable def depth (h : G.IsTree) (r a : T) : ℕ :=
  (rootPath h r a).val.length

theorem depth_prefix (h : G.IsTree) (r : T) {x a : T} (p : G.Path r x)
    [DecidableEq T] (ha : a ∈ p.val.support) :
    depth h r a = (p.val.takeUntil a ha).length := by
  unfold depth
  exact congrArg (fun w : G.Path r a => w.val.length)
    (path_eq h _ ⟨_, p.property.takeUntil ha⟩)

theorem nearest_on_path (h : G.IsTree) (r : T) {S : Set T}
    (hc : (G.induce S).Connected) {a x : T} (ha : a ∈ S) (hx : x ∈ S)
    (hm : ∀ b ∈ S, depth h r a ≤ depth h r b) :
    a ∈ (rootPath h r x).val.support := by
  classical
  by_contra hn
  have hra : r ≠ a := fun e => hn (e ▸ (rootPath h r x).val.start_mem_support)
  let p := (rootPath h r a).val
  have hnil : ¬ p.Nil := by
    intro he
    exact hra he.eq
  let b := p.penultimate
  have hadj : G.Adj b a := p.adj_penultimate hnil
  have hlast : s(b, a) ∈ p.edges := by
    have he : p.edges ≠ [] := by simpa using hnil
    rw [← Walk.getLast_edges_eq_mk_penultimate_end he]
    exact List.getLast_mem he
  obtain ⟨wi⟩ := hc ⟨x, hx⟩ ⟨a, ha⟩
  let w : G.Walk x a := wi.map (Embedding.induce S).toHom
  let q := (rootPath h r x).val
  have hpq : p = ((q.append w).toPath).val :=
    congrArg Subtype.val (path_eq h (rootPath h r a) (q.append w).toPath)
  have hedge : s(b, a) ∈ q.edges ++ w.edges := by
    rw [← Walk.edges_append]
    apply (q.append w).edges_bypass_sublist_edges.subset
    change s(b, a) ∈ ((q.append w).toPath).val.edges
    rw [← hpq]
    exact hlast
  have hb : b ∈ S := by
    rcases List.mem_append.mp hedge with hq | hw
    · exact (hn (q.snd_mem_support_of_mem_edges hq)).elim
    · exact support_induced wi b (w.fst_mem_support_of_mem_edges hw)
  have hbs : b ∈ p.support := p.fst_mem_support_of_mem_edges hlast
  have hprefix := depth_prefix h r (rootPath h r a) hbs
  have hle := p.length_takeUntil_le_length hbs
  have hlt : (p.takeUntil b hbs).length < p.length := by
    refine lt_of_le_of_ne hle ?_
    intro he
    have he' := Walk.getVert_length_takeUntil (p := p) hbs
    rw [he, Walk.getVert_length] at he'
    exact hadj.ne he'.symm
  have hh := hm b hb
  change depth h r b = (p.takeUntil b hbs).length at hprefix
  change p.length ≤ depth h r b at hh
  omega

theorem suffix_of_depth (h : G.IsTree) {r x a b : T} (p : G.Path r x)
    [DecidableEq T] (ha : a ∈ p.val.support) (hb : b ∈ p.val.support)
    (hle : depth h r a ≤ depth h r b) :
    b ∈ (p.val.dropUntil a ha).support := by
  by_contra hn
  have happ := p.val.take_spec ha
  have hmem : b ∈ (p.val.takeUntil a ha).support := by
    have hh : b ∈ ((p.val.takeUntil a ha).append (p.val.dropUntil a ha)).support :=
      happ.symm ▸ hb
    exact (((Walk.mem_support_append_iff _ _).mp hh).resolve_right hn)
  have hne : b ≠ a := fun e => hn (e ▸ (p.val.dropUntil a ha).start_mem_support)
  let pre := p.val.takeUntil a ha
  have h₁ := depth_prefix h r p ha
  have h₂ := depth_prefix h r (⟨pre, p.property.takeUntil ha⟩ : G.Path r a) hmem
  have hlt : (pre.takeUntil b hmem).length < pre.length := by
    refine lt_of_le_of_ne (pre.length_takeUntil_le_length hmem) ?_
    intro he
    have he' := Walk.getVert_length_takeUntil (p := pre) hmem
    rw [he, Walk.getVert_length] at he'
    exact hne he'.symm
  change depth h r a = pre.length at h₁
  change depth h r b = (pre.takeUntil b hmem).length at h₂
  omega

theorem helly {ι : Type*} [Fintype ι] [Nonempty ι] (h : G.IsTree)
    (S : ι → Set T) (hc : ∀ i, (G.induce (S i)).Connected)
    (hit : ∀ i j, ∃ x, x ∈ S i ∧ x ∈ S j) :
    ∃ x, ∀ i, x ∈ S i := by
  classical
  let r : T := Classical.choice h.connected.nonempty
  have nearest (i : ι) : ∃ a ∈ S i, ∀ b ∈ S i, depth h r a ≤ depth h r b := by
    have ex : ∃ n : ℕ, ∃ a ∈ S i, depth h r a = n := by
      obtain ⟨a, ha, _⟩ := hit i i
      exact ⟨_, a, ha, rfl⟩
    obtain ⟨a, ha, he⟩ := Nat.find_spec ex
    exact ⟨a, ha, fun b hb => he ▸ Nat.find_min' ex ⟨b, hb, rfl⟩⟩
  choose a ma low using nearest
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun i => depth h r (a i))
    Finset.univ_nonempty
  refine ⟨a j, fun i => ?_⟩
  obtain ⟨x, hxi, hxj⟩ := hit i j
  have hi := nearest_on_path h r (hc i) (ma i) hxi (low i)
  have hq := nearest_on_path h r (hc j) (ma j) hxj (low j)
  have hs := suffix_of_depth h (rootPath h r x) hi hq (hj i (Finset.mem_univ i))
  exact path_inside h (hc i) (ma i) hxi
    ⟨_, (rootPath h r x).property.dropUntil hi⟩ _ hs

end RootedHelly
end MathDB366258
```

## Obstruction.lean

```lean
import Core
import Helly

open SimpleGraph

namespace MathDB366258

universe u v
variable {V : Type u} {G : SimpleGraph V} {k : ℤ} {T : Type v}

def Decomposition.meets (D : Decomposition G k T) (B : Set V) : Set T :=
  {t | ∃ x ∈ B, x ∈ D.bag t}

theorem Decomposition.one_vertex_reachable (D : Decomposition G k T) {B : Set V}
    {x : V} (hx : x ∈ B) {t s : D.meets B} (ht : x ∈ D.bag t.val)
    (hs : x ∈ D.bag s.val) : (D.tree.induce (D.meets B)).Reachable t s := by
  let f := (D.tree.induceHomOfLE (show {a | x ∈ D.bag a} ⊆ D.meets B from
    fun a h => ⟨x, hx, h⟩)).toHom
  exact (D.occurs x ⟨t, ht⟩ ⟨s, hs⟩).map f

theorem Decomposition.walk_meets (D : Decomposition G k T) {B : Set V}
    {x y : B} (p : (G.induce B).Walk x y) :
    ∀ (t s : D.meets B), x.val ∈ D.bag t.val → y.val ∈ D.bag s.val →
      (D.tree.induce (D.meets B)).Reachable t s := by
  induction p with
  | @nil a =>
    intro t s ht hs
    exact D.one_vertex_reachable a.property ht hs
  | @cons a b c e p ih =>
    intro t s ht hs
    obtain ⟨m, ham, hbm⟩ := D.edge (show G.Adj a.val b.val from e)
    let m' : D.meets B := ⟨m, a.val, a.property, ham⟩
    exact (D.one_vertex_reachable a.property ht (show a.val ∈ D.bag m'.val from ham)).trans
      (ih m' s hbm hs)

theorem Decomposition.meets_connected (D : Decomposition G k T) {B : Set V}
    (h : (G.induce B).Connected) : (D.tree.induce (D.meets B)).Connected := by
  refine { preconnected := ?_, nonempty := ?_ }
  · intro t s
    obtain ⟨x, hx, hxt⟩ := t.property
    obtain ⟨y, hy, hys⟩ := s.property
    obtain ⟨p⟩ := h ⟨x, hx⟩ ⟨y, hy⟩
    exact D.walk_meets p t s hxt hys
  · obtain ⟨x⟩ := h.nonempty
    obtain ⟨t, ht⟩ := D.covers x.val
    exact ⟨⟨t, x.val, x.property, ht⟩⟩

/-- The index tree can be infinite and is in an independent universe. -/
theorem Decomposition.branch_card_bound (D : Decomposition G k T)
    {ι : Type*} [Fintype ι] [Nonempty ι] (B : ι → Set V)
    (hconn : ∀ i, (G.induce (B i)).Connected)
    (hdisj : ∀ i j x, x ∈ B i → x ∈ B j → i = j)
    (htouch : ∀ i j, i ≠ j → ∃ x ∈ B i, ∃ y ∈ B j, G.Adj x y) :
    (Fintype.card ι : ℤ) ≤ k + 1 := by
  classical
  have hit (i j : ι) : ∃ t, t ∈ D.meets (B i) ∧ t ∈ D.meets (B j) := by
    by_cases hij : i = j
    · subst j
      obtain ⟨x⟩ := (hconn i).nonempty
      obtain ⟨t, ht⟩ := D.covers x.val
      exact ⟨t, ⟨x.val, x.property, ht⟩, ⟨x.val, x.property, ht⟩⟩
    · obtain ⟨x, hx, y, hy, hxy⟩ := htouch i j hij
      obtain ⟨t, hxt, hyt⟩ := D.edge hxy
      exact ⟨t, ⟨x, hx, hxt⟩, ⟨y, hy, hyt⟩⟩
  obtain ⟨t, ht⟩ := RootedHelly.helly D.isTree (fun i => D.meets (B i))
    (fun i => D.meets_connected (hconn i)) hit
  have representatives (i : ι) : ∃ x, x ∈ B i ∧ x ∈ D.bag t := ht i
  choose xs hb hbag using representatives
  let f : ι → {x // x ∈ D.bag t} := fun i => ⟨xs i, hbag i⟩
  have hf : Function.Injective f := by
    intro i j he
    have e : xs i = xs j := congrArg Subtype.val he
    exact hdisj i j (xs i) (hb i) (e.symm ▸ hb j)
  have hcard : Fintype.card ι ≤ (D.bag t).card := by
    simpa using Fintype.card_le_of_injective f hf
  exact (Int.ofNat_le.mpr hcard).trans (D.bound t)

/-- A singleton or one edge is enough for each of the four witness branches. -/
theorem four_pairs_obstruction (H : SimpleGraph V) (p : Fin 4 → Bool → V)
    (hc : ∀ i, p i false = p i true ∨ H.Adj (p i false) (p i true))
    (hd : ∀ i j b d, p i b = p j d → i = j)
    (ht : ∀ i j, i ≠ j → ∃ b d, H.Adj (p i b) (p j d)) :
    ¬ WidthLE.{u,v} H 2 := by
  intro ⟨T, ⟨D⟩⟩
  let B (i : Fin 4) : Set V := {x | ∃ b, x = p i b}
  have hconn (i : Fin 4) : (H.induce (B i)).Connected := by
    let r : B i := ⟨p i false, false, rfl⟩
    have go (x : B i) : (H.induce (B i)).Reachable r x := by
      obtain ⟨b, he⟩ := x.property
      apply short_induce
      cases b
      · exact Or.inl he.symm
      · rcases hc i with heq | heq
        · exact Or.inl (heq.trans he.symm)
        · exact Or.inr (Or.inl (he ▸ heq))
    exact { preconnected := fun x y => (go x).symm.trans (go y), nonempty := ⟨r⟩ }
  have hdisj (i j : Fin 4) (x : V) (hi : x ∈ B i) (hj : x ∈ B j) : i = j := by
    obtain ⟨b, hb⟩ := hi
    obtain ⟨d, hd'⟩ := hj
    exact hd i j b d (hb.symm.trans hd')
  have htouch (i j : Fin 4) (hn : i ≠ j) : ∃ x ∈ B i, ∃ y ∈ B j, H.Adj x y := by
    obtain ⟨b, d, hadj⟩ := ht i j hn
    exact ⟨p i b, ⟨b, rfl⟩, p j d, ⟨d, rfl⟩, hadj⟩
  have hh := D.branch_card_bound B hconn hdisj htouch
  simp at hh

end MathDB366258
```

## Endpoint.lean

```lean
import Obstruction

open SimpleGraph

namespace MathDB366258

/-- Three distinct candidate vertices cannot all belong to a deletion of size less than three. -/
theorem survives_three {W : Type*} (S : Finset W) (hs : (S.card : ℤ) < 3)
    (f : Fin 3 → W) (hf : Function.Injective f) : ∃ i, f i ∉ S := by
  classical
  by_contra! hall
  have hsub : Finset.univ.image f ⊆ S := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hall i
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin] at hcard
  omega

def sideX (u : Fin 4) (i : Fin 3) : Vertex :=
  if i = 0 then gadget u 0 else if i = 1 then core (u+2) else core (u+3)

def sideY (u : Fin 4) (i : Fin 3) : Vertex :=
  if i = 0 then core u else gadget u i

def attachment (u : Fin 4) (i : Fin 3) : Fin 4 :=
  if i = 0 then u else if i = 1 then u+2 else u+3

def opposite (u : Fin 4) (j i : Fin 3) : Vertex :=
  if j = 0 then sideY u i else sideX u i

theorem opposite_inj : ∀ (u : Fin 4) (j i l : Fin 3),
    opposite u j i = opposite u j l → i = l := by decide

theorem attachment_inj : ∀ (u : Fin 4) (i l : Fin 3),
    core (attachment u i) = core (attachment u l) → i = l := by decide

theorem core_reaches : ∀ a b : Fin 4, core a = core b ∨ witness.Adj (core a) (core b) :=
  by decide

theorem gadget_reaches : ∀ (u : Fin 4) (j i l : Fin 3),
    witness.Adj (gadget u j) (core (attachment u l)) ∨
      (witness.Adj (gadget u j) (opposite u j i) ∧
       witness.Adj (opposite u j i) (core (attachment u l))) := by decide

theorem witness_connected : VertexConnected witness 3 := by
  refine ⟨?_, ?_⟩
  · rw [Nat.card_eq_fintype_card, witness_order]
    decide
  · intro S hs
    let W : Set Vertex := {x | x ∉ S}
    let H := witness.induce W
    obtain ⟨i, hi⟩ := survives_three S hs (fun j => core (attachment 0 j))
      (fun {_ _} => attachment_inj 0 _ _)
    let r : W := ⟨core (attachment 0 i), hi⟩
    have nearCore (x : W) : ∃ (a : Fin 4) (ha : core a ∈ W), H.Reachable x ⟨core a, ha⟩ := by
      rcases x with ⟨x, hx⟩
      rcases x with a | ⟨u,j⟩
      · exact ⟨a, hx, .refl _⟩
      · obtain ⟨l, hl⟩ := survives_three S hs (fun m => core (attachment u m))
          (fun {_ _} => attachment_inj u _ _)
        obtain ⟨m, hm⟩ := survives_three S hs (opposite u j)
          (fun {_ _} => opposite_inj u j _ _)
        refine ⟨attachment u l, hl, short_induce _ _ ?_⟩
        rcases gadget_reaches u j m l with edge | ⟨edge₁, edge₂⟩
        · exact Or.inr (Or.inl edge)
        · exact Or.inr (Or.inr ⟨_, hm, edge₁, edge₂⟩)
    have go (x : W) : H.Reachable x r := by
      obtain ⟨a, ha, hp⟩ := nearCore x
      apply hp.trans
      apply short_induce
      exact (core_reaches a (attachment 0 i)).imp_right Or.inl
    exact { preconnected := fun x y => (go x).trans (go y).symm, nonempty := ⟨r⟩ }

/-- Transfer the four connected branches to the induced complement's vertex type. -/
theorem induced_pairs {S : Set Vertex} (p : Fin 4 → Bool → Vertex)
    (hS : ∀ i b, p i b ∈ S)
    (hc : ∀ i, p i false = p i true ∨ witness.Adj (p i false) (p i true))
    (hd : ∀ i j b d, p i b = p j d → i = j)
    (ht : ∀ i j, i ≠ j → ∃ b d, witness.Adj (p i b) (p j d)) :
    ¬ WidthLE.{0,v} (witness.induce S) 2 := by
  apply four_pairs_obstruction (witness.induce S) (fun i b => ⟨p i b, hS i b⟩)
  · intro i
    exact (hc i).imp_left Subtype.ext
  · intro i j b d h
    exact hd i j b d (congrArg Subtype.val h)
  · exact ht

def corePairs (i : Fin 4) (_ : Bool) : Vertex := core i

theorem core_disjoint : ∀ (i j : Fin 4) (b d : Bool),
    corePairs i b = corePairs j d → i = j := by decide

theorem core_touch : ∀ (i j : Fin 4), i ≠ j →
    ∃ b d : Bool, witness.Adj (corePairs i b) (corePairs j d) := by decide

def gadgetPairs (u i : Fin 4) (b : Bool) : Vertex :=
  if i = 0 then core (u+2) else if i = 1 then core (u+3) else
    if i = 2 then gadget u 1 else gadget u (if b then 2 else 0)

theorem gadget_pair_connected : ∀ (u i : Fin 4), gadgetPairs u i false = gadgetPairs u i true ∨
    witness.Adj (gadgetPairs u i false) (gadgetPairs u i true) := by decide

theorem gadget_pair_disjoint : ∀ (u i j : Fin 4) (b d : Bool),
    gadgetPairs u i b = gadgetPairs u j d → i = j := by decide

theorem gadget_pair_touch : ∀ (u i j : Fin 4), i ≠ j →
    ∃ b d : Bool, witness.Adj (gadgetPairs u i b) (gadgetPairs u j d) := by decide

theorem gadget_pair_member : ∀ (u i : Fin 4) (b : Bool),
    gadgetPairs u i b = core (u+2) ∨ gadgetPairs u i b = core (u+3) ∨
    gadgetPairs u i b = gadget u 0 ∨ gadgetPairs u i b = gadget u 1 ∨
    gadgetPairs u i b = gadget u 2 := by decide

theorem center_adj : ∀ u : Fin 4,
    witness.Adj (core u) (core (u+2)) ∧ witness.Adj (core u) (core (u+3)) ∧
    witness.Adj (core u) (gadget u 0) := by decide

theorem center_neighbors : ∀ (u : Fin 4) (x : Vertex),
    witness.Adj (gadget u 0) x →
      x = core u ∨ x = gadget u 1 ∨ x = gadget u 2 := by decide

theorem center_avoids_A : ∀ u : Fin 4, gadget u 0 ≠ core (u+2) ∧
    ¬ witness.Adj (gadget u 0) (core (u+2)) := by decide

theorem missing_leaf_cut (I : Set Vertex) (u : Fin 4)
    (hu : core u ∈ I) (hc : gadget u 0 ∉ I) (ha : core (u+2) ∉ I)
    (hm : gadget u 1 ∈ I ∨ gadget u 2 ∈ I) :
    ¬ VertexConnected (witness.induce Iᶜ) 2 := by
  classical
  intro hconn
  let W : Set Vertex := Iᶜ
  let H := witness.induce W
  let c : W := ⟨gadget u 0, hc⟩
  let a : W := ⟨core (u+2), ha⟩
  let _ : Fintype W := Fintype.ofFinite _
  let cut : Finset W := Finset.univ.filter (H.Adj c)
  have memcut (x : W) : x ∈ cut ↔ H.Adj c x := by simp [cut]
  have htwo (x : W) (hx : x ∈ cut) : x.val = gadget u 1 ∨ x.val = gadget u 2 := by
    rcases center_neighbors u x.val ((memcut x).mp hx) with e | e
    · exact (x.property (e.symm ▸ hu)).elim
    · exact e
  have hcard : cut.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    apply Subtype.ext
    rcases hm with h₁ | h₂
    · have x₂ := (htwo x hx).resolve_left (fun e => x.property (e.symm ▸ h₁))
      have y₂ := (htwo y hy).resolve_left (fun e => y.property (e.symm ▸ h₁))
      exact x₂.trans y₂.symm
    · have x₁ := (htwo x hx).resolve_right (fun e => x.property (e.symm ▸ h₂))
      have y₁ := (htwo y hy).resolve_right (fun e => y.property (e.symm ▸ h₂))
      exact x₁.trans y₁.symm
  have hc' : c ∉ cut := fun hm => ((memcut c).mp hm).ne rfl
  have ha' : a ∉ cut := fun hm => (center_avoids_A u).2 ((memcut a).mp hm)
  obtain ⟨p⟩ := (hconn.2 cut (by omega)) ⟨c, hc'⟩ ⟨a, ha'⟩
  have hnil : ¬ p.Nil := by
    intro hn
    exact (center_avoids_A u).1 (congrArg (fun x => x.val.val) hn.eq)
  exact p.snd.property ((memcut p.snd.val).mpr (p.adj_snd hnil))

theorem witness_alternatives (I : Set Vertex) (hI : witness.IsIndepSet I) :
    ¬ WidthLE.{0,v} (witness.induce Iᶜ) 2 ∨
      ¬ VertexConnected (witness.induce Iᶜ) 2 := by
  classical
  by_cases has : ∃ u : Fin 4, core u ∈ I
  · obtain ⟨u, hu⟩ := has
    have survives (x : Vertex) (h : witness.Adj (core u) x) : x ∉ I :=
      fun hx => hI hu hx h.ne h
    have h₂ := survives _ (center_adj u).1
    have h₃ := survives _ (center_adj u).2.1
    have hc := survives _ (center_adj u).2.2
    by_cases missing : gadget u 1 ∈ I ∨ gadget u 2 ∈ I
    · exact Or.inr (missing_leaf_cut I u hu hc h₂ missing)
    · left
      apply induced_pairs (gadgetPairs u) ?_ (gadget_pair_connected u)
        (gadget_pair_disjoint u) (gadget_pair_touch u)
      intro i b
      rcases gadget_pair_member u i b with e | e | e | e | e
      · exact e.symm ▸ h₂
      · exact e.symm ▸ h₃
      · exact e.symm ▸ hc
      · exact e.symm ▸ (fun h => missing (Or.inl h))
      · exact e.symm ▸ (fun h => missing (Or.inr h))
  · exact Or.inl (induced_pairs corePairs (fun i _ h => has ⟨i, h⟩)
      (fun _ => Or.inl rfl) core_disjoint core_touch)

theorem witness_failure (I : Set Vertex) (hI : witness.IsIndepSet I) :
    ¬ (WidthLE.{0,v} (witness.induce Iᶜ) 2 ∧
      VertexConnected (witness.induce Iᶜ) 2) := by
  intro ⟨hw, hc⟩
  exact (witness_alternatives I hI).elim (fun bad => bad hw) (fun bad => bad hc)

/-- Conjecture 36, using the integer parameter of the MathDB row. -/
def NativeConjecture : Prop :=
  ∀ (V : Type) [Finite V] (G : SimpleGraph V) (k : ℤ),
    WidthLE.{0,0} G k → VertexConnected G k →
    ∃ I : Set V, G.IsIndepSet I ∧
      WidthLE.{0,0} (G.induce Iᶜ) (k - 1) ∧ VertexConnected (G.induce Iᶜ) (k - 1)

theorem native_refutation : ¬ NativeConjecture := by
  intro h
  obtain ⟨I, hi, hw, hc⟩ := h Vertex witness (3 : ℤ) witness_width witness_connected
  exact witness_failure I hi ⟨hw, hc⟩

#check Decomposition
#check WidthLE
#check VertexConnected
#check witness
#check witness_width
#check witness_connected
#check witness_alternatives
#check witness_failure
#check NativeConjecture
#check native_refutation
#print NativeConjecture
#print axioms witness_order
#print axioms witness_edges
#print axioms tree_isTree
#print axioms witness_width
#print axioms witness_connected
#print axioms RootedHelly.helly
#print axioms Decomposition.branch_card_bound
#print axioms witness_alternatives
#print axioms witness_failure
#print axioms native_refutation

end MathDB366258
```

## MathDB366258.lean

```lean
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open SimpleGraph
open scoped Sym2

namespace MathDB366258

universe u v
variable {V : Type u}

structure Decomposition (G : SimpleGraph V) (k : ℤ) (T : Type v) where
  tree : SimpleGraph T
  isTree : tree.IsTree
  bag : T → Finset V
  bound : ∀ t, ((bag t).card : ℤ) ≤ k + 1
  covers : ∀ x, ∃ t, x ∈ bag t
  edge : ∀ ⦃x y⦄, G.Adj x y → ∃ t, x ∈ bag t ∧ y ∈ bag t
  occurs : ∀ x, (tree.induce {t | x ∈ bag t}).Connected

def WidthLE (G : SimpleGraph V) (k : ℤ) : Prop :=
  ∃ T : Type v, Nonempty (Decomposition G k T)

def VertexConnected (G : SimpleGraph V) (k : ℤ) : Prop :=
  k < (Nat.card V : ℤ) ∧
    ∀ S : Finset V, (S.card : ℤ) < k → (G.induce {x | x ∉ S}).Connected

abbrev Vertex := Fin 4 ⊕ (Fin 4 × Fin 3)
abbrev core (u : Fin 4) : Vertex := .inl u
abbrev gadget (u : Fin 4) (j : Fin 3) : Vertex := .inr (u, j)

def inA (u a : Fin 4) : Prop := a = u + 2 ∨ a = u + 3
instance (u a : Fin 4) : Decidable (inA u a) := inferInstanceAs (Decidable (_ ∨ _))

def cross (a u : Fin 4) (j : Fin 3) : Prop :=
  if j = 0 then a = u else inA u a
instance (a u : Fin 4) (j : Fin 3) : Decidable (cross a u j) := by
  unfold cross
  infer_instance

def adjacent : Vertex → Vertex → Prop
  | .inl a, .inl b => a ≠ b
  | .inl a, .inr (u,j) => cross a u j
  | .inr (u,j), .inl a => cross a u j
  | .inr (u,i), .inr (w,j) => u = w ∧ ((i = 0 ∧ j ≠ 0) ∨ (j = 0 ∧ i ≠ 0))

instance : DecidableRel adjacent := fun x y => by
  rcases x with a | ⟨u,i⟩ <;> rcases y with b | ⟨w,j⟩ <;> unfold adjacent <;>
    infer_instance

def witness : SimpleGraph Vertex where
  Adj := adjacent
  symm := ⟨by
    intro x y h
    rcases x with a | ⟨u,i⟩ <;> rcases y with b | ⟨w,j⟩
    · exact Ne.symm h
    · exact h
    · exact h
    · exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by
    intro x h
    rcases x with a | ⟨u,i⟩
    · exact h rfl
    · exact h.2.elim (fun e => e.2 e.1) (fun e => e.2 e.1)⟩

instance : DecidableRel witness.Adj := inferInstanceAs (DecidableRel adjacent)

theorem witness_order : Fintype.card Vertex = 16 := by decide

theorem witness_edges : witness.edgeFinset.card = 34 := by decide

abbrev Node := Option (Fin 4 × Fin 3)

def parent : Fin 4 × Fin 3 → Node
  | (u,j) => if j = 0 then none else some (u,0)

def nodeAdj (x y : Node) : Prop :=
  (∃ z : Fin 4 × Fin 3, x = some z ∧ y = parent z) ∨
    (∃ z : Fin 4 × Fin 3, y = some z ∧ x = parent z)

instance : DecidableRel nodeAdj := fun x y => by
  unfold nodeAdj
  infer_instance

def bagTree : SimpleGraph Node where
  Adj := nodeAdj
  symm := ⟨fun {_ _} h => h.symm⟩
  loopless := ⟨by
    change ∀ n : Node, ¬ nodeAdj n n
    decide⟩

instance : DecidableRel bagTree.Adj := inferInstanceAs (DecidableRel nodeAdj)

def bags : Node → Finset Vertex
  | none => Finset.univ.image core
  | some (u,j) => {core (u+2), core (u+3), gadget u 0,
      if j = 0 then core u else gadget u j}

theorem bag_order : Fintype.card Node = 13 := by decide
theorem bag_edges : bagTree.edgeFinset.card = 12 := by decide
theorem bag_size : ∀ t, (bags t).card = 4 := by decide

#eval Lean.versionString

theorem short_reachable {W : Type*} {G : SimpleGraph W} {x y : W}
    (h : x = y ∨ G.Adj x y ∨ ∃ m, G.Adj x m ∧ G.Adj m y) :
    G.Reachable x y := by
  rcases h with rfl | h | ⟨m, h, h'⟩
  · exact .refl _
  · exact h.reachable
  · exact h.reachable.trans h'.reachable

theorem short_induce {W : Type*} {G : SimpleGraph W} {S : Set W} (x y : S)
    (h : x.val = y.val ∨ G.Adj x.val y.val ∨
      ∃ m ∈ S, G.Adj x.val m ∧ G.Adj m y.val) : (G.induce S).Reachable x y := by
  apply short_reachable
  rcases h with h | h | ⟨m, hm, h₁, h₂⟩
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨⟨m, hm⟩, h₁, h₂⟩)

theorem node_short : ∀ x : Node, x = none ∨ bagTree.Adj x none ∨
    ∃ m, bagTree.Adj x m ∧ bagTree.Adj m none := by decide

theorem tree_isTree : bagTree.IsTree := by
  rw [isTree_iff_connected_and_card]
  refine And.intro (show bagTree.Connected from { preconnected := ?_, nonempty := ⟨none⟩ }) ?_
  · intro x y
    exact (short_reachable (node_short x)).trans (short_reachable (node_short y)).symm
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card, bag_edges,
      bag_order]

def home : Vertex → Node
  | .inl _ => none
  | .inr z => some z

theorem home_mem : ∀ x, x ∈ bags (home x) := by decide
theorem bag_local : ∀ (x : Vertex) (t : Node), x ∈ bags t →
    t = home x ∨ bagTree.Adj t (home x) ∨
      ∃ m, x ∈ bags m ∧ bagTree.Adj t m ∧ bagTree.Adj m (home x) := by decide
theorem bag_cover_edge : ∀ (x y : Vertex), witness.Adj x y →
    ∃ n, x ∈ bags n ∧ y ∈ bags n := by decide

def concreteDecomposition : Decomposition witness 3 Node where
  tree := bagTree
  isTree := tree_isTree
  bag := bags
  bound t := by rw [bag_size]; decide
  covers x := ⟨home x, home_mem x⟩
  edge := fun {x y} => bag_cover_edge x y
  occurs x := by
    let r : {t : Node // x ∈ bags t} := ⟨home x, home_mem x⟩
    have go (t : {t : Node // x ∈ bags t}) :
        (bagTree.induce {t | x ∈ bags t}).Reachable t r :=
      short_induce t r (bag_local x t t.property)
    exact { preconnected := fun t s => (go t).trans (go s).symm, nonempty := ⟨r⟩ }

theorem witness_width : WidthLE.{0,0} witness 3 :=
  ⟨Node, ⟨concreteDecomposition⟩⟩

end MathDB366258


open SimpleGraph
open scoped Sym2

namespace MathDB366258
namespace RootedHelly

variable {T : Type*} {G : SimpleGraph T}

theorem support_induced {S : Set T} {a b : S} (p : (G.induce S).Walk a b) :
    ∀ z ∈ (p.map (Embedding.induce S).toHom).support, z ∈ S := by
  intro z hz
  rw [Walk.support_map] at hz
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
  exact w.property

theorem path_eq (h : G.IsTree) {a b : T} (p q : G.Path a b) : p = q :=
  (h.isAcyclic.subsingleton_path a b).elim p q

theorem path_inside (h : G.IsTree) {S : Set T} (hc : (G.induce S).Connected)
    {a b : T} (ha : a ∈ S) (hb : b ∈ S) (p : G.Path a b) :
    ∀ z ∈ p.val.support, z ∈ S := by
  classical
  obtain ⟨w⟩ := hc ⟨a, ha⟩ ⟨b, hb⟩
  let q : G.Walk a b := w.map (Embedding.induce S).toHom
  rw [path_eq h p q.toPath]
  exact fun z hz => support_induced w z (q.support_toPath_subset_support hz)

noncomputable def rootPath (h : G.IsTree) (r a : T) : G.Path r a := by
  classical
  exact (Classical.choice (h.connected r a)).toPath

noncomputable def depth (h : G.IsTree) (r a : T) : ℕ :=
  (rootPath h r a).val.length

theorem depth_prefix (h : G.IsTree) (r : T) {x a : T} (p : G.Path r x)
    [DecidableEq T] (ha : a ∈ p.val.support) :
    depth h r a = (p.val.takeUntil a ha).length := by
  unfold depth
  exact congrArg (fun w : G.Path r a => w.val.length)
    (path_eq h _ ⟨_, p.property.takeUntil ha⟩)

theorem nearest_on_path (h : G.IsTree) (r : T) {S : Set T}
    (hc : (G.induce S).Connected) {a x : T} (ha : a ∈ S) (hx : x ∈ S)
    (hm : ∀ b ∈ S, depth h r a ≤ depth h r b) :
    a ∈ (rootPath h r x).val.support := by
  classical
  by_contra hn
  have hra : r ≠ a := fun e => hn (e ▸ (rootPath h r x).val.start_mem_support)
  let p := (rootPath h r a).val
  have hnil : ¬ p.Nil := by
    intro he
    exact hra he.eq
  let b := p.penultimate
  have hadj : G.Adj b a := p.adj_penultimate hnil
  have hlast : s(b, a) ∈ p.edges := by
    have he : p.edges ≠ [] := by simpa using hnil
    rw [← Walk.getLast_edges_eq_mk_penultimate_end he]
    exact List.getLast_mem he
  obtain ⟨wi⟩ := hc ⟨x, hx⟩ ⟨a, ha⟩
  let w : G.Walk x a := wi.map (Embedding.induce S).toHom
  let q := (rootPath h r x).val
  have hpq : p = ((q.append w).toPath).val :=
    congrArg Subtype.val (path_eq h (rootPath h r a) (q.append w).toPath)
  have hedge : s(b, a) ∈ q.edges ++ w.edges := by
    rw [← Walk.edges_append]
    apply (q.append w).edges_bypass_sublist_edges.subset
    change s(b, a) ∈ ((q.append w).toPath).val.edges
    rw [← hpq]
    exact hlast
  have hb : b ∈ S := by
    rcases List.mem_append.mp hedge with hq | hw
    · exact (hn (q.snd_mem_support_of_mem_edges hq)).elim
    · exact support_induced wi b (w.fst_mem_support_of_mem_edges hw)
  have hbs : b ∈ p.support := p.fst_mem_support_of_mem_edges hlast
  have hprefix := depth_prefix h r (rootPath h r a) hbs
  have hle := p.length_takeUntil_le_length hbs
  have hlt : (p.takeUntil b hbs).length < p.length := by
    refine lt_of_le_of_ne hle ?_
    intro he
    have he' := Walk.getVert_length_takeUntil (p := p) hbs
    rw [he, Walk.getVert_length] at he'
    exact hadj.ne he'.symm
  have hh := hm b hb
  change depth h r b = (p.takeUntil b hbs).length at hprefix
  change p.length ≤ depth h r b at hh
  omega

theorem suffix_of_depth (h : G.IsTree) {r x a b : T} (p : G.Path r x)
    [DecidableEq T] (ha : a ∈ p.val.support) (hb : b ∈ p.val.support)
    (hle : depth h r a ≤ depth h r b) :
    b ∈ (p.val.dropUntil a ha).support := by
  by_contra hn
  have happ := p.val.take_spec ha
  have hmem : b ∈ (p.val.takeUntil a ha).support := by
    have hh : b ∈ ((p.val.takeUntil a ha).append (p.val.dropUntil a ha)).support :=
      happ.symm ▸ hb
    exact (((Walk.mem_support_append_iff _ _).mp hh).resolve_right hn)
  have hne : b ≠ a := fun e => hn (e ▸ (p.val.dropUntil a ha).start_mem_support)
  let pre := p.val.takeUntil a ha
  have h₁ := depth_prefix h r p ha
  have h₂ := depth_prefix h r (⟨pre, p.property.takeUntil ha⟩ : G.Path r a) hmem
  have hlt : (pre.takeUntil b hmem).length < pre.length := by
    refine lt_of_le_of_ne (pre.length_takeUntil_le_length hmem) ?_
    intro he
    have he' := Walk.getVert_length_takeUntil (p := pre) hmem
    rw [he, Walk.getVert_length] at he'
    exact hne he'.symm
  change depth h r a = pre.length at h₁
  change depth h r b = (pre.takeUntil b hmem).length at h₂
  omega

theorem helly {ι : Type*} [Fintype ι] [Nonempty ι] (h : G.IsTree)
    (S : ι → Set T) (hc : ∀ i, (G.induce (S i)).Connected)
    (hit : ∀ i j, ∃ x, x ∈ S i ∧ x ∈ S j) :
    ∃ x, ∀ i, x ∈ S i := by
  classical
  let r : T := Classical.choice h.connected.nonempty
  have nearest (i : ι) : ∃ a ∈ S i, ∀ b ∈ S i, depth h r a ≤ depth h r b := by
    have ex : ∃ n : ℕ, ∃ a ∈ S i, depth h r a = n := by
      obtain ⟨a, ha, _⟩ := hit i i
      exact ⟨_, a, ha, rfl⟩
    obtain ⟨a, ha, he⟩ := Nat.find_spec ex
    exact ⟨a, ha, fun b hb => he ▸ Nat.find_min' ex ⟨b, hb, rfl⟩⟩
  choose a ma low using nearest
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun i => depth h r (a i))
    Finset.univ_nonempty
  refine ⟨a j, fun i => ?_⟩
  obtain ⟨x, hxi, hxj⟩ := hit i j
  have hi := nearest_on_path h r (hc i) (ma i) hxi (low i)
  have hq := nearest_on_path h r (hc j) (ma j) hxj (low j)
  have hs := suffix_of_depth h (rootPath h r x) hi hq (hj i (Finset.mem_univ i))
  exact path_inside h (hc i) (ma i) hxi
    ⟨_, (rootPath h r x).property.dropUntil hi⟩ _ hs

end RootedHelly
end MathDB366258


open SimpleGraph

namespace MathDB366258

universe u v
variable {V : Type u} {G : SimpleGraph V} {k : ℤ} {T : Type v}

def Decomposition.meets (D : Decomposition G k T) (B : Set V) : Set T :=
  {t | ∃ x ∈ B, x ∈ D.bag t}

theorem Decomposition.one_vertex_reachable (D : Decomposition G k T) {B : Set V}
    {x : V} (hx : x ∈ B) {t s : D.meets B} (ht : x ∈ D.bag t.val)
    (hs : x ∈ D.bag s.val) : (D.tree.induce (D.meets B)).Reachable t s := by
  let f := (D.tree.induceHomOfLE (show {a | x ∈ D.bag a} ⊆ D.meets B from
    fun a h => ⟨x, hx, h⟩)).toHom
  exact (D.occurs x ⟨t, ht⟩ ⟨s, hs⟩).map f

theorem Decomposition.walk_meets (D : Decomposition G k T) {B : Set V}
    {x y : B} (p : (G.induce B).Walk x y) :
    ∀ (t s : D.meets B), x.val ∈ D.bag t.val → y.val ∈ D.bag s.val →
      (D.tree.induce (D.meets B)).Reachable t s := by
  induction p with
  | @nil a =>
    intro t s ht hs
    exact D.one_vertex_reachable a.property ht hs
  | @cons a b c e p ih =>
    intro t s ht hs
    obtain ⟨m, ham, hbm⟩ := D.edge (show G.Adj a.val b.val from e)
    let m' : D.meets B := ⟨m, a.val, a.property, ham⟩
    exact (D.one_vertex_reachable a.property ht (show a.val ∈ D.bag m'.val from ham)).trans
      (ih m' s hbm hs)

theorem Decomposition.meets_connected (D : Decomposition G k T) {B : Set V}
    (h : (G.induce B).Connected) : (D.tree.induce (D.meets B)).Connected := by
  refine { preconnected := ?_, nonempty := ?_ }
  · intro t s
    obtain ⟨x, hx, hxt⟩ := t.property
    obtain ⟨y, hy, hys⟩ := s.property
    obtain ⟨p⟩ := h ⟨x, hx⟩ ⟨y, hy⟩
    exact D.walk_meets p t s hxt hys
  · obtain ⟨x⟩ := h.nonempty
    obtain ⟨t, ht⟩ := D.covers x.val
    exact ⟨⟨t, x.val, x.property, ht⟩⟩

/-- The index tree can be infinite and is in an independent universe. -/
theorem Decomposition.branch_card_bound (D : Decomposition G k T)
    {ι : Type*} [Fintype ι] [Nonempty ι] (B : ι → Set V)
    (hconn : ∀ i, (G.induce (B i)).Connected)
    (hdisj : ∀ i j x, x ∈ B i → x ∈ B j → i = j)
    (htouch : ∀ i j, i ≠ j → ∃ x ∈ B i, ∃ y ∈ B j, G.Adj x y) :
    (Fintype.card ι : ℤ) ≤ k + 1 := by
  classical
  have hit (i j : ι) : ∃ t, t ∈ D.meets (B i) ∧ t ∈ D.meets (B j) := by
    by_cases hij : i = j
    · subst j
      obtain ⟨x⟩ := (hconn i).nonempty
      obtain ⟨t, ht⟩ := D.covers x.val
      exact ⟨t, ⟨x.val, x.property, ht⟩, ⟨x.val, x.property, ht⟩⟩
    · obtain ⟨x, hx, y, hy, hxy⟩ := htouch i j hij
      obtain ⟨t, hxt, hyt⟩ := D.edge hxy
      exact ⟨t, ⟨x, hx, hxt⟩, ⟨y, hy, hyt⟩⟩
  obtain ⟨t, ht⟩ := RootedHelly.helly D.isTree (fun i => D.meets (B i))
    (fun i => D.meets_connected (hconn i)) hit
  have representatives (i : ι) : ∃ x, x ∈ B i ∧ x ∈ D.bag t := ht i
  choose xs hb hbag using representatives
  let f : ι → {x // x ∈ D.bag t} := fun i => ⟨xs i, hbag i⟩
  have hf : Function.Injective f := by
    intro i j he
    have e : xs i = xs j := congrArg Subtype.val he
    exact hdisj i j (xs i) (hb i) (e.symm ▸ hb j)
  have hcard : Fintype.card ι ≤ (D.bag t).card := by
    simpa using Fintype.card_le_of_injective f hf
  exact (Int.ofNat_le.mpr hcard).trans (D.bound t)

/-- A singleton or one edge is enough for each of the four witness branches. -/
theorem four_pairs_obstruction (H : SimpleGraph V) (p : Fin 4 → Bool → V)
    (hc : ∀ i, p i false = p i true ∨ H.Adj (p i false) (p i true))
    (hd : ∀ i j b d, p i b = p j d → i = j)
    (ht : ∀ i j, i ≠ j → ∃ b d, H.Adj (p i b) (p j d)) :
    ¬ WidthLE.{u,v} H 2 := by
  intro ⟨T, ⟨D⟩⟩
  let B (i : Fin 4) : Set V := {x | ∃ b, x = p i b}
  have hconn (i : Fin 4) : (H.induce (B i)).Connected := by
    let r : B i := ⟨p i false, false, rfl⟩
    have go (x : B i) : (H.induce (B i)).Reachable r x := by
      obtain ⟨b, he⟩ := x.property
      apply short_induce
      cases b
      · exact Or.inl he.symm
      · rcases hc i with heq | heq
        · exact Or.inl (heq.trans he.symm)
        · exact Or.inr (Or.inl (he ▸ heq))
    exact { preconnected := fun x y => (go x).symm.trans (go y), nonempty := ⟨r⟩ }
  have hdisj (i j : Fin 4) (x : V) (hi : x ∈ B i) (hj : x ∈ B j) : i = j := by
    obtain ⟨b, hb⟩ := hi
    obtain ⟨d, hd'⟩ := hj
    exact hd i j b d (hb.symm.trans hd')
  have htouch (i j : Fin 4) (hn : i ≠ j) : ∃ x ∈ B i, ∃ y ∈ B j, H.Adj x y := by
    obtain ⟨b, d, hadj⟩ := ht i j hn
    exact ⟨p i b, ⟨b, rfl⟩, p j d, ⟨d, rfl⟩, hadj⟩
  have hh := D.branch_card_bound B hconn hdisj htouch
  simp at hh

end MathDB366258


open SimpleGraph

namespace MathDB366258

/-- Three distinct candidate vertices cannot all belong to a deletion of size less than three. -/
theorem survives_three {W : Type*} (S : Finset W) (hs : (S.card : ℤ) < 3)
    (f : Fin 3 → W) (hf : Function.Injective f) : ∃ i, f i ∉ S := by
  classical
  by_contra! hall
  have hsub : Finset.univ.image f ⊆ S := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hall i
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin] at hcard
  omega

def sideX (u : Fin 4) (i : Fin 3) : Vertex :=
  if i = 0 then gadget u 0 else if i = 1 then core (u+2) else core (u+3)

def sideY (u : Fin 4) (i : Fin 3) : Vertex :=
  if i = 0 then core u else gadget u i

def attachment (u : Fin 4) (i : Fin 3) : Fin 4 :=
  if i = 0 then u else if i = 1 then u+2 else u+3

def opposite (u : Fin 4) (j i : Fin 3) : Vertex :=
  if j = 0 then sideY u i else sideX u i

theorem opposite_inj : ∀ (u : Fin 4) (j i l : Fin 3),
    opposite u j i = opposite u j l → i = l := by decide

theorem attachment_inj : ∀ (u : Fin 4) (i l : Fin 3),
    core (attachment u i) = core (attachment u l) → i = l := by decide

theorem core_reaches : ∀ a b : Fin 4, core a = core b ∨ witness.Adj (core a) (core b) :=
  by decide

theorem gadget_reaches : ∀ (u : Fin 4) (j i l : Fin 3),
    witness.Adj (gadget u j) (core (attachment u l)) ∨
      (witness.Adj (gadget u j) (opposite u j i) ∧
       witness.Adj (opposite u j i) (core (attachment u l))) := by decide

theorem witness_connected : VertexConnected witness 3 := by
  refine ⟨?_, ?_⟩
  · rw [Nat.card_eq_fintype_card, witness_order]
    decide
  · intro S hs
    let W : Set Vertex := {x | x ∉ S}
    let H := witness.induce W
    obtain ⟨i, hi⟩ := survives_three S hs (fun j => core (attachment 0 j))
      (fun {_ _} => attachment_inj 0 _ _)
    let r : W := ⟨core (attachment 0 i), hi⟩
    have nearCore (x : W) : ∃ (a : Fin 4) (ha : core a ∈ W), H.Reachable x ⟨core a, ha⟩ := by
      rcases x with ⟨x, hx⟩
      rcases x with a | ⟨u,j⟩
      · exact ⟨a, hx, .refl _⟩
      · obtain ⟨l, hl⟩ := survives_three S hs (fun m => core (attachment u m))
          (fun {_ _} => attachment_inj u _ _)
        obtain ⟨m, hm⟩ := survives_three S hs (opposite u j)
          (fun {_ _} => opposite_inj u j _ _)
        refine ⟨attachment u l, hl, short_induce _ _ ?_⟩
        rcases gadget_reaches u j m l with edge | ⟨edge₁, edge₂⟩
        · exact Or.inr (Or.inl edge)
        · exact Or.inr (Or.inr ⟨_, hm, edge₁, edge₂⟩)
    have go (x : W) : H.Reachable x r := by
      obtain ⟨a, ha, hp⟩ := nearCore x
      apply hp.trans
      apply short_induce
      exact (core_reaches a (attachment 0 i)).imp_right Or.inl
    exact { preconnected := fun x y => (go x).trans (go y).symm, nonempty := ⟨r⟩ }

/-- Transfer the four connected branches to the induced complement's vertex type. -/
theorem induced_pairs {S : Set Vertex} (p : Fin 4 → Bool → Vertex)
    (hS : ∀ i b, p i b ∈ S)
    (hc : ∀ i, p i false = p i true ∨ witness.Adj (p i false) (p i true))
    (hd : ∀ i j b d, p i b = p j d → i = j)
    (ht : ∀ i j, i ≠ j → ∃ b d, witness.Adj (p i b) (p j d)) :
    ¬ WidthLE.{0,v} (witness.induce S) 2 := by
  apply four_pairs_obstruction (witness.induce S) (fun i b => ⟨p i b, hS i b⟩)
  · intro i
    exact (hc i).imp_left Subtype.ext
  · intro i j b d h
    exact hd i j b d (congrArg Subtype.val h)
  · exact ht

def corePairs (i : Fin 4) (_ : Bool) : Vertex := core i

theorem core_disjoint : ∀ (i j : Fin 4) (b d : Bool),
    corePairs i b = corePairs j d → i = j := by decide

theorem core_touch : ∀ (i j : Fin 4), i ≠ j →
    ∃ b d : Bool, witness.Adj (corePairs i b) (corePairs j d) := by decide

def gadgetPairs (u i : Fin 4) (b : Bool) : Vertex :=
  if i = 0 then core (u+2) else if i = 1 then core (u+3) else
    if i = 2 then gadget u 1 else gadget u (if b then 2 else 0)

theorem gadget_pair_connected : ∀ (u i : Fin 4), gadgetPairs u i false = gadgetPairs u i true ∨
    witness.Adj (gadgetPairs u i false) (gadgetPairs u i true) := by decide

theorem gadget_pair_disjoint : ∀ (u i j : Fin 4) (b d : Bool),
    gadgetPairs u i b = gadgetPairs u j d → i = j := by decide

theorem gadget_pair_touch : ∀ (u i j : Fin 4), i ≠ j →
    ∃ b d : Bool, witness.Adj (gadgetPairs u i b) (gadgetPairs u j d) := by decide

theorem gadget_pair_member : ∀ (u i : Fin 4) (b : Bool),
    gadgetPairs u i b = core (u+2) ∨ gadgetPairs u i b = core (u+3) ∨
    gadgetPairs u i b = gadget u 0 ∨ gadgetPairs u i b = gadget u 1 ∨
    gadgetPairs u i b = gadget u 2 := by decide

theorem center_adj : ∀ u : Fin 4,
    witness.Adj (core u) (core (u+2)) ∧ witness.Adj (core u) (core (u+3)) ∧
    witness.Adj (core u) (gadget u 0) := by decide

theorem center_neighbors : ∀ (u : Fin 4) (x : Vertex),
    witness.Adj (gadget u 0) x →
      x = core u ∨ x = gadget u 1 ∨ x = gadget u 2 := by decide

theorem center_avoids_A : ∀ u : Fin 4, gadget u 0 ≠ core (u+2) ∧
    ¬ witness.Adj (gadget u 0) (core (u+2)) := by decide

theorem missing_leaf_cut (I : Set Vertex) (u : Fin 4)
    (hu : core u ∈ I) (hc : gadget u 0 ∉ I) (ha : core (u+2) ∉ I)
    (hm : gadget u 1 ∈ I ∨ gadget u 2 ∈ I) :
    ¬ VertexConnected (witness.induce Iᶜ) 2 := by
  classical
  intro hconn
  let W : Set Vertex := Iᶜ
  let H := witness.induce W
  let c : W := ⟨gadget u 0, hc⟩
  let a : W := ⟨core (u+2), ha⟩
  let _ : Fintype W := Fintype.ofFinite _
  let cut : Finset W := Finset.univ.filter (H.Adj c)
  have memcut (x : W) : x ∈ cut ↔ H.Adj c x := by simp [cut]
  have htwo (x : W) (hx : x ∈ cut) : x.val = gadget u 1 ∨ x.val = gadget u 2 := by
    rcases center_neighbors u x.val ((memcut x).mp hx) with e | e
    · exact (x.property (e.symm ▸ hu)).elim
    · exact e
  have hcard : cut.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    apply Subtype.ext
    rcases hm with h₁ | h₂
    · have x₂ := (htwo x hx).resolve_left (fun e => x.property (e.symm ▸ h₁))
      have y₂ := (htwo y hy).resolve_left (fun e => y.property (e.symm ▸ h₁))
      exact x₂.trans y₂.symm
    · have x₁ := (htwo x hx).resolve_right (fun e => x.property (e.symm ▸ h₂))
      have y₁ := (htwo y hy).resolve_right (fun e => y.property (e.symm ▸ h₂))
      exact x₁.trans y₁.symm
  have hc' : c ∉ cut := fun hm => ((memcut c).mp hm).ne rfl
  have ha' : a ∉ cut := fun hm => (center_avoids_A u).2 ((memcut a).mp hm)
  obtain ⟨p⟩ := (hconn.2 cut (by omega)) ⟨c, hc'⟩ ⟨a, ha'⟩
  have hnil : ¬ p.Nil := by
    intro hn
    exact (center_avoids_A u).1 (congrArg (fun x => x.val.val) hn.eq)
  exact p.snd.property ((memcut p.snd.val).mpr (p.adj_snd hnil))

theorem witness_alternatives (I : Set Vertex) (hI : witness.IsIndepSet I) :
    ¬ WidthLE.{0,v} (witness.induce Iᶜ) 2 ∨
      ¬ VertexConnected (witness.induce Iᶜ) 2 := by
  classical
  by_cases has : ∃ u : Fin 4, core u ∈ I
  · obtain ⟨u, hu⟩ := has
    have survives (x : Vertex) (h : witness.Adj (core u) x) : x ∉ I :=
      fun hx => hI hu hx h.ne h
    have h₂ := survives _ (center_adj u).1
    have h₃ := survives _ (center_adj u).2.1
    have hc := survives _ (center_adj u).2.2
    by_cases missing : gadget u 1 ∈ I ∨ gadget u 2 ∈ I
    · exact Or.inr (missing_leaf_cut I u hu hc h₂ missing)
    · left
      apply induced_pairs (gadgetPairs u) ?_ (gadget_pair_connected u)
        (gadget_pair_disjoint u) (gadget_pair_touch u)
      intro i b
      rcases gadget_pair_member u i b with e | e | e | e | e
      · exact e.symm ▸ h₂
      · exact e.symm ▸ h₃
      · exact e.symm ▸ hc
      · exact e.symm ▸ (fun h => missing (Or.inl h))
      · exact e.symm ▸ (fun h => missing (Or.inr h))
  · exact Or.inl (induced_pairs corePairs (fun i _ h => has ⟨i, h⟩)
      (fun _ => Or.inl rfl) core_disjoint core_touch)

theorem witness_failure (I : Set Vertex) (hI : witness.IsIndepSet I) :
    ¬ (WidthLE.{0,v} (witness.induce Iᶜ) 2 ∧
      VertexConnected (witness.induce Iᶜ) 2) := by
  intro ⟨hw, hc⟩
  exact (witness_alternatives I hI).elim (fun bad => bad hw) (fun bad => bad hc)

/-- Conjecture 36, using the integer parameter of the MathDB row. -/
def NativeConjecture : Prop :=
  ∀ (V : Type) [Finite V] (G : SimpleGraph V) (k : ℤ),
    WidthLE.{0,0} G k → VertexConnected G k →
    ∃ I : Set V, G.IsIndepSet I ∧
      WidthLE.{0,0} (G.induce Iᶜ) (k - 1) ∧ VertexConnected (G.induce Iᶜ) (k - 1)

theorem native_refutation : ¬ NativeConjecture := by
  intro h
  obtain ⟨I, hi, hw, hc⟩ := h Vertex witness (3 : ℤ) witness_width witness_connected
  exact witness_failure I hi ⟨hw, hc⟩

#check Decomposition
#check WidthLE
#check VertexConnected
#check witness
#check witness_width
#check witness_connected
#check witness_alternatives
#check witness_failure
#check NativeConjecture
#check native_refutation
#print NativeConjecture
#print axioms witness_order
#print axioms witness_edges
#print axioms tree_isTree
#print axioms witness_width
#print axioms witness_connected
#print axioms RootedHelly.helly
#print axioms Decomposition.branch_card_bound
#print axioms witness_alternatives
#print axioms witness_failure
#print axioms native_refutation

end MathDB366258

namespace MathDB366258

/-- The two cyclic offsets are exactly the allowed core side of the gadget. -/
theorem inA_exact : ∀ u a : Fin 4, inA u a ↔ a ≠ u ∧ a ≠ u + 1 := by decide

/-- Both sides of each gadget span all of their cross edges. -/
theorem side_cross : ∀ (u : Fin 4) (i j : Fin 3),
    witness.Adj (sideX u i) (sideY u j) := by decide

theorem independent_core_unique (I : Set Vertex) (hI : witness.IsIndepSet I)
    (u a : Fin 4) (hu : core u ∈ I) (ha : core a ∈ I) : a = u := by
  by_contra hne
  have e : witness.Adj (core a) (core u) := hne
  exact hI ha hu e.ne e

end MathDB366258

namespace MathDB366258

#print axioms Decomposition
#print axioms WidthLE
#print axioms VertexConnected
#print axioms Vertex
#print axioms core
#print axioms gadget
#print axioms inA
#print axioms cross
#print axioms adjacent
#print axioms witness
#print axioms Node
#print axioms parent
#print axioms nodeAdj
#print axioms bagTree
#print axioms bags
#print axioms bag_order
#print axioms bag_edges
#print axioms bag_size
#print axioms short_reachable
#print axioms short_induce
#print axioms node_short
#print axioms home
#print axioms home_mem
#print axioms bag_local
#print axioms bag_cover_edge
#print axioms concreteDecomposition
#print axioms RootedHelly.support_induced
#print axioms RootedHelly.path_eq
#print axioms RootedHelly.path_inside
#print axioms RootedHelly.rootPath
#print axioms RootedHelly.depth
#print axioms RootedHelly.depth_prefix
#print axioms RootedHelly.nearest_on_path
#print axioms RootedHelly.suffix_of_depth
#print axioms Decomposition.meets
#print axioms Decomposition.one_vertex_reachable
#print axioms Decomposition.walk_meets
#print axioms Decomposition.meets_connected
#print axioms four_pairs_obstruction
#print axioms survives_three
#print axioms sideX
#print axioms sideY
#print axioms attachment
#print axioms opposite
#print axioms opposite_inj
#print axioms attachment_inj
#print axioms core_reaches
#print axioms gadget_reaches
#print axioms induced_pairs
#print axioms corePairs
#print axioms core_disjoint
#print axioms core_touch
#print axioms gadgetPairs
#print axioms gadget_pair_connected
#print axioms gadget_pair_disjoint
#print axioms gadget_pair_touch
#print axioms gadget_pair_member
#print axioms center_adj
#print axioms center_neighbors
#print axioms center_avoids_A
#print axioms missing_leaf_cut
#print axioms NativeConjecture
#print axioms inA_exact
#print axioms side_cross
#print axioms independent_core_unique

end MathDB366258
```
