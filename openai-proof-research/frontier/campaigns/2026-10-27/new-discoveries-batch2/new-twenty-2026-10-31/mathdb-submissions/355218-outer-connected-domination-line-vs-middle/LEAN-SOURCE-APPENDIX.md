# Lean source appendix

Modules are listed in import order.

## OuterCore.lean

```lean
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Order.Lattice.Nat

namespace OuterDom

open SimpleGraph

variable {V W : Type}

def lineGraph (G : SimpleGraph V) : SimpleGraph G.edgeSet where
  Adj e f := e ≠ f ∧ ∃ v, v ∈ e.val ∧ v ∈ f.val
  symm := by
    constructor
    rintro e f ⟨hne, v, he, hf⟩
    exact ⟨hne.symm, v, hf, he⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def middleGraph (G : SimpleGraph V) : SimpleGraph (V ⊕ G.edgeSet) where
  Adj
    | .inl _, .inl _ => False
    | .inl v, .inr e => v ∈ e.val
    | .inr e, .inl v => v ∈ e.val
    | .inr e, .inr f => (lineGraph G).Adj e f
  symm := by
    constructor
    intro u v h
    cases u <;> cases v
    · exact h
    · exact h
    · exact h
    · exact SimpleGraph.Adj.symm h
  loopless := ⟨by
    intro u h
    cases u with
    | inl v => exact h
    | inr e => exact (lineGraph G).irrefl h⟩

def Remainder (H : SimpleGraph W) (D : Finset W) :=
  H.induce {v | v ∉ D}

def IsOCDS (allowEmpty : Bool) (H : SimpleGraph W) (D : Finset W) : Prop :=
  (∀ v, v ∉ D → ∃ d ∈ D, H.Adj v d) ∧
  (Remainder H D).Preconnected ∧ (allowEmpty = false → ∃ v, v ∉ D)

theorem isOCDS_false_iff (H : SimpleGraph W) (D : Finset W) :
    IsOCDS false H D ↔
      (∀ v, v ∉ D → ∃ d ∈ D, H.Adj v d) ∧ (Remainder H D).Connected := by
  constructor
  · rintro ⟨hd, hc, hn⟩
    obtain ⟨v, hv⟩ := hn rfl
    exact ⟨hd, @SimpleGraph.Connected.mk _ _ hc ⟨⟨v, hv⟩⟩⟩
  · rintro ⟨hd, hc⟩
    obtain ⟨⟨v, hv⟩⟩ := hc.nonempty
    exact ⟨hd, hc.preconnected, fun _ => ⟨v, hv⟩⟩

/-- Cardinalities of admissible sets, with value zero by the natural infimum
    convention if there is no admissible set. -/
noncomputable def ocd (allowEmpty : Bool) (H : SimpleGraph W) : ℕ :=
  sInf {k | ∃ D : Finset W, IsOCDS allowEmpty H D ∧ D.card = k}

theorem ocd_le {a : Bool} {H : SimpleGraph W} {D : Finset W} (h : IsOCDS a H D) :
    ocd a H ≤ D.card :=
  csInf_le' (s := {k | ∃ S : Finset W, IsOCDS a H S ∧ S.card = k}) ⟨D, h, rfl⟩

theorem ocd_attained {a : Bool} {H : SimpleGraph W} (h : ∃ D, IsOCDS a H D) :
    ∃ D, IsOCDS a H D ∧ D.card = ocd a H := by
  obtain ⟨D, hD⟩ := h
  exact csInf_mem (s := {k | ∃ S : Finset W, IsOCDS a H S ∧ S.card = k})
    ⟨D.card, D, hD, rfl⟩

theorem exists_ocds_of_adj [Fintype W] {H : SimpleGraph W} {u v : W}
    (a : Bool) (h : H.Adj u v) : ∃ D, IsOCDS a H D := by
  classical
  let D : Finset W := Finset.univ.erase u
  have outside : ∀ w, w ∉ D ↔ w = u := by
    intro w
    simp [D]
  refine ⟨D, ?_, ?_, fun _ => ⟨u, (outside u).mpr rfl⟩⟩
  · intro w hw
    rw [(outside w).mp hw]
    exact ⟨v, by simp [D, h.ne.symm], h⟩
  · intro w z
    have he : w = z := Subtype.ext ((outside w.val).mp w.property |>.trans
      ((outside z.val).mp z.property).symm)
    subst z
    exact SimpleGraph.Reachable.rfl

theorem label_eq_of_reachable {H : SimpleGraph V} {u v : V}
    {A : Type} (f : V → A) (step : ∀ {x y}, H.Adj x y → f x = f y)
    (h : H.Reachable u v) : f u = f v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons h _ ih => exact (step h).trans ih

def edgeOf {G : SimpleGraph V} {u v : V} (h : G.Adj u v) : G.edgeSet := ⟨s(u,v), h⟩

theorem incident_reachable {G : SimpleGraph V} {u v : V}
    {e f : G.edgeSet} (he : u ∈ e.val) (hf : v ∈ f.val) (h : G.Reachable u v) :
    (lineGraph G).Reachable e f := by
  have share : ∀ (w : V) (e f : G.edgeSet), w ∈ e.val → w ∈ f.val →
      (lineGraph G).Reachable e f := by
    intro w e f he hf
    by_cases hne : e = f
    · subst f
      exact SimpleGraph.Reachable.rfl
    exact (show (lineGraph G).Adj e f from ⟨hne, w, he, hf⟩).reachable
  obtain ⟨p⟩ := h
  induction p generalizing e with
  | nil => exact share _ e f he hf
  | cons h _ ih =>
    exact (share _ e (edgeOf h) he (Sym2.mem_mk_left _ _)).trans
      (ih (Sym2.mem_mk_right _ _) hf)

theorem edge_has_endpoint {G : SimpleGraph V} (e : G.edgeSet) : ∃ u, u ∈ e.val :=
  Sym2.ind (fun u v => ⟨u, Sym2.mem_mk_left u v⟩) e.val

theorem line_preconnected {G : SimpleGraph V} (h : G.Preconnected) :
    (lineGraph G).Preconnected := by
  intro e f
  obtain ⟨u, hu⟩ := edge_has_endpoint e
  obtain ⟨v, hv⟩ := edge_has_endpoint f
  exact incident_reachable hu hv (h u v)

theorem incidence_map_iff {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) (v : V) (e : G.edgeSet) :
    φ v ∈ (φ.mapEdgeSet e).val ↔ v ∈ e.val := by
  change φ v ∈ Sym2.map φ e.val ↔ v ∈ e.val
  rw [Sym2.mem_map]
  constructor
  · rintro ⟨u, hu, huv⟩
    simpa only [φ.injective huv] using hu
  · intro hv
    exact ⟨v, hv, rfl⟩

def lineIso {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H) :
    lineGraph G ≃g lineGraph H where
  toEquiv := φ.mapEdgeSet
  map_rel_iff' := by
    intro e f
    change (φ.mapEdgeSet e ≠ φ.mapEdgeSet f ∧
      ∃ w, w ∈ (φ.mapEdgeSet e).val ∧ w ∈ (φ.mapEdgeSet f).val) ↔
      (e ≠ f ∧ ∃ v, v ∈ e.val ∧ v ∈ f.val)
    rw [φ.mapEdgeSet.injective.ne_iff]
    apply and_congr_right
    intro _
    constructor
    · rintro ⟨w, he, hf⟩
      obtain ⟨v, rfl⟩ := φ.surjective w
      exact ⟨v, (incidence_map_iff φ v e).mp he, (incidence_map_iff φ v f).mp hf⟩
    · rintro ⟨v, he, hf⟩
      exact ⟨φ v, (incidence_map_iff φ v e).mpr he, (incidence_map_iff φ v f).mpr hf⟩

def middleIso {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H) :
    middleGraph G ≃g middleGraph H where
  toEquiv := Equiv.sumCongr φ.toEquiv φ.mapEdgeSet
  map_rel_iff' := by
    intro u v
    cases u <;> cases v
    · rfl
    · exact incidence_map_iff φ _ _
    · exact incidence_map_iff φ _ _
    · exact (lineIso φ).map_adj_iff

theorem ocds_map {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) {a : Bool} {D : Finset V} (h : IsOCDS a G D) :
    IsOCDS a H (D.map φ.toEquiv.toEmbedding) := by
  have mem : ∀ v, φ v ∈ D.map φ.toEquiv.toEmbedding ↔ v ∈ D :=
    fun _ => Finset.mem_map' _
  have maps : Set.BijOn φ {v | v ∉ D} {w | w ∉ D.map φ.toEquiv.toEmbedding} := by
    refine ⟨fun v hv => fun hm => hv ((mem v).mp hm), φ.injective.injOn, ?_⟩
    intro w hw
    obtain ⟨v, rfl⟩ := φ.surjective w
    exact ⟨v, fun hm => hw ((mem v).mpr hm), rfl⟩
  refine ⟨?_, h.2.1.map (φ.induce maps).toHom (φ.induce maps).surjective, ?_⟩
  · intro w hw
    obtain ⟨v, rfl⟩ := φ.surjective w
    obtain ⟨d, hd, hadj⟩ := h.1 v (fun hm => hw ((mem v).mpr hm))
    exact ⟨φ d, (mem d).mpr hd, φ.map_adj_iff.mpr hadj⟩
  · intro ha
    obtain ⟨v, hv⟩ := h.2.2 ha
    exact ⟨φ v, fun hm => hv ((mem v).mp hm)⟩

theorem ocd_iso {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H) (a : Bool) :
    ocd a G = ocd a H := by
  by_cases hex : ∃ D, IsOCDS a G D
  · obtain ⟨D, hd, hc⟩ := ocd_attained hex
    obtain ⟨E, he, hec⟩ := ocd_attained ⟨_, ocds_map φ hd⟩
    apply le_antisymm
    · simpa [hec] using ocd_le (ocds_map φ.symm he)
    · simpa [hc] using ocd_le (ocds_map φ hd)
  · have hey : ¬ ∃ E, IsOCDS a H E := by
      rintro ⟨E, he⟩
      exact hex ⟨_, ocds_map φ.symm he⟩
    have empty (K : SimpleGraph W) (hk : ¬ ∃ E, IsOCDS a K E) :
        {k | ∃ E : Finset W, IsOCDS a K E ∧ E.card = k} = ∅ := by
      ext k
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨E, he, _⟩
      exact hk ⟨E, he⟩
    have hg : {k | ∃ D : Finset V, IsOCDS a G D ∧ D.card = k} = ∅ := by
      ext k
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨D, hd, _⟩
      exact hex ⟨D, hd⟩
    unfold ocd
    rw [empty H hey, hg]

end OuterDom
```

## CliquePath.lean

```lean
import OuterCore

namespace OuterDom
namespace CliquePath

open SimpleGraph

abbrev Vertex (h : ℕ) := (Bool × Fin (2*h)) ⊕ Bool

def clique {h : ℕ} (b : Bool) (i : Fin (2*h)) : Vertex h := .inl (b, i)
def joint {h : ℕ} (b : Bool) : Vertex h := .inr b

def graph (h : ℕ) : SimpleGraph (Vertex h) where
  Adj
    | .inl (b, i), .inl (c, j) => b = c ∧ i ≠ j
    | .inl (b, i), .inr c => b = c ∧ i.val = 0
    | .inr c, .inl (b, i) => b = c ∧ i.val = 0
    | .inr b, .inr c => b ≠ c
  symm := ⟨by
    intro u v huv
    cases u with
    | inl bi =>
      cases bi
      cases v with
      | inl cj =>
        cases cj
        exact ⟨huv.1.symm, huv.2.symm⟩
      | inr c => exact huv
    | inr b =>
      cases v with
      | inl cj =>
        cases cj
        exact huv
      | inr c => exact huv.symm⟩
  loopless := ⟨by
    intro u hu
    cases u with
    | inl bi =>
      cases bi
      exact hu.2 rfl
    | inr b => exact hu rfl⟩

abbrev Edge (h : ℕ) := (graph h).edgeSet

def root {h : ℕ} (hh : 2 ≤ h) (b : Bool) : Vertex h :=
  clique b ⟨0, by omega⟩

def bridge {h : ℕ} (hh : 2 ≤ h) : Option Bool → Edge h
  | none => edgeOf (show (graph h).Adj (joint false) (joint true) from by change false ≠ true; decide)
  | some b => edgeOf (show (graph h).Adj (root hh b) (joint b) from ⟨rfl, rfl⟩)

theorem bridge_none_eq {h : ℕ} (hh : 2 ≤ h) :
    (bridge hh none).val = s(joint false, joint true) := rfl

theorem bridge_some_eq {h : ℕ} (hh : 2 ≤ h) (b : Bool) :
    (bridge hh (some b)).val = s(root hh b, joint b) := rfl

def cliqueEmb {h : ℕ} (b : Bool) : Fin (2*h) ↪ Vertex h where
  toFun := clique b
  inj' := by intro i j hij; simpa [clique] using hij

abbrev CompleteEdge (h : ℕ) := (⊤ : SimpleGraph (Fin (2*h))).edgeSet

def cliqueEdge {h : ℕ} (b : Bool) : CompleteEdge h ↪ Edge h where
  toFun e := ⟨e.val.map (clique b), by
    obtain ⟨e, he⟩ := e
    induction e using Sym2.inductionOn with
    | _ i j =>
      exact ⟨rfl, he⟩⟩
  inj' := by
    intro e f hef
    apply Subtype.ext
    exact Sym2.map.injective (cliqueEmb b).injective (congrArg Subtype.val hef)

theorem cliqueEdge_endpoints {h : ℕ} {b : Bool} {e : CompleteEdge h} {v : Vertex h} :
    v ∈ (cliqueEdge b e).val ↔ ∃ i, i ∈ e.val ∧ clique b i = v :=
  Sym2.mem_map

theorem cliqueEdge_ne_bridge {h : ℕ} (hh : 2 ≤ h) (b : Bool)
    (e : CompleteEdge h) (k : Option Bool) : cliqueEdge b e ≠ bridge hh k := by
  intro he
  cases k with
  | none =>
    have hm : joint false ∈ (cliqueEdge b e).val := by
      rw [he, bridge_none_eq]
      exact Sym2.mem_mk_left _ _
    obtain ⟨i, _, hi⟩ := cliqueEdge_endpoints.mp hm
    cases hi
  | some c =>
    have hm : joint c ∈ (cliqueEdge b e).val := by
      rw [he, bridge_some_eq]
      exact Sym2.mem_mk_right _ _
    obtain ⟨i, _, hi⟩ := cliqueEdge_endpoints.mp hm
    cases hi

theorem incident_joint {h : ℕ} (hh : 2 ≤ h) (b : Bool) (e : Edge h)
    (he : joint b ∈ e.val) : e = bridge hh none ∨ e = bridge hh (some b) := by
  obtain ⟨v, hv⟩ := Sym2.mem_iff_exists.mp he
  have ha : (graph h).Adj (joint b) v := by
    change s(joint b, v) ∈ (graph h).edgeSet
    rw [← hv]
    exact e.property
  cases v with
  | inl ci =>
    obtain ⟨c, i⟩ := ci
    change c = b ∧ i.val = 0 at ha
    obtain ⟨rfl, hi⟩ := ha
    have hr : clique c i = root hh c := by
      exact congrArg (clique c) (Fin.ext hi)
    right
    apply Subtype.ext
    rw [hv, bridge_some_eq, ← hr]
    exact Sym2.eq_swap
  | inr c =>
    change b ≠ c at ha
    left
    apply Subtype.ext
    rw [hv, bridge_none_eq]
    cases b <;> cases c <;> first | contradiction | rfl | exact Sym2.eq_swap

def cutSide {h : ℕ} (k : Option Bool) : Vertex h → Bool
  | .inl (b, _) => b
  | .inr b => match k with
    | none => b
    | some c => !c

theorem crossing_edge {h : ℕ} (hh : 2 ≤ h) (k : Option Bool) {u v : Vertex h}
    (ha : (graph h).Adj u v) (hc : cutSide k u ≠ cutSide k v) :
    edgeOf ha = bridge hh k := by
  cases u with
  | inl p =>
    obtain ⟨b, i⟩ := p
    cases v with
    | inl q =>
      obtain ⟨c, j⟩ := q
      exact (hc ha.1).elim
    | inr c =>
      change b = c ∧ i.val = 0 at ha
      obtain ⟨rfl, hi⟩ := ha
      have hr : clique b i = root hh b := congrArg (clique b) (Fin.ext hi)
      cases k with
      | none => exact (hc rfl).elim
      | some d =>
        have hbd : b = d := by cases b <;> cases d <;> simp_all [cutSide]
        subst d
        apply Subtype.ext
        change s(clique b i, joint b) = _
        rw [bridge_some_eq, hr]
  | inr b =>
    cases v with
    | inl q =>
      obtain ⟨c, j⟩ := q
      change c = b ∧ j.val = 0 at ha
      obtain ⟨rfl, hj⟩ := ha
      have hr : clique c j = root hh c := congrArg (clique c) (Fin.ext hj)
      cases k with
      | none => exact (hc rfl).elim
      | some d =>
        have hcd : c = d := by cases c <;> cases d <;> simp_all [cutSide]
        subst d
        apply Subtype.ext
        change s(joint c, clique c j) = _
        rw [bridge_some_eq, hr, Sym2.eq_swap]
    | inr c =>
      cases k with
      | some d => exact (hc rfl).elim
      | none =>
        change b ≠ c at ha
        apply Subtype.ext
        rw [bridge_none_eq]
        cases b <;> cases c <;> first | contradiction | rfl | exact Sym2.eq_swap

theorem edge_side_eq {h : ℕ} (hh : 2 ≤ h) (k : Option Bool) (e : Edge h)
    (he : e ≠ bridge hh k) {u v : Vertex h} (hu : u ∈ e.val) (hv : v ∈ e.val) :
    cutSide k u = cutSide k v := by
  by_contra hne
  have heq : e.val = s(u,v) :=
    (Sym2.mem_and_mem_iff (fun huv => hne (congrArg (cutSide k) huv))).mp ⟨hu, hv⟩
  have ha : (graph h).Adj u v := by
    change s(u,v) ∈ (graph h).edgeSet
    rw [← heq]
    exact e.property
  exact he ((Subtype.ext heq).trans (crossing_edge hh k ha hne))

end CliquePath
end OuterDom
```

## LineLower.lean

```lean
import CliquePath

namespace OuterDom.CliquePath

open SimpleGraph

theorem center_adj_left {h : ℕ} (hh : 2 ≤ h) :
    (lineGraph (graph h)).Adj (bridge hh none) (bridge hh (some false)) := by
  refine ⟨?_, joint false, Sym2.mem_mk_left _ _, Sym2.mem_mk_right _ _⟩
  intro he
  have hm : joint true ∈ (bridge hh (some false)).val := by
    rw [← he, bridge_none_eq]
    exact Sym2.mem_mk_right _ _
  simp [bridge_some_eq, Sym2.mem_iff, root, clique, joint] at hm

theorem has_selected_bridge {h : ℕ} {a : Bool} (hh : 2 ≤ h) {D : Finset (Edge h)}
    (hd : IsOCDS a (lineGraph (graph h)) D) : ∃ k, bridge hh k ∈ D := by
  by_cases hc : bridge hh none ∈ D
  · exact ⟨none, hc⟩
  obtain ⟨d, hm, _, v, hv, hvd⟩ := hd.1 _ hc
  rw [bridge_none_eq, Sym2.mem_iff] at hv
  rcases hv with rfl | rfl <;>
    rcases incident_joint hh _ d hvd with he | he <;>
    exact ⟨_, he ▸ hm⟩

theorem separated_by_bridge {h : ℕ} (hh : 2 ≤ h) (k : Option Bool)
    {D : Finset (Edge h)} (hk : bridge hh k ∈ D)
    {e f : CompleteEdge h} (he : cliqueEdge false e ∉ D) (hf : cliqueEdge true f ∉ D) :
    ¬ (Remainder (lineGraph (graph h)) D).Reachable
      ⟨cliqueEdge false e, he⟩ ⟨cliqueEdge true f, hf⟩ := by
  classical
  let chosen (d : Edge h) := Classical.choose (edge_has_endpoint d)
  have endpoint (d : Edge h) : chosen d ∈ d.val := Classical.choose_spec (edge_has_endpoint d)
  let label (d : {v : Edge h // v ∉ D}) := cutSide k (chosen d.val)
  have compare : ∀ (d : {v : Edge h // v ∉ D}) {v : Vertex h},
      v ∈ d.val.val → label d = cutSide k v := by
    intro d v hv
    exact edge_side_eq hh k d.val (fun heq => d.property (heq ▸ hk)) (endpoint d.val) hv
  have step : ∀ {d d' : {v : Edge h // v ∉ D}},
      (Remainder (lineGraph (graph h)) D).Adj d d' → label d = label d' := by
    rintro d d' ⟨_, v, hv, hv'⟩
    exact (compare d hv).trans (compare d' hv').symm
  have left : label ⟨cliqueEdge false e, he⟩ = false := by
    obtain ⟨i, hi⟩ := edge_has_endpoint e
    exact compare ⟨cliqueEdge false e, he⟩ (cliqueEdge_endpoints.mpr ⟨i, hi, rfl⟩)
  have right : label ⟨cliqueEdge true f, hf⟩ = true := by
    obtain ⟨i, hi⟩ := edge_has_endpoint f
    exact compare ⟨cliqueEdge true f, hf⟩ (cliqueEdge_endpoints.mpr ⟨i, hi, rfl⟩)
  intro hr
  have heq := label_eq_of_reachable label step hr
  rw [left, right] at heq
  cases heq

theorem entire_clique_selected {h : ℕ} {a : Bool} (hh : 2 ≤ h)
    {D : Finset (Edge h)} (hd : IsOCDS a (lineGraph (graph h)) D)
    {k : Option Bool} (hk : bridge hh k ∈ D) :
    ∃ b : Bool, ∀ e : CompleteEdge h, cliqueEdge b e ∈ D := by
  by_cases hleft : ∀ e : CompleteEdge h, cliqueEdge false e ∈ D
  · exact ⟨false, hleft⟩
  push Not at hleft
  obtain ⟨e, he⟩ := hleft
  refine ⟨true, fun f => ?_⟩
  by_contra hf
  exact separated_by_bridge hh k hk he hf (hd.2.1 ⟨_, he⟩ ⟨_, hf⟩)

theorem line_card_lower {h : ℕ} {a : Bool} (hh : 2 ≤ h)
    {D : Finset (Edge h)} (hd : IsOCDS a (lineGraph (graph h)) D) :
    (2*h).choose 2 + 1 ≤ D.card := by
  classical
  obtain ⟨k, hk⟩ := has_selected_bridge hh hd
  obtain ⟨b, hb⟩ := entire_clique_selected hh hd hk
  let E := (Finset.univ : Finset (CompleteEdge h)).map (cliqueEdge b)
  have hmem : bridge hh k ∉ E := by
    intro hm
    obtain ⟨e, _, he⟩ := Finset.mem_map.mp hm
    exact cliqueEdge_ne_bridge hh b e k he
  have hsub : insert (bridge hh k) E ⊆ D := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact hk
    obtain ⟨f, _, rfl⟩ := Finset.mem_map.mp he
    exact hb f
  have hcard : E.card = (2*h).choose 2 := by
    simp only [E, Finset.card_map, Finset.card_univ, SimpleGraph.card_edgeSet,
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
  simpa only [Finset.card_insert_of_notMem hmem, hcard] using Finset.card_le_card hsub

theorem line_lower {h : ℕ} (hh : 2 ≤ h) (a : Bool) :
    (2*h).choose 2 + 1 ≤ ocd a (lineGraph (graph h)) := by
  classical
  obtain ⟨D, hD, hcard⟩ := ocd_attained (exists_ocds_of_adj a (center_adj_left hh))
  exact hcard ▸ line_card_lower hh hD

theorem middle_bound_lt_line_bound {h : ℕ} (hh : 2 ≤ h) :
    2*h+2 < (2*h).choose 2 + 1 := by
  rw [Nat.choose_two_right]
  have hm := Nat.mul_le_mul_left (2*h) (show 3 ≤ 2*h-1 by omega)
  omega

end OuterDom.CliquePath
```

## MiddleUpper.lean

```lean
import CliquePath

namespace OuterDom.CliquePath

open SimpleGraph

def firstIndex {h : ℕ} (j : Fin h) : Fin (2*h) := ⟨2*j.val, by omega⟩
def secondIndex {h : ℕ} (j : Fin h) : Fin (2*h) := ⟨2*j.val+1, by omega⟩

def matchingEdge {h : ℕ} (b : Bool) (j : Fin h) : Edge h :=
  edgeOf (show (graph h).Adj (clique b (firstIndex j)) (clique b (secondIndex j)) from
    ⟨rfl, fun he => by have := congrArg Fin.val he; simp [firstIndex, secondIndex] at this⟩)

abbrev MidVertex (h : ℕ) := Vertex h ⊕ Edge h

def selectedVertex {h : ℕ} : ((Bool × Fin h) ⊕ Bool) → MidVertex h
  | .inl (b, j) => .inr (matchingEdge b j)
  | .inr b => .inl (joint b)

noncomputable def matchingSet (h : ℕ) : Finset (MidVertex h) := by
  classical
  exact Finset.univ.image selectedVertex

theorem selected_joint {h : ℕ} (b : Bool) : Sum.inl (joint b) ∈ matchingSet h := by
  classical
  exact Finset.mem_image.mpr ⟨Sum.inr b, Finset.mem_univ _, rfl⟩

theorem selected_matching {h : ℕ} (b : Bool) (j : Fin h) :
    Sum.inr (matchingEdge b j) ∈ matchingSet h := by
  classical
  exact Finset.mem_image.mpr ⟨Sum.inl (b, j), Finset.mem_univ _, rfl⟩

theorem selected_edge_kind {h : ℕ} {e : Edge h}
    (he : Sum.inr e ∈ matchingSet h) : ∃ b j, e = matchingEdge b j := by
  classical
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp he
  cases x with
  | inl p =>
    obtain ⟨b, j⟩ := p
    exact ⟨b, j, (Sum.inr.inj hx).symm⟩
  | inr b => cases hx

theorem matching_endpoints {h : ℕ} {b : Bool} {j : Fin h} {v : Vertex h} :
    v ∈ (matchingEdge b j).val ↔ v = clique b (firstIndex j) ∨ v = clique b (secondIndex j) :=
  Sym2.mem_iff

theorem matching_covers {h : ℕ} (b : Bool) (i : Fin (2*h)) :
    ∃ j, clique b i ∈ (matchingEdge b j).val := by
  let j : Fin h := ⟨i.val / 2, by omega⟩
  refine ⟨j, matching_endpoints.mpr ?_⟩
  have he : i.val = 2*j.val ∨ i.val = 2*j.val+1 := by
    dsimp [j]
    omega
  rcases he with he | he
  · exact Or.inl (congrArg (clique b) (Fin.ext he))
  · exact Or.inr (congrArg (clique b) (Fin.ext he))

theorem matchingSet_dominates {h : ℕ} (v : MidVertex h) (hv : v ∉ matchingSet h) :
    ∃ d ∈ matchingSet h, (middleGraph (graph h)).Adj v d := by
  cases v with
  | inl v =>
    cases v with
    | inl p =>
      obtain ⟨b, i⟩ := p
      obtain ⟨j, hj⟩ := matching_covers b i
      exact ⟨Sum.inr (matchingEdge b j), selected_matching b j, hj⟩
    | inr b => exact (hv (selected_joint b)).elim
  | inr e =>
    obtain ⟨v, hv'⟩ := edge_has_endpoint e
    cases v with
    | inl p =>
      obtain ⟨b, i⟩ := p
      obtain ⟨j, hj⟩ := matching_covers b i
      refine ⟨Sum.inr (matchingEdge b j), selected_matching b j, ?_⟩
      exact ⟨fun he => hv (he ▸ selected_matching b j), clique b i, hv', hj⟩
    | inr b => exact ⟨Sum.inl (joint b), selected_joint b, hv'⟩

def removedMatching (h : ℕ) : Set (Sym2 (Vertex h)) :=
  {e | ∃ d : Edge h, Sum.inr d ∈ matchingSet h ∧ d.val = e}

def residual (h : ℕ) : SimpleGraph (Vertex h) :=
  (graph h).deleteEdges (removedMatching h)

theorem residual_of_adj {h : ℕ} {u v : Vertex h} (hG : (graph h).Adj u v)
    (hn : Sum.inr (edgeOf hG) ∉ matchingSet h) : (residual h).Adj u v := by
  rw [residual, SimpleGraph.deleteEdges_adj]
  refine ⟨hG, ?_⟩
  rintro ⟨e, he, heq⟩
  exact hn ((show e = edgeOf hG from Subtype.ext heq) ▸ he)

theorem bridge_not_selected {h : ℕ} (hh : 2 ≤ h) (k : Option Bool) :
    Sum.inr (bridge hh k) ∉ matchingSet h := by
  intro he
  obtain ⟨b, j, hj⟩ := selected_edge_kind he
  cases k with
  | none =>
    have hm : joint false ∈ (matchingEdge b j).val := by
      rw [← hj, bridge_none_eq]
      exact Sym2.mem_mk_left _ _
    rcases matching_endpoints.mp hm with h | h <;> cases h
  | some c =>
    have hm : joint c ∈ (matchingEdge b j).val := by
      rw [← hj, bridge_some_eq]
      exact Sym2.mem_mk_right _ _
    rcases matching_endpoints.mp hm with h | h <;> cases h

theorem residual_side_bridge {h : ℕ} (hh : 2 ≤ h) (b : Bool) :
    (residual h).Adj (root hh b) (joint b) :=
  residual_of_adj ⟨rfl, rfl⟩ (bridge_not_selected hh (some b))

theorem residual_center {h : ℕ} (hh : 2 ≤ h) :
    (residual h).Adj (joint false) (joint true) :=
  residual_of_adj (by change false ≠ true; decide) (bridge_not_selected hh none)

theorem matching_index {h : ℕ} {b c : Bool} {i : Fin (2*h)} {j : Fin h}
    (hm : clique b i ∈ (matchingEdge c j).val) : i.val / 2 = j.val := by
  rcases matching_endpoints.mp hm with he | he
  · have hi : i.val = 2*j.val := congrArg (fun p => p.2.val) (Sum.inl.inj he)
    omega
  · have hi : i.val = 2*j.val+1 := congrArg (fun p => p.2.val) (Sum.inl.inj he)
    omega

theorem residual_clique_adj {h : ℕ} (b : Bool) {i j : Fin (2*h)}
    (hne : i.val / 2 ≠ j.val / 2) : (residual h).Adj (clique b i) (clique b j) := by
  have ha : (graph h).Adj (clique b i) (clique b j) := ⟨rfl, fun he => hne (he ▸ rfl)⟩
  apply residual_of_adj ha
  intro hm
  obtain ⟨c, k, he⟩ := selected_edge_kind hm
  have hi : clique b i ∈ (matchingEdge c k).val := he ▸ Sym2.mem_mk_left _ _
  have hj : clique b j ∈ (matchingEdge c k).val := he ▸ Sym2.mem_mk_right _ _
  exact hne ((matching_index hi).trans (matching_index hj).symm)

theorem residual_clique_reaches_root {h : ℕ} (hh : 2 ≤ h) (b : Bool) (i : Fin (2*h)) :
    (residual h).Reachable (clique b i) (root hh b) := by
  let z : Fin (2*h) := ⟨0, by omega⟩
  let j : Fin (2*h) := ⟨2, by omega⟩
  change (residual h).Reachable (clique b i) (clique b z)
  by_cases hi : i.val / 2 = 0
  · exact (residual_clique_adj b (i := i) (j := j) (by simp [j, hi])).reachable.trans
      (residual_clique_adj b (i := j) (j := z) (by simp [j, z])).reachable
  · exact (residual_clique_adj b (j := z) (by simpa [z] using hi)).reachable

theorem residual_connected {h : ℕ} (hh : 2 ≤ h) : (residual h).Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable (G := residual h)).mpr
  refine ⟨joint false, ?_⟩
  have joints (b : Bool) : (residual h).Reachable (joint false) (joint b) := by
    cases b
    · exact SimpleGraph.Reachable.rfl
    · exact (residual_center hh).reachable
  rintro (⟨b, i⟩ | b)
  · exact (joints b).trans ((residual_side_bridge hh b).symm.reachable.trans
      (residual_clique_reaches_root hh b i).symm)
  · exact joints b

theorem graph_connected {h : ℕ} (hh : 2 ≤ h) : (graph h).Connected :=
  (residual_connected hh).mono (SimpleGraph.deleteEdges_le _)

def residualEdge {h : ℕ} (e : (residual h).edgeSet) : Edge h :=
  ⟨e.val, (show (residual h).edgeSet ⊆ (graph h).edgeSet from
    SimpleGraph.edgeSet_mono (SimpleGraph.deleteEdges_le _)) e.property⟩

theorem residualEdge_injective {h : ℕ} : Function.Injective (residualEdge (h := h)) :=
  fun _ _ he => Subtype.ext (congrArg (fun d : Edge h => d.val) he)

theorem residualEdge_not_selected {h : ℕ} (e : (residual h).edgeSet) :
    Sum.inr (residualEdge e) ∉ matchingSet h := by
  intro he
  have hn : e.val ∈ (residual h).edgeSet := e.property
  have hs := (Set.ext_iff.mp (SimpleGraph.edgeSet_deleteEdges (G := graph h) (removedMatching h)) e.val).mp hn
  exact hs.2 ⟨residualEdge e, he, rfl⟩

def toMiddleRemainder {h : ℕ} :
    lineGraph (residual h) →g Remainder (middleGraph (graph h)) (matchingSet h) where
  toFun e := ⟨Sum.inr (residualEdge e), residualEdge_not_selected e⟩
  map_rel' := by
    rintro e f ⟨hne, v, he, hf⟩
    exact ⟨fun h => hne (residualEdge_injective h), v, he, hf⟩

theorem reaches_residual_edge {h : ℕ} (hh : 2 ≤ h)
    (v : {v : MidVertex h // v ∉ matchingSet h}) :
    ∃ e : (residual h).edgeSet,
      (Remainder (middleGraph (graph h)) (matchingSet h)).Reachable v (toMiddleRemainder e) := by
  obtain ⟨v, hv⟩ := v
  cases v with
  | inr d =>
    have hs : d.val ∈ (residual h).edgeSet := by
      rw [residual, SimpleGraph.edgeSet_deleteEdges]
      refine ⟨d.property, ?_⟩
      rintro ⟨e, he, heq⟩
      exact hv ((show e = d from Subtype.ext heq) ▸ he)
    let e : (residual h).edgeSet := ⟨d.val, hs⟩
    refine ⟨e, ?_⟩
    have he : (⟨Sum.inr d, hv⟩ : {v : MidVertex h // v ∉ matchingSet h}) =
        toMiddleRemainder e := Subtype.ext (congrArg Sum.inr (Subtype.ext rfl))
    rw [he]
  | inl v =>
    cases v with
    | inr b => exact (hv (selected_joint b)).elim
    | inl p =>
      obtain ⟨b, i⟩ := p
      let z : Fin (2*h) := ⟨0, by omega⟩
      let j : Fin (2*h) := ⟨2, by omega⟩
      have hsome : ∃ k, (residual h).Adj (clique b i) (clique b k) := by
        by_cases hi : i.val / 2 = 0
        · exact ⟨j, residual_clique_adj b (by simp [j, hi])⟩
        · exact ⟨z, residual_clique_adj b (by simpa [z] using hi)⟩
      obtain ⟨k, hk⟩ := hsome
      exact ⟨edgeOf hk, SimpleGraph.Adj.reachable (G := Remainder (middleGraph (graph h))
        (matchingSet h)) (show clique b i ∈ (edgeOf hk).val from Sym2.mem_mk_left _ _)⟩

theorem middle_upper {h : ℕ} (hh : 2 ≤ h) (a : Bool) :
    ocd a (middleGraph (graph h)) ≤ 2*h+2 := by
  classical
  have hc : (Remainder (middleGraph (graph h)) (matchingSet h)).Preconnected := by
    intro u v
    obtain ⟨e, he⟩ := reaches_residual_edge hh u
    obtain ⟨f, hf⟩ := reaches_residual_edge hh v
    exact he.trans (((line_preconnected (residual_connected hh).preconnected e f).map
      toMiddleRemainder).trans hf.symm)
  have hd : IsOCDS a (middleGraph (graph h)) (matchingSet h) :=
    ⟨matchingSet_dominates, hc, fun _ => ⟨Sum.inr (bridge hh none), bridge_not_selected hh none⟩⟩
  refine (ocd_le hd).trans ?_
  calc
    (matchingSet h).card ≤ (Finset.univ : Finset ((Bool × Fin h) ⊕ Bool)).card :=
      Finset.card_image_le
    _ = 2*h+2 := by simp

end OuterDom.CliquePath
```

## LineMiddleConjecture.lean

```lean
import LineLower
import MiddleUpper

namespace OuterDom

open SimpleGraph

namespace CliquePath

theorem clique_path_bounds {h : ℕ} (hh : 2 ≤ h) (a : Bool) :
    ocd a (middleGraph (graph h)) ≤ 2*h+2 ∧
    2*h+2 < (2*h).choose 2+1 ∧
    (2*h).choose 2+1 ≤ ocd a (lineGraph (graph h)) :=
  ⟨middle_upper hh a, middle_bound_lt_line_bound hh, line_lower hh a⟩

noncomputable def labels (h : ℕ) : Vertex h ≃ Fin (4*h+2) :=
  Fintype.equivFinOfCardEq (by simp; omega)

noncomputable def labeledGraph (h : ℕ) : SimpleGraph (Fin (4*h+2)) :=
  (graph h).comap (labels h).symm

noncomputable def labelingIso (h : ℕ) : graph h ≃g labeledGraph h :=
  (SimpleGraph.Iso.comap (labels h).symm (graph h)).symm

theorem labeled_clique_path_bounds {h : ℕ} (hh : 2 ≤ h) :
    (labeledGraph h).Connected ∧ ∀ a : Bool,
      ocd a (middleGraph (labeledGraph h)) ≤ 2*h+2 ∧
      2*h+2 < (2*h).choose 2+1 ∧
      (2*h).choose 2+1 ≤ ocd a (lineGraph (labeledGraph h)) := by
  constructor
  · exact (graph_connected hh).map (labelingIso h).toHom (labelingIso h).surjective
  · intro a
    rw [← ocd_iso (middleIso (labelingIso h)) a, ← ocd_iso (lineIso (labelingIso h)) a]
    exact clique_path_bounds hh a

theorem clique_path_strict {h : ℕ} (hh : 2 ≤ h) (a : Bool) :
    ocd a (middleGraph (labeledGraph h)) < ocd a (lineGraph (labeledGraph h)) := by
  obtain ⟨hm, ht, hl⟩ := (labeled_clique_path_bounds hh).2 a
  exact (lt_of_le_of_lt hm ht).trans_le hl

theorem infinitely_many_counterexample_orders (a : Bool) :
    Set.Infinite {n : ℕ | ∃ G : SimpleGraph (Fin n), 2 ≤ n ∧ G.Connected ∧
      ocd a (middleGraph G) < ocd a (lineGraph G)} := by
  let f (j : ℕ) := 4*(j+2)+2
  have hi : Function.Injective f := by
    intro i j he
    dsimp [f] at he
    omega
  apply (Set.infinite_range_of_injective hi).mono
  rintro _ ⟨j, rfl⟩
  have hh : 2 ≤ j+2 := by omega
  exact ⟨labeledGraph (j+2), by dsimp [f]; omega,
    (labeled_clique_path_bounds hh).1, clique_path_strict hh a⟩

end CliquePath

def Conjecture76 (a : Bool) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), 2 ≤ n →
    ocd a (lineGraph G) ≤ ocd a (middleGraph G)

theorem not_conjecture76 (a : Bool) : ¬ Conjecture76 a := by
  intro hc
  exact (not_le_of_gt (CliquePath.clique_path_strict (h := 2) (by decide) a))
    (hc 10 (CliquePath.labeledGraph 2) (by decide))

theorem mathdb_355218 :
    ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n)), 2 ≤ n →
      ocd true (lineGraph G) ≤ ocd true (middleGraph G) :=
  not_conjecture76 true

theorem mathdb_355218_nonempty :
    ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n)), 2 ≤ n →
      ocd false (lineGraph G) ≤ ocd false (middleGraph G) :=
  not_conjecture76 false

end OuterDom

#check OuterDom.Conjecture76
#check OuterDom.not_conjecture76
#check OuterDom.mathdb_355218
#check OuterDom.mathdb_355218_nonempty
#check OuterDom.CliquePath.clique_path_bounds
#check OuterDom.CliquePath.labeled_clique_path_bounds
#check OuterDom.CliquePath.clique_path_strict
#check OuterDom.CliquePath.infinitely_many_counterexample_orders
#print axioms OuterDom.not_conjecture76
#print axioms OuterDom.mathdb_355218
#print axioms OuterDom.mathdb_355218_nonempty
#print axioms OuterDom.CliquePath.clique_path_bounds
#print axioms OuterDom.CliquePath.labeled_clique_path_bounds
#print axioms OuterDom.CliquePath.clique_path_strict
#print axioms OuterDom.CliquePath.infinitely_many_counterexample_orders
```

